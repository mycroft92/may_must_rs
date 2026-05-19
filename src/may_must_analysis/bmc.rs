//! Bounded model checking (BMC) via loop unrolling.
//!
//! Unrolls each loop in the CFG up to a configurable `bound`, producing an
//! acyclic CFG that the existing backward analysis can reason about directly.
//! BMC is sound for **bug finding only**: a `BugFound` result is a real
//! counterexample.  The absence of a bug within the bound is not a proof of
//! safety — callers should treat a `None` return as UNKNOWN.
//!
//! # Unrolling strategy
//!
//! For a loop with body nodes `{H, B…, L}` and back edge `L→H`:
//! - Iteration 0 reuses the original nodes.
//! - Iterations 1..bound−1 are fresh node copies added to the cloned CFG.
//! - `L_i → H_{i+1}` replaces the back edge at each step; the original back
//!   edge is removed so the CFG becomes acyclic.
//! - Exit edges are replicated from every copy so the loop can exit at any
//!   iteration.
//!
//! Nested loops are not supported; `bmc_check` returns `None` for those cases.
//! Independent (non-nested) loops in the same function are each unrolled with
//! the same bound.

use crate::common::abstract_cfg::{AbstractCfg, CfgNodeId};
use crate::common::adapter::AssertionSite;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::{self, AssertionResult};
use crate::may_must_analysis::loops::{detect_loops, sort_innermost_first, LoopInfo};
use crate::may_must_analysis::rules::Judgement;
use std::collections::BTreeMap;

/// Try to find a bug in `site` within `bound` loop iterations.
///
/// Builds a k-times-unrolled version of `cfg` and runs the backward analysis
/// on the acyclic result.  Returns `Some(result)` with a `BugFound` judgement
/// if a counterexample is found within the bound; `None` otherwise.
pub fn bmc_check(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    bound: usize,
) -> Option<AssertionResult> {
    if bound == 0 {
        return None;
    }

    let mut loops = detect_loops(cfg);
    if loops.is_empty() {
        return None;
    }
    sort_innermost_first(&mut loops);

    // Reject nested loops: body of one loop contains a node from another.
    for i in 0..loops.len() {
        for j in (i + 1)..loops.len() {
            if loops[i].body.iter().any(|n| loops[j].body.contains(n)) {
                log::debug!(
                    target: "bmc",
                    "nested loops detected — BMC not supported for this function"
                );
                return None;
            }
        }
    }

    let mut bmc_cfg = cfg.clone();

    // For each loop, track additional copies of the assertion node so we can
    // check violations that occur at a specific iteration depth.
    let mut assertion_node_copies: Vec<CfgNodeId> = vec![site.node];

    for loop_info in &loops {
        let copy_maps = unroll_single_loop(&mut bmc_cfg, loop_info, bound);

        if loop_info.body.contains(&site.node) {
            for copy_map in &copy_maps {
                if let Some(&new_node) = copy_map.get(&site.node) {
                    assertion_node_copies.push(new_node);
                }
            }
        }

        bmc_cfg.remove_edge(loop_info.back_edge);
    }

    log::debug!(
        target: "bmc",
        "bmc_check: bound={bound} unrolled nodes={} assertion_copies={}",
        bmc_cfg.nodes().len(),
        assertion_node_copies.len()
    );

    // For assertions inside a loop body: check each iteration copy separately.
    // For assertions outside loops: the single backward pass propagates through
    // all k unrolled copies simultaneously, so one check suffices.
    let assertion_in_any_loop = loops.iter().any(|l| l.body.contains(&site.node));
    let sites_to_check: Vec<AssertionSite> = if assertion_in_any_loop {
        assertion_node_copies
            .iter()
            .map(|&node| AssertionSite {
                id: site.id,
                node,
                source_location: site.source_location.clone(),
                location: site.location.clone(),
                obligation: site.obligation.clone(),
            })
            .collect()
    } else {
        vec![site.clone()]
    };

    for check_site in &sites_to_check {
        match backward::analyze(&bmc_cfg, check_site, oracle) {
            Ok(result) if matches!(result.judgement, Judgement::BugFound { .. }) => {
                log::info!(
                    target: "bmc",
                    "bmc_check: BugFound at node {:?} (bound={bound})",
                    check_site.node
                );
                return Some(result);
            }
            Ok(_) => {}
            Err(e) => {
                log::debug!(target: "bmc", "bmc_check: analysis error: {e}");
            }
        }
    }

    None
}

/// Add `bound−1` additional copies of the loop body to `cfg` and wire them
/// together via the back-edge guard.  The original back edge is **not** removed
/// here — the caller must call `cfg.remove_edge(loop_info.back_edge)` after
/// all loops have been processed.
///
/// Returns a list of per-iteration node maps for iterations 1..bound−1.
/// Iteration 0 uses the original (unmodified) node IDs.
fn unroll_single_loop(
    cfg: &mut AbstractCfg,
    loop_info: &LoopInfo,
    bound: usize,
) -> Vec<BTreeMap<CfgNodeId, CfgNodeId>> {
    let mut iteration_maps: Vec<BTreeMap<CfgNodeId, CfgNodeId>> = Vec::new();

    if bound <= 1 {
        return iteration_maps;
    }

    let body_nodes: Vec<CfgNodeId> = loop_info.body.iter().copied().collect();

    // prev_latch tracks the latch node of the most recently added iteration.
    // Starts at the original latch (iteration 0).
    let mut prev_latch = loop_info.latch;

    for i in 1..bound {
        // Create fresh copies of every body node.
        let mut node_map: BTreeMap<CfgNodeId, CfgNodeId> = BTreeMap::new();
        for &orig_id in &body_nodes {
            let (label, transfer) = {
                let n = cfg.node(orig_id).expect("body node exists in cfg");
                (format!("{}_bmc{i}", n.label), n.transfer.clone())
            };
            let new_id = cfg.add_node(label, transfer);
            node_map.insert(orig_id, new_id);
        }

        // Replicate intra-body edges (everything except the back edge).
        let intra: Vec<_> = cfg
            .edges()
            .values()
            .filter(|e| {
                loop_info.body.contains(&e.source)
                    && loop_info.body.contains(&e.target)
                    && e.id != loop_info.back_edge
            })
            .cloned()
            .collect();

        for edge in intra {
            let src = node_map[&edge.source];
            let tgt = node_map[&edge.target];
            cfg.add_edge(src, tgt, edge.guard, edge.effects)
                .expect("newly added nodes must be valid");
        }

        // Connect the previous iteration's latch to this iteration's header.
        let (back_guard, back_effects) = {
            let be = cfg.edge(loop_info.back_edge).expect("back edge exists");
            (be.guard.clone(), be.effects.clone())
        };
        let new_header = node_map[&loop_info.header];
        cfg.add_edge(prev_latch, new_header, back_guard, back_effects)
            .expect("prev_latch and new_header must be valid");

        // Replicate exit edges: each iteration can exit to the same post-loop target.
        let exits: Vec<_> = loop_info
            .exit_edges
            .iter()
            .filter_map(|&eid| cfg.edge(eid).ok().cloned())
            .collect();

        for exit_edge in exits {
            if let Some(&new_src) = node_map.get(&exit_edge.source) {
                cfg.add_edge(
                    new_src,
                    exit_edge.target,
                    exit_edge.guard,
                    exit_edge.effects,
                )
                .expect("new_src and exit target must be valid");
            }
        }

        prev_latch = node_map[&loop_info.latch];
        iteration_maps.push(node_map);
    }

    iteration_maps
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AbstractCfg, TransferFn};
    use crate::common::formula::Formula;

    /// Build a minimal CFG with one loop:
    ///   entry → header → body → latch ──(back)──→ header
    ///                      ↓ (exit)
    ///                   post_loop
    fn make_single_loop_cfg() -> (AbstractCfg, CfgNodeId, CfgNodeId) {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        let header = cfg.add_node("header", TransferFn::identity());
        let body = cfg.add_node("body", TransferFn::identity());
        let latch = cfg.add_node("latch", TransferFn::identity());
        let post_loop = cfg.add_node("post_loop", TransferFn::identity());

        cfg.add_edge(entry, header, Formula::True, vec![]).unwrap();
        cfg.add_edge(header, body, Formula::True, vec![]).unwrap();
        cfg.add_edge(body, latch, Formula::True, vec![]).unwrap();
        // back edge
        cfg.add_edge(latch, header, Formula::True, vec![]).unwrap();
        // exit edge
        cfg.add_edge(latch, post_loop, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(post_loop).unwrap();
        cfg.ensure_single_exit().unwrap();

        (cfg, header, post_loop)
    }

    #[test]
    fn unroll_bound_2_adds_one_copy() {
        let (cfg, header, _post_loop) = make_single_loop_cfg();
        let original_node_count = cfg.nodes().len();

        let loops = detect_loops(&cfg);
        assert_eq!(loops.len(), 1);
        let loop_info = &loops[0];
        assert_eq!(loop_info.header, header);

        let mut bmc_cfg = cfg.clone();
        let maps = unroll_single_loop(&mut bmc_cfg, loop_info, 2);
        bmc_cfg.remove_edge(loop_info.back_edge);

        // One extra copy of all body nodes (3 body nodes: header, body, latch).
        assert_eq!(maps.len(), 1);
        assert_eq!(
            bmc_cfg.nodes().len(),
            original_node_count + loop_info.body.len()
        );

        // Resulting CFG should be acyclic.
        assert!(
            bmc_cfg.topological_order().is_some(),
            "unrolled CFG must be acyclic"
        );
    }

    #[test]
    fn unroll_bound_1_is_noop() {
        let (cfg, header, _) = make_single_loop_cfg();
        let loops = detect_loops(&cfg);
        let loop_info = &loops[0];
        let _ = header;

        let mut bmc_cfg = cfg.clone();
        let maps = unroll_single_loop(&mut bmc_cfg, loop_info, 1);
        assert!(maps.is_empty());
        // Node count unchanged (no copies added, back edge not yet removed).
        assert_eq!(bmc_cfg.nodes().len(), cfg.nodes().len());
    }
}
