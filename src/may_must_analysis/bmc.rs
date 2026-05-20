//! Bounded model checking (BMC) via loop unrolling.
//!
//! BMC is sound for **bug finding only**: a `BugFound` result is a real
//! counterexample.  The absence of a bug within the bound is UNKNOWN.
//!
//! # Backend: single WP pass + one SAT query
//!
//! After unrolling, the CFG is acyclic.  Rather than running the full
//! bidirectional fixpoint engine (designed for proving, not for finding bugs),
//! [`bmc_sat_check`] does:
//!
//! 1. Seed `state[assertion_node] = transfer_fn.wp(NOT obligation)`.
//! 2. One backward pass in reverse topological order: propagate each node's
//!    state through its incoming edges (edge effects + guard + source transfer),
//!    OR-joining at merge points.  No intermediate SMT queries.
//! 3. One `feasibility_with_model` at the entry.  SAT → `BugFound`; else None.
//!
//! This is O(1) SMT queries per depth (versus O(edges) for the proof engine).
//!
//! # Incremental deepening
//!
//! [`bmc_check`] tries k = 1, 2, …, bound in order and stops at the first bug.
//! Each depth gets a fresh unrolled CFG.  Bugs reachable in fewer iterations are
//! found without paying for deeper unrollings.
//!
//! # Unrolling strategy
//!
//! For a loop with body nodes `{H, B…, L}` and back edge `L→H`:
//! - Iteration 0 reuses the original nodes.
//! - Iterations 1..=k are fresh copies (k extra copies per depth k).
//! - Exit edges are replicated on every copy so the loop can exit after
//!   0, 1, …, or exactly k full iterations.
//! - The latch of the final copy is a dead end.
//!
//! Nested loops are not supported; independent loops are each unrolled with
//! the same bound.

use crate::common::abstract_cfg::{AbstractCfg, CfgNodeId};
use crate::common::adapter::AssertionSite;
use crate::common::alpha_rename;
use crate::common::formula::Formula;
use crate::common::oracle::{Feasibility, Oracle};
use crate::may_must_analysis::backward::AssertionResult;
use crate::may_must_analysis::loops::{detect_loops, sort_innermost_first, LoopInfo};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::rules::Judgement;
use std::collections::{BTreeMap, HashMap};

/// Try to find a bug in `site` within `bound` loop iterations.
///
/// Uses incremental deepening: tries k = 1, 2, …, bound in order, stopping
/// at the first counterexample.  Each depth unrolls the CFG k times and runs
/// one SAT query (via [`bmc_sat_check`]) — no fixpoint engine, no intermediate
/// SMT calls.  Returns `None` when no bug is found within the bound (UNKNOWN).
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

    let assertion_in_any_loop = loops.iter().any(|l| l.body.contains(&site.node));

    for k in 1..=bound {
        let mut bmc_cfg = cfg.clone();
        let mut assertion_node_copies: Vec<CfgNodeId> = vec![site.node];

        for loop_info in &loops {
            let copy_maps = unroll_single_loop(&mut bmc_cfg, loop_info, k);
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
            "bmc_check: k={k} nodes={} assertion_copies={}",
            bmc_cfg.nodes().len(),
            assertion_node_copies.len()
        );

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
            if let Some(result) = bmc_sat_check(&bmc_cfg, check_site, oracle) {
                log::info!(
                    target: "bmc",
                    "bmc_check: BugFound at node {:?} (k={k})",
                    check_site.node
                );
                return Some(result);
            }
        }

        log::debug!(target: "bmc", "bmc_check: k={k} no bug found");
    }

    None
}

/// Single-pass WP bug-finder for an acyclic (BMC-unrolled) CFG.
///
/// Propagates `NOT obligation` backward in one topological pass — no fixpoint,
/// no `reach` component, no intermediate SMT calls.  One `feasibility_with_model`
/// at the entry: SAT means a real counterexample exists at this unroll depth.
fn bmc_sat_check(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
) -> Option<AssertionResult> {
    // Acyclicity guard — returns None if back edges weren't removed.
    let topo = cfg.topological_order()?;

    let mut state: BTreeMap<CfgNodeId, Formula> = BTreeMap::new();

    // Seed: WP of (NOT obligation) through the assertion node's transfer fn.
    let neg_obligation = Formula::not(site.obligation.clone());
    let pre_at_site = cfg.node(site.node).ok()?.transfer.wp(&neg_obligation);
    state.insert(site.node, pre_at_site);

    // Backward pass: process each node (reverse topo = successors before
    // predecessors).  For each node that has a state, propagate it backward
    // through every incoming edge and OR-join into the source node's state.
    //
    // This is exactly the `notmay_pre` rule from `rules.rs:204`, applied once
    // per edge in topological order instead of inside a fixpoint loop, with
    // `join_state` (OR) at merge points.  The proof engine runs the same
    // computation but also fires `notmay_pre_pruned` (one SMT query per edge)
    // to prune infeasible paths early using `reach`.  For bug-finding on an
    // acyclic CFG there is no `reach` component, so pruning is skipped and the
    // cost is O(1) SMT queries (one feasibility check at the entry) versus
    // O(edges) for the proof engine path.
    for &node in topo.iter().rev() {
        let Some(node_state) = state.get(&node).cloned() else {
            continue;
        };
        for edge_id in cfg.incoming_edges(node) {
            let Ok(edge) = cfg.edge(edge_id) else {
                continue;
            };
            let edge = edge.clone();
            // edge.transfer().wp(node_state) — same as notmay_pre's edge_pre
            let edge_pre = edge.transfer().wp(&node_state);
            // AND guard — same as notmay_pre's post_at_source
            let guarded = Formula::and(edge.guard.clone(), edge_pre);
            // source.transfer.wp(guarded) — same as notmay_pre's pre_at_source
            let Ok(src_node) = cfg.node(edge.source) else {
                continue;
            };
            let src_pre = src_node.transfer.wp(&guarded);
            // OR-join — same as join_state in node_summary.rs
            let acc = state.entry(edge.source).or_insert(Formula::False);
            *acc = Formula::or(acc.clone(), src_pre);
        }
    }

    let entry_state = state.get(&cfg.entry()).cloned().unwrap_or(Formula::False);
    let report = oracle.feasibility_with_model(&entry_state).ok()?;

    if report.feasibility != Feasibility::Feasible {
        return None;
    }

    Some(AssertionResult {
        site_id: site.id,
        site_label: site.location.clone(),
        source_location: site.source_location.clone().into(),
        judgement: Judgement::BugFound {
            model: report.model,
        },
        entry_summary: NodeSummary {
            node: cfg.entry(),
            reach: Formula::True,
            state: entry_state.clone(),
            // BMC's bug witness is a concrete reachable bug state at the
            // assertion site, propagated back to the entry through the
            // unrolled (acyclic) CFG.  Therefore the entry-side under-
            // approximation is just `True` constrained by the entry state.
            must_reach: entry_state,
        },
        assertion_summary: NodeSummary {
            node: site.node,
            reach: Formula::True,
            state: neg_obligation.clone(),
            // At the assertion site the WP-derived violation precondition is
            // identical to the (concrete) must_reach: BMC's feasibility
            // check on the unrolled CFG just confirmed this state is reachable.
            must_reach: neg_obligation,
        },
        debug_names: HashMap::new(),
    })
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

    if bound == 0 {
        return iteration_maps;
    }

    let body_nodes: Vec<CfgNodeId> = loop_info.body.iter().copied().collect();

    // prev_latch tracks the latch node of the most recently added iteration.
    // Starts at the original latch (iteration 0).
    let mut prev_latch = loop_info.latch;

    // Add `bound` extra copies (iterations 1..=bound).  Each copy's header has
    // the original exit edges, so the loop can exit after exactly i iterations.
    for i in 1..=bound {
        // Each copy gets a fresh variable suffix so that SSA variables from
        // different iterations do not interfere in the backward analysis.
        // Memory region names are NOT renamed — they represent shared mutable
        // state (the array, j, menor) that must be visible across iterations.
        let suffix = format!("_bmc{i}");

        // Scalar SSA vars get a fresh suffix per iteration; memory region names
        // stay unchanged so stores from one iteration are visible to the next.
        let var_r = |name: &str| format!("{name}{suffix}");
        let reg_r = |name: &str| name.to_string();

        // Create fresh copies of every body node with renamed transfer fns.
        let mut node_map: BTreeMap<CfgNodeId, CfgNodeId> = BTreeMap::new();
        for &orig_id in &body_nodes {
            let (label, transfer) = {
                let n = cfg.node(orig_id).expect("body node exists in cfg");
                (
                    format!("{}_bmc{i}", n.label),
                    alpha_rename::rename_transfer_fn(&n.transfer, var_r, reg_r),
                )
            };
            let new_id = cfg.add_node(label, transfer);
            node_map.insert(orig_id, new_id);
        }

        // Replicate intra-body edges with renamed guards and effects.
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
            let guard = alpha_rename::rename_formula(&edge.guard, var_r, reg_r);
            let effects = edge
                .effects
                .iter()
                .map(|e| alpha_rename::rename_effect(e, var_r, reg_r))
                .collect();
            cfg.add_edge(src, tgt, guard, effects)
                .expect("newly added nodes must be valid");
        }

        // Connect the previous iteration's latch to this iteration's header.
        // The back-edge guard/effects carry the loop-condition test; rename them.
        let (back_guard, back_effects) = {
            let be = cfg.edge(loop_info.back_edge).expect("back edge exists");
            let guard = alpha_rename::rename_formula(&be.guard, var_r, reg_r);
            let effects = be
                .effects
                .iter()
                .map(|e| alpha_rename::rename_effect(e, var_r, reg_r))
                .collect();
            (guard, effects)
        };
        let new_header = node_map[&loop_info.header];
        cfg.add_edge(prev_latch, new_header, back_guard, back_effects)
            .expect("prev_latch and new_header must be valid");

        // Replicate exit edges with renamed guards and effects.
        let exits: Vec<_> = loop_info
            .exit_edges
            .iter()
            .filter_map(|&eid| cfg.edge(eid).ok().cloned())
            .collect();

        for exit_edge in exits {
            if let Some(&new_src) = node_map.get(&exit_edge.source) {
                let guard = alpha_rename::rename_formula(&exit_edge.guard, var_r, reg_r);
                let effects = exit_edge
                    .effects
                    .iter()
                    .map(|e| alpha_rename::rename_effect(e, var_r, reg_r))
                    .collect();
                cfg.add_edge(new_src, exit_edge.target, guard, effects)
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
    fn unroll_bound_1_adds_one_copy() {
        let (cfg, header, _post_loop) = make_single_loop_cfg();
        let original_node_count = cfg.nodes().len();

        let loops = detect_loops(&cfg);
        assert_eq!(loops.len(), 1);
        let loop_info = &loops[0];
        assert_eq!(loop_info.header, header);

        let mut bmc_cfg = cfg.clone();
        let maps = unroll_single_loop(&mut bmc_cfg, loop_info, 1);
        bmc_cfg.remove_edge(loop_info.back_edge);

        // bound=1 adds 1 extra copy so "exit after 1 iteration" is reachable.
        assert_eq!(maps.len(), 1);
        assert_eq!(
            bmc_cfg.nodes().len(),
            original_node_count + loop_info.body.len()
        );

        assert!(
            bmc_cfg.topological_order().is_some(),
            "unrolled CFG must be acyclic"
        );
    }

    #[test]
    fn unroll_bound_2_adds_two_copies() {
        let (cfg, header, _post_loop) = make_single_loop_cfg();
        let original_node_count = cfg.nodes().len();

        let loops = detect_loops(&cfg);
        assert_eq!(loops.len(), 1);
        let loop_info = &loops[0];
        assert_eq!(loop_info.header, header);

        let mut bmc_cfg = cfg.clone();
        let maps = unroll_single_loop(&mut bmc_cfg, loop_info, 2);
        bmc_cfg.remove_edge(loop_info.back_edge);

        // bound=2 adds 2 extra copies (exit after 1 or 2 iterations reachable).
        assert_eq!(maps.len(), 2);
        assert_eq!(
            bmc_cfg.nodes().len(),
            original_node_count + 2 * loop_info.body.len()
        );

        assert!(
            bmc_cfg.topological_order().is_some(),
            "unrolled CFG must be acyclic"
        );
    }
}
