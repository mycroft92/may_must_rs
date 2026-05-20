//! DART-style path-enumeration forward MUST.
//!
//! Forward MUST is the **bug-finding pillar** of the bidirectional SMASH
//! analysis (Godefroid/Nori/Rajamani/Tetali, POPL'10).  Where the backward
//! NOT-MAY pillar overapproximates with WP + loop invariants to prove safety,
//! forward MUST under-approximates by enumerating concrete paths and asking
//! the SMT solver "does an input exist that follows this path AND violates
//! the assertion?"  A SAT answer is a real bug witness.
//!
//! The classical algorithm is DART (Directed Automated Random Testing,
//! Godefroid/Klarlund/Sen, PLDI'05): symbolic execution along a chosen
//! concrete path, then a solver query.  We use a simpler bounded variant:
//! depth-first enumeration of all paths up to a configurable depth and
//! per-node revisit count, with one feasibility query per path.
//!
//! # Algorithm sketch
//!
//! ```text
//! dart_explore(cfg, site, phi2, phi1, oracle, config):
//!   paths = enumerate_paths(cfg, entry, site.node, config)
//!   for path in paths.first(config.max_paths):
//!     pc = compute_path_condition(cfg, path, phi1)
//!     report = oracle.feasibility_with_model(pc ∧ phi2)
//!     if report.feasibility == Feasible:
//!       return BugFound { path, model }
//!   return Unknown
//! ```
//!
//! `phi1` is the entry precondition (typically `True` for top-level
//! assertions).  `phi2` is the violation precondition at the **pre-state**
//! of the assertion node — the caller computes
//! `assertion_node.transfer.wp(NOT obligation)` once and passes it in.
//!
//! # Soundness boundaries
//!
//! - `BugFound` is sound: the SAT model is a concrete satisfying assignment
//!   to the path condition AND the violation precondition.
//! - `Unknown` is always sound.
//! - `Verified` is **never** returned by DART.  Proving universal safety is
//!   the NOT-MAY pillar's job.
//!
//! # The append-only formula invariant (P8 from `design_docs/DART.md`)
//!
//! The path condition is built by walking the path's edges in forward order
//! and **conjoining** new constraints as they arise.  Once a conjunct is in
//! the formula, it is never modified, substituted, or rewritten.  The
//! `current_version` and `memory_state` maps are lookup tables used only
//! when **adding** a new constraint; their values get baked in at append
//! time and frozen forever.  Violating this invariant produces the classical
//! retroactive-substitution catastrophe (P1) where a loop's first iteration
//! gets rewritten with the second iteration's SSA names and the formula
//! becomes self-contradictory.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::common::abstract_cfg::{AbstractCfg, AssignValue, CfgEdgeId, CfgNodeId, TransferEffect};
use crate::common::adapter::AssertionSite;
use crate::common::formula::{Formula, Memory, SmtModel, Term, Var};
use crate::common::oracle::{Feasibility, Oracle};
use crate::may_must_analysis::backward::AssertionResult;
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::rules::Judgement;

// ── Public types ─────────────────────────────────────────────────────────

/// Configuration knobs for [`dart_explore`].
///
/// Three independent bounds keep the path search from running away:
///
/// - `max_depth`: total number of CFG edges that any single enumerated path
///   may contain.  Bigger = more thorough; cost is roughly linear in this.
/// - `max_loop_iters`: how many times any single CFG node may be re-entered
///   along the same path.  Effectively the BMC unroll depth, but expressed
///   on the original (cyclic) CFG without physically unrolling it.
/// - `max_paths`: hard cap on the number of enumerated paths.  Useful in
///   branchy CFGs where the path count would explode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DartConfig {
    pub max_depth: usize,
    pub max_loop_iters: usize,
    pub max_paths: usize,
}

impl Default for DartConfig {
    fn default() -> Self {
        Self {
            max_depth: 200,
            max_loop_iters: 4,
            max_paths: 256,
        }
    }
}

/// Concrete bug-witness produced by DART.
#[derive(Clone, Debug)]
pub struct DartPathSummary {
    /// Sequence of edges from `cfg.entry()` to the assertion node.
    pub path: Vec<CfgEdgeId>,
    /// The path condition: a formula constraining program variables to
    /// exactly those inputs that follow `path`.
    pub path_condition: Formula,
    /// Caller-supplied violation precondition (in entry-namespace SSA).
    pub phi2: Formula,
    /// `path_condition ∧ phi2` — the formula whose SAT model is the witness.
    pub combined: Formula,
    /// SMT model assigning concrete values to free variables — the bug input.
    pub model: Option<SmtModel>,
}

/// What [`dart_explore`] decided.
#[derive(Clone, Debug)]
pub enum DartOutcome {
    BugFound(DartPathSummary),
    Unknown,
}

// ── Top-level entry ──────────────────────────────────────────────────────

/// Run DART on `cfg` to look for a concrete bug at `site`.
///
/// `phi2` is the violation precondition at the **pre-state** of `site.node`
/// — call `site.node.transfer.wp(NOT site.obligation)` to obtain it once.
///
/// `phi1` is the entry precondition (typically `Formula::True` for
/// top-level assertions; non-trivial when DART is invoked from a sub-query
/// that constrained the entry).
///
/// On `BugFound`, the returned [`AssertionResult`] is shaped so the caller
/// (the SMASH orchestrator) can return it as-is — `entry_summary.state` is
/// the path condition (used by `CREATE_MUSTSUMMARY` as the concrete pre),
/// and `assertion_summary.state` is `phi2` (the concrete post-precondition).
pub fn dart_explore(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    config: DartConfig,
    debug_names: &HashMap<String, String>,
) -> Option<AssertionResult> {
    let phi1 = Formula::True;
    let neg_obligation = Formula::not(site.obligation.clone());
    let phi2 = cfg.node(site.node).ok()?.transfer.wp(&neg_obligation);

    let paths = enumerate_paths(cfg, cfg.entry(), site.node, &config);
    log::debug!(
        target: "forward_must",
        "dart_explore: enumerated {} paths (max_depth={} max_loop_iters={} max_paths={})",
        paths.len(),
        config.max_depth,
        config.max_loop_iters,
        config.max_paths,
    );

    for (i, path) in paths.iter().enumerate() {
        let (pc, current_version, memory_state) =
            compute_path_condition_with_state(cfg, path, &phi1);
        // phi2 references entry-namespace SSA names that the path may have
        // re-defined.  Substitute it through the path's `current_version` and
        // `memory_state` at combine time so it evaluates against the values
        // visible at the assertion site's pre-state.  This is NOT the §P1
        // anti-pattern — §P1 forbids rewriting the accumulated path-condition
        // formula; here we rewrite the externally-supplied phi2 once, never
        // touching `pc`.
        let phi2_subst = subst_formula_walk(&phi2, &current_version, &memory_state);
        let combined = Formula::and(pc.clone(), phi2_subst.clone());
        let report = oracle.feasibility_with_model(&combined).ok()?;
        log::debug!(
            target: "forward_must",
            "dart_explore: path #{i} (len={}) feasibility={:?}",
            path.len(),
            report.feasibility,
        );
        if report.feasibility == Feasibility::Feasible {
            log::debug!(
                target: "forward_must",
                "dart_explore: BugFound on path #{i}",
            );
            return Some(AssertionResult {
                site_id: site.id,
                site_label: site.location.clone(),
                source_location: site.source_location.clone().into(),
                judgement: Judgement::BugFound {
                    model: report.model.clone(),
                },
                entry_summary: NodeSummary {
                    node: cfg.entry(),
                    reach: Formula::True,
                    state: pc.clone(),
                    must_reach: pc,
                },
                assertion_summary: NodeSummary {
                    node: site.node,
                    reach: Formula::True,
                    state: phi2_subst.clone(),
                    must_reach: phi2_subst,
                },
                debug_names: debug_names.clone(),
            });
        }
    }

    None
}

// ── Step 1: path enumeration ─────────────────────────────────────────────

/// Enumerate paths (edge sequences) from `start` to `target` in `cfg` by DFS.
///
/// Bounded by [`DartConfig::max_depth`] (total edges per path),
/// [`DartConfig::max_loop_iters`] (max times any node may be re-entered on a
/// single path), and [`DartConfig::max_paths`] (cap on result count).
///
/// The decrement-on-backtrack in the DFS is critical: without it, sibling
/// DFS branches at a fork share the same visit-count quota for downstream
/// nodes, and the second sibling gets incorrectly pruned.  See
/// `design_docs/DART.md` §3.1.
pub fn enumerate_paths(
    cfg: &AbstractCfg,
    start: CfgNodeId,
    target: CfgNodeId,
    config: &DartConfig,
) -> Vec<Vec<CfgEdgeId>> {
    let mut out: Vec<Vec<CfgEdgeId>> = Vec::new();
    let mut current: Vec<CfgEdgeId> = Vec::new();
    let mut visit_count: HashMap<CfgNodeId, usize> = HashMap::new();
    dfs(
        cfg,
        start,
        target,
        config.max_depth,
        config.max_loop_iters,
        &mut current,
        &mut visit_count,
        &mut out,
        config.max_paths,
    );
    out
}

#[allow(clippy::too_many_arguments)]
fn dfs(
    cfg: &AbstractCfg,
    node: CfgNodeId,
    target: CfgNodeId,
    remaining_depth: usize,
    max_iters: usize,
    current: &mut Vec<CfgEdgeId>,
    visit_count: &mut HashMap<CfgNodeId, usize>,
    out: &mut Vec<Vec<CfgEdgeId>>,
    max_paths: usize,
) {
    if out.len() >= max_paths {
        return;
    }
    if node == target {
        out.push(current.clone());
        return;
    }
    if remaining_depth == 0 {
        return;
    }

    {
        let count = visit_count.entry(node).or_insert(0);
        if *count >= max_iters {
            return;
        }
        *count += 1;
    }

    for edge_id in cfg.outgoing_edges(node) {
        if out.len() >= max_paths {
            break;
        }
        let Ok(edge) = cfg.edge(edge_id) else {
            continue;
        };
        let succ = edge.target;
        current.push(edge_id);
        dfs(
            cfg,
            succ,
            target,
            remaining_depth - 1,
            max_iters,
            current,
            visit_count,
            out,
            max_paths,
        );
        current.pop();
    }

    // Decrement on backtrack so sibling DFS branches each get their own
    // visit-count quota on this node.  See `design_docs/DART.md` §3.1.
    if let Some(c) = visit_count.get_mut(&node) {
        *c = c.saturating_sub(1);
    }
}

// ── Step 2: path condition ───────────────────────────────────────────────

/// Build the path condition: a formula constraining program variables to
/// exactly the inputs that follow `path`.
///
/// Walks edges in order, processing each edge's source node's transfer
/// effects, then the edge's guard, then the edge's effects.  Maintains
/// three pieces of state local to this walk:
///
/// - `current_version` — for each SSA variable that has been re-defined,
///   maps the original name to its current versioned name.  When a node is
///   visited for the k-th time (k ≥ 2), any [`TransferEffect::Assign`]
///   target gets renamed to `<orig>$n{node_id}v{k}`.
/// - `memory_state` — for each memory region, the current symbolic memory
///   expression (a chain of [`Memory::Store`] applications on top of
///   [`Memory::Var`]).  A `MemoryStore` effect extends this chain; a later
///   `Select` in some loaded term sees the stored value via Z3 array axioms.
/// - `node_visit_count` — counts visits to each node so the versioning
///   above is unique per `(node, visit)`.
///
/// **Append-only:** once a conjunct is in `formula`, neither map is allowed
/// to retroactively change it.  Reads are substituted **eagerly** at the
/// moment a new conjunct is appended.  See `design_docs/DART.md` §P8.
pub fn compute_path_condition(cfg: &AbstractCfg, path: &[CfgEdgeId], phi1: &Formula) -> Formula {
    compute_path_condition_with_state(cfg, path, phi1).0
}

/// Same as [`compute_path_condition`] but also returns the final
/// `current_version` and `memory_state` so the caller can substitute an
/// external formula (typically the assertion's `phi2`) through them once at
/// combine time.
///
/// **Why expose final state?**  The path condition uses the path's renamed
/// SSA names (e.g. `x$n{cond}v2`) for variables that were re-defined along
/// the path.  An externally-supplied formula like `phi2 = wp(assert)(¬O)`
/// references those variables under their entry-namespace names (`x`).  The
/// caller must substitute `phi2` through the returned `current_version` so
/// it evaluates against the values visible at the assertion site's
/// pre-state.  Only `phi2` is rewritten; the path condition itself remains
/// append-only (§P1 / §P8).
pub fn compute_path_condition_with_state(
    cfg: &AbstractCfg,
    path: &[CfgEdgeId],
    phi1: &Formula,
) -> (Formula, HashMap<String, String>, HashMap<String, Memory>) {
    let mut formula = phi1.clone();
    let mut current_version: HashMap<String, String> = HashMap::new();
    let mut memory_state: HashMap<String, Memory> = HashMap::new();
    let mut node_visit_count: HashMap<CfgNodeId, u32> = HashMap::new();
    let mut defined: HashSet<String> = HashSet::new();

    for edge_id in path {
        let Ok(edge) = cfg.edge(*edge_id) else {
            continue;
        };
        let edge = edge.clone();

        // 1. Bump visit count of the SOURCE node — its transfer effects run now.
        let src_visit = {
            let c = node_visit_count.entry(edge.source).or_insert(0);
            *c += 1;
            *c
        };

        // 2. Source node's transfer effects.
        if let Ok(src_node) = cfg.node(edge.source) {
            for effect in &src_node.transfer.effects {
                apply_path_effect(
                    &mut formula,
                    effect,
                    &mut current_version,
                    &mut memory_state,
                    &mut defined,
                    edge.source,
                    src_visit,
                );
            }
        }

        // 3. Edge guard (substituted through state AT THIS POINT, then conjoined).
        let guard_subst = subst_formula_walk(&edge.guard, &current_version, &memory_state);
        formula = conjoin(formula, guard_subst);

        // 4. Edge effects (phi assignments).  Per §P5, use the TARGET's
        // UPCOMING visit count (its current count + 1), because phi-assigned
        // names belong to the target block.
        let tgt_visit = *node_visit_count.get(&edge.target).unwrap_or(&0) + 1;
        for effect in &edge.effects {
            apply_path_effect(
                &mut formula,
                effect,
                &mut current_version,
                &mut memory_state,
                &mut defined,
                edge.target,
                tgt_visit,
            );
        }
    }

    // §P1 / §P8: do NOT do a final substitution of the accumulated formula
    // through current_version.  Reads were already substituted eagerly.
    (formula, current_version, memory_state)
}

/// Apply one effect to the path-condition state.
///
/// - `Assign { target, Term(t) }`: substitute `t` through current state, then
///   bump `target`'s version if revisiting, and conjoin
///   `versioned_target = t_subst`.
/// - `Assign { target, Predicate(p) }`: same with `iff`.
/// - `Assume(c)` / `Obligation(c)` / `TypeBound(c)`: substitute `c` and
///   conjoin.  TypeBound and Assume are both sp-conjoin in this forward
///   direction (the inductive-WP distinction is irrelevant for path
///   conditions).
/// - `MemoryStore { region, offset, value }`: extend `memory_state[region]`
///   to `Store(prev, offset_subst, value_subst)`.  Formula unchanged — the
///   store surfaces on later `Select`s via substitution.
/// - Everything else: no-op.  §P4: these are sp-identity after
///   `resolve_memory_effects`; do **not** apply sp to the whole formula.
fn apply_path_effect(
    formula: &mut Formula,
    effect: &TransferEffect,
    current_version: &mut HashMap<String, String>,
    memory_state: &mut HashMap<String, Memory>,
    defined: &mut HashSet<String>,
    node_id: CfgNodeId,
    visit_count: u32,
) {
    match effect {
        TransferEffect::Assign {
            target,
            value: AssignValue::Term(t),
        } => {
            // Substitute the RHS through the OLD version map (so a
            // self-referential `x = x + 1` reads the old `x`).
            let t_subst = subst_term_walk(t, current_version, memory_state);
            // Now version the target.
            let versioned = version_var(target, node_id, visit_count, current_version, defined);
            *formula = conjoin(formula.clone(), Formula::eq(Term::Var(versioned), t_subst));
        }
        TransferEffect::Assign {
            target,
            value: AssignValue::Predicate(p),
        } => {
            let p_subst = subst_formula_walk(p, current_version, memory_state);
            let versioned = version_var(target, node_id, visit_count, current_version, defined);
            *formula = conjoin(
                formula.clone(),
                Formula::iff(Formula::Var(versioned), p_subst),
            );
        }
        TransferEffect::Assume(c)
        | TransferEffect::Obligation(c)
        | TransferEffect::TypeBound(c) => {
            let c_subst = subst_formula_walk(c, current_version, memory_state);
            *formula = conjoin(formula.clone(), c_subst);
        }
        TransferEffect::MemoryStore {
            region,
            offset,
            value,
        } => {
            let offset_subst = subst_term_walk(offset, current_version, memory_state);
            let value_subst = subst_term_walk(value, current_version, memory_state);
            let prev = memory_state
                .get(region)
                .cloned()
                .unwrap_or_else(|| Memory::var(region));
            memory_state.insert(
                region.clone(),
                Memory::store(prev, offset_subst, value_subst),
            );
        }
        // §P4: everything else is no-op.  Alloca/GEP/PointerLoad/PointerStore/
        // PointerAlias/IntToPtr/Call/HavocRegions/HeapAlloc/IndirectCall/Load/
        // Store/Nop — sp-identity after `resolve_memory_effects` rewrote the
        // resolved ones into `Assign` / `MemoryStore`.  Applying `tf.sp` to
        // the entire accumulated formula would violate §P8.
        _ => {}
    }
}

/// SSA versioning with defined-set tracking.
///
/// The first definition of a variable (on any node visit) keeps its
/// original name — this gives clean formulas for the common single-static-
/// assignment case where each variable is assigned exactly once.  Any
/// later definition — whether on a revisit of the same node (`visit_count
/// >= 2`) or a definition at a different node — gets a fresh name
/// `<orig>$n{node_id}v{visit_count}`.  Node ids are globally unique and
/// visit counts are per-node monotonic, so the resulting fresh names are
/// unique without a shared counter (§P2 / §P3).
///
/// **Why the `defined` set is needed (extension beyond `design_docs/DART.md`):**
/// The doc's spec says "first visit (k = 1) keeps the original name."
/// That's correct for true SSA inputs where each variable is defined at
/// most once across the entire CFG.  Our adapter's lowering occasionally
/// produces non-SSA shapes (phi assignments on edges that re-define a
/// header-phi variable across iterations), and hand-built test CFGs do
/// too.  Without `defined` tracking, the second definition of `x` on a
/// first visit of a different node would re-use the original name and
/// produce a self-contradictory conjunct (e.g. `x = 1 ∧ x = x - 1`).
/// Tracking `defined` and bumping the version on re-definition fixes this
/// while preserving doc-spec behaviour for true-SSA inputs.
fn version_var(
    target: &Var,
    node_id: CfgNodeId,
    visit_count: u32,
    current_version: &mut HashMap<String, String>,
    defined: &mut HashSet<String>,
) -> Var {
    let orig = target.name().to_string();
    let first_definition = visit_count == 1 && !defined.contains(&orig);
    if first_definition {
        defined.insert(orig.clone());
        current_version.remove(&orig);
        target.clone()
    } else {
        let fresh_name = format!("{}$n{}v{}", orig, node_id.0, visit_count);
        defined.insert(fresh_name.clone());
        current_version.insert(orig, fresh_name.clone());
        Var::new(fresh_name, target.sort())
    }
}

// ── Substitution helpers ─────────────────────────────────────────────────

/// Substitute through `current_version` (var-rename) and `memory_state`
/// (region replacement) in one pass.
///
/// Composition order: rename vars first, then replace memory regions.  Both
/// passes only insert; they never reach back into the result of the other.
fn subst_formula_walk(
    formula: &Formula,
    current_version: &HashMap<String, String>,
    memory_state: &HashMap<String, Memory>,
) -> Formula {
    let mut f = formula.clone();
    for (orig, fresh) in current_version {
        // We don't know the original Var's sort, so we use a name-only
        // substitution that walks both scalar and Bool sites.  The underlying
        // `substitute_var_in_formula` matches by name only, and we use
        // `substitute_bool_var_in_formula` for Bool sites separately.
        let int_target = Var::new(orig.clone(), crate::common::formula::Sort::Int);
        let int_replacement = Term::Var(Var::new(fresh.clone(), crate::common::formula::Sort::Int));
        f = crate::common::abstract_cfg::substitute_var_in_formula(
            &int_target,
            &int_replacement,
            &f,
        );
        let bool_target = Var::new(orig.clone(), crate::common::formula::Sort::Bool);
        let bool_replacement =
            Formula::Var(Var::new(fresh.clone(), crate::common::formula::Sort::Bool));
        f = crate::common::abstract_cfg::substitute_bool_var_in_formula(
            &bool_target,
            &bool_replacement,
            &f,
        );
    }
    for (region, mem) in memory_state {
        f = crate::common::abstract_cfg::substitute_memory_var_in_formula(region, mem, &f);
    }
    f
}

fn subst_term_walk(
    term: &Term,
    current_version: &HashMap<String, String>,
    memory_state: &HashMap<String, Memory>,
) -> Term {
    let mut t = term.clone();
    for (orig, fresh) in current_version {
        let int_target = Var::new(orig.clone(), crate::common::formula::Sort::Int);
        let int_replacement = Term::Var(Var::new(fresh.clone(), crate::common::formula::Sort::Int));
        t = crate::common::abstract_cfg::substitute_var_in_term(&int_target, &int_replacement, &t);
    }
    for (region, mem) in memory_state {
        t = crate::common::abstract_cfg::substitute_memory_var_in_term(region, mem, &t);
    }
    t
}

/// Conjoin two formulas with simplification (drops `True` neutrals).
fn conjoin(lhs: Formula, rhs: Formula) -> Formula {
    Formula::and(lhs, rhs)
}

// ── Tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AssignValue, TransferEffect, TransferFn};
    use crate::common::formula::{Sort, Term, Var};
    use crate::common::oracle::Oracle;

    fn assign_int(name: &str, value: Term) -> TransferEffect {
        TransferEffect::Assign {
            target: Var::new(name, Sort::Int),
            value: AssignValue::Term(value),
        }
    }

    /// Straightline CFG: entry → mid → assert.  No loops.  Assertion is
    /// `x > 0`, but path sets `x = -1` → bug.
    #[test]
    fn dart_finds_bug_on_straightline() {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        cfg.set_entry_transfer(TransferFn::new(vec![assign_int("x", Term::int(-1))]));
        let assert_node = cfg.add_node("assert", TransferFn::identity());
        cfg.add_edge(entry, assert_node, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(assert_node).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 0,
            node: assert_node,
            source_location: crate::common::abstract_cfg::SourceLocation::new("", 0, 0),
            location: "assert".into(),
            obligation: Formula::gt(Term::var("x", Sort::Int), Term::int(0)),
        };

        let oracle = Oracle::new();
        let cfg_after = {
            // sanity: a path exists
            let paths = enumerate_paths(&cfg, cfg.entry(), assert_node, &DartConfig::default());
            assert!(!paths.is_empty(), "expected at least one path");
            cfg
        };
        let result = dart_explore(
            &cfg_after,
            &site,
            &oracle,
            DartConfig::default(),
            &HashMap::new(),
        );
        let result = result.expect("DART should find the bug");
        assert!(
            matches!(result.judgement, Judgement::BugFound { .. }),
            "expected BugFound, got {:?}",
            result.judgement
        );
    }

    /// Straightline CFG with `x = 1` → assertion `x > 0` holds → DART
    /// returns Unknown (no path violates).
    #[test]
    fn dart_returns_unknown_when_assertion_holds_on_all_paths() {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        cfg.set_entry_transfer(TransferFn::new(vec![assign_int("x", Term::int(1))]));
        let assert_node = cfg.add_node("assert", TransferFn::identity());
        cfg.add_edge(entry, assert_node, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(assert_node).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 0,
            node: assert_node,
            source_location: crate::common::abstract_cfg::SourceLocation::new("", 0, 0),
            location: "assert".into(),
            obligation: Formula::gt(Term::var("x", Sort::Int), Term::int(0)),
        };

        let oracle = Oracle::new();
        let result = dart_explore(&cfg, &site, &oracle, DartConfig::default(), &HashMap::new());
        assert!(
            result.is_none(),
            "expected Unknown (None), got {:?}",
            result.map(|r| r.judgement)
        );
    }

    /// Branchy CFG: entry has two successors with opposite guards on `x`.
    /// One branch keeps `x` safe, the other violates the assertion.
    /// DART must find the violating path.
    #[test]
    fn dart_finds_bug_on_branchy_cfg() {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        let safe = cfg.add_node("safe", TransferFn::identity());
        let unsafe_node = cfg.add_node("unsafe", TransferFn::identity());
        let merge = cfg.add_node("merge", TransferFn::identity());

        // x > 0 → safe; otherwise unsafe.
        let cmp = Formula::gt(Term::var("x", Sort::Int), Term::int(0));
        cfg.add_edge(entry, safe, cmp.clone(), vec![]).unwrap();
        cfg.add_edge(entry, unsafe_node, Formula::not(cmp), vec![])
            .unwrap();
        cfg.add_edge(safe, merge, Formula::True, vec![]).unwrap();
        cfg.add_edge(unsafe_node, merge, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(merge).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 0,
            node: merge,
            source_location: crate::common::abstract_cfg::SourceLocation::new("", 0, 0),
            location: "merge".into(),
            obligation: Formula::gt(Term::var("x", Sort::Int), Term::int(0)),
        };

        let oracle = Oracle::new();
        let result = dart_explore(&cfg, &site, &oracle, DartConfig::default(), &HashMap::new());
        let result = result.expect("DART should find the bug on the unsafe branch");
        assert!(matches!(result.judgement, Judgement::BugFound { .. }));
    }

    /// The true-then-false loop-header pattern (§P6 from the design doc).
    ///
    /// CFG: entry → cond → body → cond → assert.
    /// Body decrements `x`.  Guard is `x > 0`.  Assertion is `x > 0` at exit.
    ///
    /// 1-iteration path: entry sets x = 1, cond visit 1 true (1 > 0), body
    /// sets x = 0, cond visit 2 false (0 > 0 = false), exit.  At exit
    /// `x = 0` violates `x > 0`.  This is the path DART must find.
    ///
    /// Critically: the cond node is visited twice on this path, with
    /// opposite branch directions.  If we accidentally retroactively
    /// substitute the 1st guard (`cmp = (x > 0)`) with the 2nd-visit's
    /// versioned name, the formula contains both `cmp` and `!cmp$nNv2` in a
    /// contradictory way and the path becomes spuriously UNSAT.  This test
    /// would catch that regression.
    #[test]
    fn dart_finds_bug_on_true_then_false_loop_pattern() {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        // Entry: x = 1 (so the 1-iteration path is the witness).
        cfg.set_entry_transfer(TransferFn::new(vec![assign_int("x", Term::int(1))]));

        // cond node: cmp = (x > 0).
        let cond = cfg.add_node(
            "cond",
            TransferFn::new(vec![TransferEffect::Assign {
                target: Var::new("cmp", Sort::Bool),
                value: AssignValue::Predicate(Formula::gt(Term::var("x", Sort::Int), Term::int(0))),
            }]),
        );

        // body node: x = x - 1.
        let body = cfg.add_node(
            "body",
            TransferFn::new(vec![assign_int(
                "x",
                Term::sub(Term::var("x", Sort::Int), Term::int(1)),
            )]),
        );

        let exit = cfg.add_node("exit", TransferFn::identity());

        cfg.add_edge(entry, cond, Formula::True, vec![]).unwrap();
        // cond → body when cmp is true.
        cfg.add_edge(
            cond,
            body,
            Formula::Var(Var::new("cmp", Sort::Bool)),
            vec![],
        )
        .unwrap();
        // body → cond (back-ish edge, but DART doesn't care about back edges).
        cfg.add_edge(body, cond, Formula::True, vec![]).unwrap();
        // cond → exit when !cmp.
        cfg.add_edge(
            cond,
            exit,
            Formula::not(Formula::Var(Var::new("cmp", Sort::Bool))),
            vec![],
        )
        .unwrap();
        cfg.mark_exit(exit).unwrap();
        cfg.ensure_single_exit().unwrap();

        // Assertion at exit: x > 0.  Witnessed-false by the 1-iteration path
        // where x becomes 0.
        let site = AssertionSite {
            id: 0,
            node: exit,
            source_location: crate::common::abstract_cfg::SourceLocation::new("", 0, 0),
            location: "exit".into(),
            obligation: Formula::gt(Term::var("x", Sort::Int), Term::int(0)),
        };

        let oracle = Oracle::new();
        let result = dart_explore(&cfg, &site, &oracle, DartConfig::default(), &HashMap::new());
        let result =
            result.expect("DART must find the 1-iteration bug (true-then-false loop pattern, §P6)");
        assert!(matches!(result.judgement, Judgement::BugFound { .. }));
    }

    /// MemoryStore + later Select sees the stored value via the local
    /// `memory_state` chain (§3.2.3).
    ///
    /// Path: entry stores `42` at offset `0` in region `arr`, then assertion
    /// node loads from `arr[0]` and checks it is `> 100`.  Should be a bug
    /// (42 is not > 100).
    #[test]
    fn dart_memory_store_visible_through_select() {
        use crate::common::abstract_cfg::TransferEffect;
        use crate::common::formula::Memory;
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        // entry: arr[0] := 42; then x := select(arr, 0).
        cfg.set_entry_transfer(TransferFn::new(vec![
            TransferEffect::MemoryStore {
                region: "arr".into(),
                offset: Term::int(0),
                value: Term::int(42),
            },
            TransferEffect::Assign {
                target: Var::new("x", Sort::Int),
                value: AssignValue::Term(Term::select(Memory::var("arr"), Term::int(0))),
            },
        ]));
        let assert_node = cfg.add_node("assert", TransferFn::identity());
        cfg.add_edge(entry, assert_node, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(assert_node).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 0,
            node: assert_node,
            source_location: crate::common::abstract_cfg::SourceLocation::new("", 0, 0),
            location: "assert".into(),
            obligation: Formula::gt(Term::var("x", Sort::Int), Term::int(100)),
        };

        let oracle = Oracle::new();
        let result = dart_explore(&cfg, &site, &oracle, DartConfig::default(), &HashMap::new());
        let result = result.expect("DART should see x = 42 through the store/select chain");
        assert!(matches!(result.judgement, Judgement::BugFound { .. }));
    }

    /// Version_var produces unique names per (node, visit) — §P2 regression
    /// test.  First definition keeps the original name; revisits and
    /// re-definitions at other nodes all produce distinct `$n{N}v{k}`
    /// suffixes.
    #[test]
    fn version_var_produces_unique_names_per_node_visit() {
        let mut cv = HashMap::new();
        let mut defined = HashSet::new();
        let v1 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(5),
            1,
            &mut cv,
            &mut defined,
        );
        assert_eq!(v1.name(), "x", "first definition keeps the original name");
        let v2 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(5),
            2,
            &mut cv,
            &mut defined,
        );
        assert_eq!(v2.name(), "x$n5v2");
        let v3 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(7),
            2,
            &mut cv,
            &mut defined,
        );
        assert_eq!(v3.name(), "x$n7v2");
        let v4 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(5),
            3,
            &mut cv,
            &mut defined,
        );
        assert_eq!(v4.name(), "x$n5v3");
        assert_ne!(v2.name(), v3.name());
        assert_ne!(v2.name(), v4.name());
    }

    /// Re-definition at a *different* node (non-SSA input) on visit=1 still
    /// bumps the version — exercising the `defined` set so the doc-spec
    /// rule "first visit keeps original" does NOT accidentally let two
    /// nodes both assign to the same SSA name in a single path.
    #[test]
    fn version_var_redefinition_on_first_visit_bumps_version() {
        let mut cv = HashMap::new();
        let mut defined = HashSet::new();
        let v1 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(2),
            1,
            &mut cv,
            &mut defined,
        );
        assert_eq!(v1.name(), "x");
        let v2 = version_var(
            &Var::new("x", Sort::Int),
            CfgNodeId(3),
            1,
            &mut cv,
            &mut defined,
        );
        assert_eq!(
            v2.name(),
            "x$n3v1",
            "re-defining x at a different node must produce a fresh name"
        );
    }

    /// The DFS decrement-on-backtrack invariant (§3.1).  Two siblings of a
    /// fork must each get max_loop_iters worth of visits to the joined node,
    /// not share a single quota.
    #[test]
    fn dfs_decrement_on_backtrack_gives_siblings_independent_quotas() {
        let mut cfg = AbstractCfg::new("entry");
        let entry = cfg.entry();
        let left = cfg.add_node("left", TransferFn::identity());
        let right = cfg.add_node("right", TransferFn::identity());
        let mid = cfg.add_node("mid", TransferFn::identity());
        let target = cfg.add_node("target", TransferFn::identity());

        cfg.add_edge(entry, left, Formula::True, vec![]).unwrap();
        cfg.add_edge(entry, right, Formula::True, vec![]).unwrap();
        cfg.add_edge(left, mid, Formula::True, vec![]).unwrap();
        cfg.add_edge(right, mid, Formula::True, vec![]).unwrap();
        cfg.add_edge(mid, target, Formula::True, vec![]).unwrap();
        cfg.mark_exit(target).unwrap();
        cfg.ensure_single_exit().unwrap();

        let config = DartConfig {
            max_depth: 200,
            max_loop_iters: 1,
            max_paths: 256,
        };
        let paths = enumerate_paths(&cfg, cfg.entry(), target, &config);
        // Both left and right branches must yield a path to target.
        assert_eq!(
            paths.len(),
            2,
            "both siblings should produce a path; got {paths:?}"
        );
    }
}
