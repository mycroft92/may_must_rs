//! Loop detection and loop-invariant synthesis/verification.
//!
//! # Responsibilities
//!
//! This module is responsible for three related tasks:
//!
//! 1. **Detection** — [`detect_loops`] identifies natural loops in the CFG by
//!    finding back edges and computing the corresponding loop bodies.
//!
//! 2. **Candidate generation** — [`algorithmic_candidates`], [`houdini_candidates`],
//!    and [`chc_loop_invariant`] produce formula candidates using different
//!    strategies; the caller (in `backward.rs`) tries them in order.
//!
//! 3. **Invariant checking** — [`check_loop_invariant_verbose`] performs the
//!    three-part soundness check for a candidate formula:
//!    - **Initiation**: the invariant holds on entry to the loop (checked by
//!      showing the violation condition is infeasible at the function entry).
//!    - **Inductiveness**: if the invariant holds at the header and the back
//!      edge is taken, it still holds at the header on the next iteration
//!      (checked by implication at the header after one step through the body).
//!    - **Exit closure** (optional): for each loop exit edge whose target has a
//!      non-trivial `assertion_postcondition`, the invariant together with the
//!      exit guard implies the postcondition.  This check ties the invariant to
//!      the specific assertion being proved.  It is intentionally skipped in
//!      `observer_summary_invariants` (see `driver.rs`) because the final
//!      `analyze_with_tables` call performs the authoritative discharge.
//!
//! # Nested loops
//!
//! Loops are processed innermost-first (see [`sort_innermost_first`]).  Already-
//! accepted inner invariants are passed as `inner: InnerInvariants` to
//! [`check_loop_invariant_verbose`] and to [`backward_states`] so that inner
//! loop bodies can be summarised without re-entering them.

#![allow(dead_code)]

use crate::common::abstract_cfg::{
    AbstractCfg, AssignValue, CallMemoryEffect, CfgEdgeId, CfgNodeId, SourceLocation,
    TransferEffect,
};
use crate::common::formula::{Formula, Memory, Sort, Term, Var};
use crate::common::oracle::{Oracle, Validity};
use crate::may_must_analysis::chc;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Structural description of a natural loop.
///
/// A natural loop is defined by a single *back edge* (latch → header).  The
/// `body` set contains every CFG node from which the header is reachable
/// without leaving the loop.  `exit_edges` are the CFG edges that leave the
/// body — their targets are the first nodes executed after the loop.
///
/// # Natural loop properties
///
/// - **Header**: the unique entry point; invariants are asserted at the header.
/// - **Latch**: the node that closes the loop; back_edge goes from latch to header.
/// - **Body**: all nodes inside the loop; used to restrict backward propagation.
/// - **Exit edges**: edges leaving the body; used for exit-closure checks.
///
/// # Example structure
///
/// ```text
/// entry → header → body1 → body2 ↓
///          ↑                       ↓
///          └─────── latch ←────────┘
///                     ↓
///                   exit
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopInfo {
    /// Unique entry point of the loop (target of the back edge).
    pub header: CfgNodeId,
    /// Node that closes the loop by branching back to the header.
    pub latch: CfgNodeId,
    /// The back edge from latch to header.
    pub back_edge: CfgEdgeId,
    /// All nodes inside the loop body, including header and latch.
    pub body: BTreeSet<CfgNodeId>,
    /// Edges leaving the loop body to successor nodes outside it.
    pub exit_edges: Vec<CfgEdgeId>,
    /// Guard on the back edge (the loop-continuation condition).
    pub back_edge_guard: Formula,
    /// Source location of the loop header, if available.
    pub source_location: Option<SourceLocation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CounterInit {
    Literal(i64),
    Variable(String),
    Unknown,
}

pub type InnerInvariants<'a> = &'a [(CfgNodeId, Formula)];

/// Detailed outcome of [`check_loop_invariant_verbose`].
///
/// Only `Accepted` means all three soundness conditions passed.  The failure
/// variants identify *which* condition was the first to fail, enabling
/// targeted logging and CEGIS feedback.
///
/// # Soundness checks
///
/// - **Initiation**: the candidate holds on entry (reach at header is empty).
/// - **Inductiveness**: the candidate is preserved by one iteration (holds after).
/// - **Exit closure**: the candidate implies the assertion postcondition at exits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InvariantCheckResult {
    /// Initiation, inductiveness, and exit closure all passed.
    Accepted,
    /// The candidate does not hold on entry to the loop.
    InitiationFailed,
    /// The candidate is not preserved by one iteration of the loop body.
    InductivenessFailed,
    /// The candidate does not imply the required postcondition at this exit.
    ExitClosureFailed { exit_edge: CfgEdgeId },
}

pub fn normalize_candidate(cfg: &AbstractCfg, header: CfgNodeId, candidate: &Formula) -> Formula {
    cfg.node(header)
        .map(|node| node.transfer.wp(candidate))
        .unwrap_or_else(|_| candidate.clone())
}

pub fn fmt_loop_loc(info: &LoopInfo) -> String {
    info.source_location
        .as_ref()
        .map(|location| location.to_string())
        .unwrap_or_else(|| format!("header {:?}", info.header))
}

/// Identify all natural loops in the CFG.
///
/// A natural loop is detected by finding every back edge (an edge whose target
/// dominates its source in the CFG traversal).  For each back edge the loop
/// body is computed by a backward BFS from the latch to the header.  The
/// resulting [`LoopInfo`] structs are returned in an unspecified order; callers
/// that need innermost-first processing should call [`sort_innermost_first`].
///
/// # Algorithm
///
/// 1. Detect back edges via the CFG.
/// 2. For each back edge (source → target), target becomes the header.
/// 3. Backward BFS from source to target to compute the loop body.
/// 4. Collect all edges exiting the body (targets outside body).
pub fn detect_loops(cfg: &AbstractCfg) -> Vec<LoopInfo> {
    cfg.detect_back_edges()
        .into_iter()
        .filter_map(|edge_id| {
            let edge = cfg.edge(edge_id).ok()?.clone();
            let mut body = BTreeSet::new();
            body.insert(edge.target);
            body.insert(edge.source);
            let mut queue = VecDeque::from([edge.source]);
            while let Some(node) = queue.pop_front() {
                for pred in cfg.predecessors(node) {
                    if body.insert(pred) {
                        queue.push_back(pred);
                    }
                }
            }
            let mut exit_edges = Vec::new();
            for node in &body {
                for out in cfg.outgoing_edges(*node) {
                    let out_edge = cfg.edge(out).ok()?;
                    if !body.contains(&out_edge.target) {
                        exit_edges.push(out);
                    }
                }
            }
            Some(LoopInfo {
                header: edge.target,
                latch: edge.source,
                back_edge: edge.id,
                body,
                exit_edges,
                back_edge_guard: edge.guard,
                source_location: cfg
                    .node(edge.target)
                    .ok()
                    .and_then(|node| node.source_location.clone()),
            })
        })
        .collect()
}

/// Sort a slice of loops so that smaller (inner) loops come first.
///
/// The ordering criterion is loop body size.  Processing inner loops before
/// outer ones ensures that their invariants are available when checking the
/// inductiveness of outer loops via the `inner` parameter of
/// [`check_loop_invariant_verbose`].
///
/// # Motivation
///
/// Nested loops can be summarised by their invariants (passed as `inner`) rather
/// than re-entering them during backward propagation.  This requires inner
/// invariants to be computed before outer ones.
pub fn sort_innermost_first(loops: &mut [LoopInfo]) {
    loops.sort_by_key(|info| info.body.len());
}

/// Generate invariant candidates by structural pattern matching on the loop.
///
/// This is the fastest strategy and should be tried first.  It mines candidates
/// from:
/// - The back-edge guard (loop-continuation condition) and its negation.
/// - Entry guards from the header to body nodes.
/// - Exit edge guard negations (loop-termination conditions).
/// - Predicate assignments in the body (and their implication forms).
/// - Counter increment patterns (`i = i + c`) that suggest `i >= 0`.
/// - Integer literal assignments that suggest lower-bound invariants.
///
/// Candidates derived from variables that have constant definitions in the loop
/// body are simplified via substitution using [`normalize_formula_with_defs`].
///
/// # Strategy characteristics
///
/// - **Speed**: O(CFG size) — no solver queries.
/// - **Specificity**: targets counter loops and guards.
/// - **Limitations**: misses non-syntactic invariants.
pub fn algorithmic_candidates(info: &LoopInfo, cfg: &AbstractCfg) -> Vec<Formula> {
    let defs = collect_loop_definitions(info, cfg);
    let mut candidates = Vec::new();
    push_candidate(&mut candidates, &defs, info.back_edge_guard.clone());
    emit_counter_bounds(&mut candidates, &defs, &info.back_edge_guard);
    for edge_id in cfg.outgoing_edges(info.header) {
        if let Ok(edge) = cfg.edge(edge_id) {
            if info.body.contains(&edge.target) {
                push_candidate(&mut candidates, &defs, edge.guard.clone());
                emit_counter_bounds(&mut candidates, &defs, &edge.guard);
            }
        }
    }
    for edge_id in &info.exit_edges {
        if let Ok(edge) = cfg.edge(*edge_id) {
            push_candidate(&mut candidates, &defs, Formula::not(edge.guard.clone()));
            emit_counter_bounds(&mut candidates, &defs, &edge.guard);
        }
    }
    for node in &info.body {
        if let Ok(node) = cfg.node(*node) {
            for effect in &node.transfer.effects {
                match effect {
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Predicate(predicate),
                    } => {
                        push_candidate(&mut candidates, &defs, predicate.clone());
                        push_candidate(&mut candidates, &defs, Formula::not(predicate.clone()));
                        emit_counter_bounds(&mut candidates, &defs, predicate);
                        // Generate all comparison variants (<, <=, >, >=, ==) for comparison predicates.
                        push_comparison_variants(&mut candidates, &defs, predicate);
                        if target.sort() == Sort::Bool {
                            push_candidate(
                                &mut candidates,
                                &defs,
                                Formula::implies(Formula::Var(target.clone()), predicate.clone()),
                            );
                        }
                    }
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Term(Term::Int(value)),
                    } if target.sort() == Sort::Int => {
                        push_candidate(
                            &mut candidates,
                            &defs,
                            Formula::ge(Term::Var(target.clone()), Term::int(*value)),
                        );
                    }
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Term(term),
                    } if target.sort() == Sort::Int => {
                        if is_self_increment(target, term) {
                            push_candidate(
                                &mut candidates,
                                &defs,
                                Formula::ge(Term::Var(target.clone()), Term::int(0)),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    candidates
}

/// Generate a large template set of linear arithmetic candidates (Houdini-style).
///
/// For every integer variable visible in the loop, and for every constant that
/// appears in the assertion postcondition (`header_wp`) or in the loop body,
/// this generates:
/// - Simple bounds `var >= c` and `var <= c`.
/// - Range conjunctions `var >= lo && var <= hi` for all pairs (lo, hi).
/// - Pairwise variable comparisons `v1 <= v2`, `v1 >= v2`, and `v1+1 <= v2`.
///
/// The constants `{-1, 0, 1}` are always included.  The caller is expected to
/// feed these through [`check_loop_invariant_verbose`] and keep only those that
/// pass, gradually weakening to the largest inductive conjunction (Houdini
/// algorithm).
///
/// # Strategy characteristics
///
/// - **Generality**: covers linear arithmetic patterns; generates O(vars^2 * constants^2).
/// - **Cost**: expensive; each candidate requires a solver query.
/// - **Applicability**: works well for loops with counter patterns and linear bounds.
pub fn houdini_candidates(
    variable_sorts: &BTreeMap<String, Sort>,
    header_wp: &Formula,
    loop_constants: &BTreeSet<i64>,
) -> Vec<Formula> {
    let constants = collect_int_constants(header_wp)
        .into_iter()
        .chain(loop_constants.iter().copied())
        .chain([-1, 0, 1])
        .collect::<BTreeSet<_>>();
    let vars = variable_sorts
        .iter()
        .filter_map(|(name, sort)| (*sort == Sort::Int).then_some(Var::int(name.clone())))
        .collect::<Vec<_>>();
    let mut candidates = Vec::new();
    for var in &vars {
        for constant in &constants {
            let term = Term::Var(var.clone());
            candidates.push(Formula::ge(term.clone(), Term::int(*constant)));
            candidates.push(Formula::le(term, Term::int(*constant)));
        }
        let constants_vec = constants.iter().copied().collect::<Vec<_>>();
        for (index, lower) in constants_vec.iter().enumerate() {
            for upper in constants_vec.iter().skip(index + 1) {
                candidates.push(Formula::and(
                    Formula::ge(Term::Var(var.clone()), Term::int(*lower)),
                    Formula::le(Term::Var(var.clone()), Term::int(*upper)),
                ));
            }
        }
    }
    for left in &vars {
        for right in &vars {
            if left == right {
                continue;
            }
            candidates.push(Formula::le(
                Term::Var(left.clone()),
                Term::Var(right.clone()),
            ));
            candidates.push(Formula::ge(
                Term::Var(left.clone()),
                Term::Var(right.clone()),
            ));
            candidates.push(Formula::le(
                Term::add(Term::Var(left.clone()), Term::int(1)),
                Term::Var(right.clone()),
            ));
        }
    }
    candidates
}

/// Derive a loop invariant by solving a Constrained Horn Clause (CHC) system.
///
/// Currently handles the common pattern `i < n` / `i < bound` on the back edge
/// guard: delegates to [`chc::solve_loop_chc`] to produce a closed-form
/// invariant such as `0 <= i && i <= n`.  Returns `None` if the guard does not
/// match the expected pattern.
///
/// # Strategy characteristics
///
/// - **Speed**: fast; delegates to a dedicated CHC solver.
/// - **Specificity**: targets counter-loop patterns (i < bound).
/// - **Limitations**: only handles counter patterns; generic loops get `None`.
pub fn chc_loop_invariant(info: &LoopInfo, cfg: &AbstractCfg) -> Option<Formula> {
    let guard = &info.back_edge_guard;
    if let Formula::Lt(Term::Var(counter), Term::Var(bound)) = guard {
        return chc::solve_loop_chc(counter.clone(), bound.clone(), Some(0), 1, None);
    }
    let _ = cfg;
    None
}

pub fn check_loop_invariant(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    candidate: &Formula,
    oracle: &Oracle,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
) -> bool {
    matches!(
        check_loop_invariant_verbose(
            info,
            cfg,
            candidate,
            oracle,
            assertion_postconditions,
            inner
        ),
        InvariantCheckResult::Accepted
    )
}

/// Check a loop invariant candidate and return a detailed result.
///
/// The three checks performed in order are:
///
/// ## 1. Initiation
///
/// Propagates the *violation* of the candidate backward from the header to the
/// function entry (back edges excluded).  If the violation is reachable from
/// the entry the candidate does not hold on the first iteration →
/// [`InvariantCheckResult::InitiationFailed`].
///
/// ## 2. Inductiveness
///
/// Propagates the *violation* of the candidate backward along the back edge
/// and through one iteration of the loop body, restricting propagation to the
/// loop body nodes.  Checks that `candidate → (wp of NOT candidate after one
/// step)` is valid at the header, i.e. the invariant is preserved →
/// [`InvariantCheckResult::InductivenessFailed`] if not.
///
/// ## 3. Exit closure
///
/// For each loop exit edge whose successor has a non-trivial entry in
/// `assertion_postconditions`, checks that `candidate` implies the
/// postcondition at the exit.  Pass `&BTreeMap::new()` to skip this check
/// (e.g., when generating invariants for interprocedural summaries where the
/// authoritative check is done by a subsequent `analyze_with_tables` call).
///
/// Inner loop invariants (`inner`) are injected at their respective headers
/// during the backward-state propagations so that nested loop bodies are
/// correctly summarised.
pub fn check_loop_invariant_verbose(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    candidate: &Formula,
    oracle: &Oracle,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
) -> InvariantCheckResult {
    let candidate = normalize_candidate(cfg, info.header, candidate);

    // Initiation: the candidate must hold the first time the loop header is
    // entered.  We compute a forward over-approximation of the reach at the
    // loop header (SP from the function entry through the acyclic skeleton with
    // all back edges excluded, augmented with concrete store facts from the
    // preheader).  The store facts are added as `select(region, k) = value`
    // equations so the solver can determine initiation without needing to track
    // functional memory expressions across the SMT boundary.
    //
    // This replaces the previous approach of propagating `NOT candidate`
    // backward from the header with all back edges excluded globally.  That
    // backward approach under-approximated reachability for later loops in
    // multi-loop functions (earlier loops were forced to their 0-iteration exit
    // path), which allowed absurd candidates like `!(i < length)` to pass
    // initiation for loop 3 when loop 1 and 2 had already exited.
    let reach_h = forward_reach_at_header(cfg, info.header, inner);
    let initiation_violation = Formula::and(reach_h, Formula::not(candidate.clone()));
    match oracle.feasibility(&initiation_violation) {
        Ok(crate::common::oracle::Feasibility::Feasible) => {
            return InvariantCheckResult::InitiationFailed;
        }
        Ok(crate::common::oracle::Feasibility::Unknown) | Err(_) => {
            return InvariantCheckResult::InitiationFailed;
        }
        Ok(crate::common::oracle::Feasibility::Infeasible) => {}
    }

    // Inductiveness and exit-closure checks restrict propagation to the loop
    // body and exclude all back edges to prevent cycles within the body.
    let excluded: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();

    let Some(back_edge_requirement) = edge_source_requirement(cfg, info.back_edge, &candidate)
    else {
        return InvariantCheckResult::InductivenessFailed;
    };
    let Some(inductive_states) = backward_states(
        cfg,
        &[(info.latch, back_edge_requirement)],
        &excluded,
        Some(&info.body),
        true,
        inner,
        true,
    ) else {
        return InvariantCheckResult::InductivenessFailed;
    };
    let inductive_header = inductive_states
        .get(&info.header)
        .cloned()
        .unwrap_or(Formula::False);
    match oracle.implies(&candidate, &inductive_header) {
        Ok(Validity::Valid) => {}
        Ok(Validity::Invalid) => return InvariantCheckResult::InductivenessFailed,
        Ok(Validity::Unknown) | Err(_) => return InvariantCheckResult::InductivenessFailed,
    }

    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        let Some(exit_requirement) = edge_source_requirement(cfg, *exit_edge, postcondition) else {
            return InvariantCheckResult::ExitClosureFailed {
                exit_edge: *exit_edge,
            };
        };
        let Some(exit_states) = backward_states(
            cfg,
            &[(edge.source, exit_requirement)],
            &excluded,
            Some(&info.body),
            true,
            inner,
            false,
        ) else {
            return InvariantCheckResult::ExitClosureFailed {
                exit_edge: *exit_edge,
            };
        };
        let exit_header = exit_states
            .get(&info.header)
            .cloned()
            .unwrap_or(Formula::False);
        log::trace!(
            target: "loop_invariant",
            "exit closure: candidate={} postcondition={} exit_header={}",
            crate::may_must_analysis::backward::pretty_formula(&candidate),
            crate::may_must_analysis::backward::pretty_formula(postcondition),
            crate::may_must_analysis::backward::pretty_formula(&exit_header),
        );
        // Exit closure: the invariant must be INCONSISTENT with the violation condition
        // at the exit. "I AND exit_header infeasible" means "if I holds, no violation
        // can reach the assertion through this exit" — the correct safety criterion.
        // (The old oracle.implies check tested I ⊢ violation, which is backwards.)
        let combined = Formula::and(candidate.clone(), exit_header.clone());
        match oracle.feasibility(&combined) {
            Ok(crate::common::oracle::Feasibility::Infeasible) => {}
            Ok(crate::common::oracle::Feasibility::Feasible)
            | Ok(crate::common::oracle::Feasibility::Unknown)
            | Err(_) => {
                return InvariantCheckResult::ExitClosureFailed {
                    exit_edge: *exit_edge,
                };
            }
        }
    }

    InvariantCheckResult::Accepted
}

fn emit_counter_bounds(
    candidates: &mut Vec<Formula>,
    defs: &BTreeMap<String, AssignValue>,
    formula: &Formula,
) {
    let Some((counter, bound)) = extract_counter_bound(formula) else {
        return;
    };
    let lower = Formula::ge(counter.clone(), Term::int(0));
    let upper = Formula::le(counter.clone(), bound);
    push_candidate(candidates, defs, lower.clone());
    push_candidate(candidates, defs, upper.clone());
    push_candidate(candidates, defs, Formula::and(lower, upper));
}

/// For a comparison predicate, generate all 5 operator variants with the same LHS and RHS.
///
/// When the loop body computes a comparison like `array[j] <= menor`, the invariant
/// might require a different operator (`>=`) on the same operands.  Emitting all
/// variants ensures the invariant search is not limited by which operator happened
/// to appear in the source.
fn push_comparison_variants(
    candidates: &mut Vec<Formula>,
    defs: &BTreeMap<String, AssignValue>,
    predicate: &Formula,
) {
    let (lhs, rhs) = match predicate {
        Formula::Lt(l, r)
        | Formula::Le(l, r)
        | Formula::Gt(l, r)
        | Formula::Ge(l, r)
        | Formula::Eq(l, r) => (l.clone(), r.clone()),
        _ => return,
    };
    push_candidate(candidates, defs, Formula::lt(lhs.clone(), rhs.clone()));
    push_candidate(candidates, defs, Formula::le(lhs.clone(), rhs.clone()));
    push_candidate(candidates, defs, Formula::gt(lhs.clone(), rhs.clone()));
    push_candidate(candidates, defs, Formula::ge(lhs.clone(), rhs.clone()));
    push_candidate(candidates, defs, Formula::eq(lhs, rhs));
}

fn push_nontrivial(candidates: &mut Vec<Formula>, formula: Formula) {
    if formula == Formula::True || formula == Formula::False {
        return;
    }
    // Skip tautological implications a => a (generated when a bool variable is substituted
    // with its defining predicate by normalize_formula_with_defs).
    if let Formula::Implies(lhs, rhs) = &formula {
        if lhs == rhs {
            return;
        }
    }
    if !candidates.contains(&formula) {
        candidates.push(formula);
    }
}

fn push_candidate(
    candidates: &mut Vec<Formula>,
    defs: &BTreeMap<String, AssignValue>,
    formula: Formula,
) {
    push_nontrivial(candidates, normalize_formula_with_defs(&formula, defs));
}

fn extract_counter_bound(formula: &Formula) -> Option<(Term, Term)> {
    match formula {
        Formula::Lt(counter, bound) | Formula::Le(counter, bound) => {
            matches_int_counter(counter, bound)
        }
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Ge(counter, bound) => matches_int_counter(counter, bound),
            _ => None,
        },
        _ => None,
    }
}

fn matches_int_counter(counter: &Term, bound: &Term) -> Option<(Term, Term)> {
    if !matches!(counter, Term::Var(var) if var.sort() == Sort::Int) {
        return None;
    }
    if bound.sort().ok()? != Sort::Int {
        return None;
    }
    Some((counter.clone(), bound.clone()))
}

fn is_self_increment(target: &Var, term: &Term) -> bool {
    match term {
        Term::Add(lhs, rhs) => {
            matches_same_var(lhs, target) && matches!(rhs.as_ref(), Term::Int(_))
                || matches_same_var(rhs, target) && matches!(lhs.as_ref(), Term::Int(_))
        }
        Term::Sub(lhs, rhs) => {
            matches_same_var(lhs, target) && matches!(rhs.as_ref(), Term::Int(_))
        }
        _ => false,
    }
}

fn matches_same_var(term: &Term, target: &Var) -> bool {
    matches!(term, Term::Var(var) if var == target)
}

fn collect_loop_definitions(info: &LoopInfo, cfg: &AbstractCfg) -> BTreeMap<String, AssignValue> {
    let mut defs = BTreeMap::new();
    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        for effect in &node.transfer.effects {
            if let TransferEffect::Assign { target, value } = effect {
                let recursive = match value {
                    AssignValue::Term(term) => term_mentions_var(term, target.name()),
                    AssignValue::Predicate(formula) => formula_mentions_var(formula, target.name()),
                };
                if !recursive {
                    defs.insert(target.name().to_string(), value.clone());
                }
            }
        }
    }
    defs
}

fn normalize_formula_with_defs(formula: &Formula, defs: &BTreeMap<String, AssignValue>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => {
            if let Some(AssignValue::Predicate(predicate)) = defs.get(var.name()) {
                normalize_formula_with_defs(predicate, defs)
            } else {
                Formula::Var(var.clone())
            }
        }
        Formula::Not(inner) => Formula::not(normalize_formula_with_defs(inner, defs)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| normalize_formula_with_defs(item, defs))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| normalize_formula_with_defs(item, defs))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            normalize_formula_with_defs(lhs, defs),
            normalize_formula_with_defs(rhs, defs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(lhs.clone(), rhs.clone()),
        Formula::Lt(lhs, rhs) => Formula::lt(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
    }
}

fn normalize_term_with_defs(term: &Term, defs: &BTreeMap<String, AssignValue>) -> Term {
    match term {
        Term::Var(var) => {
            if let Some(AssignValue::Term(value)) = defs.get(var.name()) {
                normalize_term_with_defs(value, defs)
            } else {
                Term::Var(var.clone())
            }
        }
        Term::Int(value) => Term::int(*value),
        Term::Real(value) => Term::real(*value),
        Term::BoolToInt(inner) => Term::bool_to_int(normalize_formula_with_defs(inner, defs)),
        Term::Select(memory, index) => Term::select(
            memory.as_ref().clone(),
            normalize_term_with_defs(index, defs),
        ),
        Term::Add(lhs, rhs) => Term::add(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Term::Div(lhs, rhs) => Term::div(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Term::Rem(lhs, rhs) => Term::rem(
            normalize_term_with_defs(lhs, defs),
            normalize_term_with_defs(rhs, defs),
        ),
        Term::Neg(inner) => Term::neg(normalize_term_with_defs(inner, defs)),
    }
}

fn formula_mentions_var(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::True | Formula::False => false,
        Formula::Var(var) => var.name() == name,
        Formula::Not(inner) => formula_mentions_var(inner, name),
        Formula::And(items) | Formula::Or(items) => {
            items.iter().any(|item| formula_mentions_var(item, name))
        }
        Formula::Implies(lhs, rhs) => {
            formula_mentions_var(lhs, name) || formula_mentions_var(rhs, name)
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => term_mentions_var(lhs, name) || term_mentions_var(rhs, name),
        Formula::MemoryEq(_, _) => false,
    }
}

fn term_mentions_var(term: &Term, name: &str) -> bool {
    match term {
        Term::Var(var) => var.name() == name,
        Term::Int(_) | Term::Real(_) => false,
        Term::BoolToInt(inner) => formula_mentions_var(inner, name),
        Term::Select(_, index) => term_mentions_var(index, name),
        Term::Add(lhs, rhs)
        | Term::Sub(lhs, rhs)
        | Term::Mul(lhs, rhs)
        | Term::Div(lhs, rhs)
        | Term::Rem(lhs, rhs) => term_mentions_var(lhs, name) || term_mentions_var(rhs, name),
        Term::Neg(inner) => term_mentions_var(inner, name),
    }
}

fn collect_int_constants(formula: &Formula) -> Vec<i64> {
    let mut constants = Vec::new();
    collect_int_constants_formula(formula, &mut constants);
    constants
}

fn collect_int_constants_formula(formula: &Formula, out: &mut Vec<i64>) {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => {}
        Formula::Not(inner) => collect_int_constants_formula(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_int_constants_formula(item, out);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_int_constants_formula(lhs, out);
            collect_int_constants_formula(rhs, out);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_int_constants_term(lhs, out);
            collect_int_constants_term(rhs, out);
        }
        Formula::MemoryEq(_, _) => {}
    }
}

fn collect_int_constants_term(term: &Term, out: &mut Vec<i64>) {
    match term {
        Term::Int(value) => out.push(*value),
        Term::Var(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_int_constants_formula(inner, out),
        Term::Select(_, index) => collect_int_constants_term(index, out),
        Term::Add(lhs, rhs)
        | Term::Sub(lhs, rhs)
        | Term::Mul(lhs, rhs)
        | Term::Div(lhs, rhs)
        | Term::Rem(lhs, rhs) => {
            collect_int_constants_term(lhs, out);
            collect_int_constants_term(rhs, out);
        }
        Term::Neg(inner) => collect_int_constants_term(inner, out),
    }
}

/// Compute a forward over-approximation of states at `header` on first entry.
///
/// Propagates SP (strongest postcondition) from the function entry through the
/// acyclic CFG skeleton (all back edges excluded).  At inner/sibling loop
/// headers that already have accepted invariants (from `inner`), the invariant
/// is OR-seeded into the initial reach so that the code following those loops
/// is not widened to `True`.
///
/// The result `R` satisfies: every state actually reachable at `header` on
/// first entry (i.e. via a path that does not use `info.back_edge`) is a model
/// of `R`.  This makes it suitable for the initiation check
/// `R ∧ ¬candidate` infeasible ⟹ candidate holds at first entry.
///
/// # Approximation note
///
/// Sibling loops whose back edges are excluded contribute only their
/// 0-iteration path to the reach, which is an under-approximation for variables
/// the sibling loop modifies.  Seeding sibling headers with their invariants
/// partially compensates: it adds the invariant as an additional OR-branch at
/// the header, so subsequent code can propagate from a state where the invariant
/// holds.  Variables that are unconditionally overwritten by the preheader code
/// between the sibling loop and the current loop are unaffected by this
/// approximation in practice.
/// Concrete store facts accumulated during the forward SP pass.
/// Maps `(region_name, constant_offset)` to the value last stored there.
type StoreFacts = BTreeMap<(String, i64), Term>;

/// Intersect two `StoreFacts` maps, keeping only entries that agree on value.
fn intersect_store_facts(a: StoreFacts, b: StoreFacts) -> StoreFacts {
    a.into_iter().filter(|(k, v)| b.get(k) == Some(v)).collect()
}

/// Resolve any `Select(Var(region), Int(k))` sub-terms using concrete store facts.
/// Other term shapes are returned unchanged.
fn resolve_select_in_term(term: &Term, facts: &StoreFacts) -> Term {
    match term {
        Term::Select(memory, index) => {
            if let Memory::Var(region) = memory.as_ref() {
                if let Some(k) = index.try_as_constant_int() {
                    if let Some(v) = facts.get(&(region.clone(), k)) {
                        return v.clone();
                    }
                }
            }
            term.clone()
        }
        Term::Add(l, r) => Term::add(
            resolve_select_in_term(l, facts),
            resolve_select_in_term(r, facts),
        ),
        Term::Sub(l, r) => Term::sub(
            resolve_select_in_term(l, facts),
            resolve_select_in_term(r, facts),
        ),
        Term::Mul(l, r) => Term::mul(
            resolve_select_in_term(l, facts),
            resolve_select_in_term(r, facts),
        ),
        Term::Div(l, r) => Term::div(
            resolve_select_in_term(l, facts),
            resolve_select_in_term(r, facts),
        ),
        Term::Rem(l, r) => Term::rem(
            resolve_select_in_term(l, facts),
            resolve_select_in_term(r, facts),
        ),
        Term::Neg(inner) => Term::neg(resolve_select_in_term(inner, facts)),
        Term::BoolToInt(_) | Term::Var(_) | Term::Int(_) | Term::Real(_) => term.clone(),
    }
}

/// SP forward pass over a slice of effects, updating both the formula and the
/// store-facts map.  `MemoryStore` effects with a constant offset are recorded
/// in `facts` (rather than dropped as the default `sp_one` does), and
/// subsequent `Assign { Select(...) }` effects resolve the load against the
/// recorded facts, so the caller sees e.g. `cur = 0` rather than
/// `cur = select(stack0, 0)` when the preheader contains `store 0, ptr %i`.
fn apply_effects_sp(effects: &[TransferEffect], pre: &Formula, facts: &mut StoreFacts) -> Formula {
    let mut formula = pre.clone();
    for effect in effects {
        match effect {
            TransferEffect::MemoryStore {
                region,
                offset,
                value,
            } => {
                match offset.try_as_constant_int() {
                    Some(k) => {
                        let resolved = resolve_select_in_term(value, facts);
                        facts.insert((region.clone(), k), resolved);
                    }
                    None => {
                        facts.retain(|(r, _), _| r != region);
                    }
                }
                // MemoryStore itself does not add to the formula; loads will resolve via facts.
            }
            TransferEffect::HavocRegions { regions } => {
                for r in regions {
                    facts.retain(|(rk, _), _| rk != r);
                }
            }
            TransferEffect::Call { memory_effect, .. }
            | TransferEffect::IndirectCall { memory_effect, .. } => {
                if matches!(memory_effect, CallMemoryEffect::HavocMemory) {
                    facts.clear();
                }
                // Call itself is transparent in SP (no formula change beyond memory havocing).
            }
            TransferEffect::Assign {
                target,
                value: AssignValue::Term(term),
            } => {
                let resolved = resolve_select_in_term(term, facts);
                formula = Formula::and(formula, Formula::eq(Term::Var(target.clone()), resolved));
            }
            TransferEffect::Assign {
                target,
                value: AssignValue::Predicate(pred),
            } => {
                formula = Formula::and(
                    formula,
                    Formula::and(
                        Formula::implies(Formula::Var(target.clone()), pred.clone()),
                        Formula::implies(pred.clone(), Formula::Var(target.clone())),
                    ),
                );
            }
            TransferEffect::Assume(c)
            | TransferEffect::TypeBound(c)
            | TransferEffect::Obligation(c) => {
                formula = Formula::and(formula, c.clone());
            }
            // All other effects (Nop, Alloca, GEP, PointerLoad/Store/Alias, etc.)
            // are transparent in the forward SP.
            _ => {}
        }
    }
    formula
}

fn forward_reach_at_header(
    cfg: &AbstractCfg,
    header: CfgNodeId,
    inner: InnerInvariants<'_>,
) -> Formula {
    let all_back_edges: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();
    let Some(order) = cfg.topological_order_excluding(&all_back_edges) else {
        // CFG has an unexpected cycle; return True (vacuously accepting) so
        // the caller falls back to InductivenessFailed rather than accepting
        // an uninspected candidate.
        return Formula::True;
    };

    let inner_map: BTreeMap<CfgNodeId, &Formula> = inner.iter().map(|(h, inv)| (*h, inv)).collect();

    // reach[node] = SP formula at node's input (before the node's own effects).
    let mut reach: BTreeMap<CfgNodeId, Formula> =
        cfg.node_ids().map(|id| (id, Formula::False)).collect();
    reach.insert(cfg.entry(), Formula::True);

    // node_in_facts[node] = concrete store facts at node's INPUT (before its effects),
    // computed as the intersection of facts along all incoming non-back-edge paths.
    let mut node_in_facts: BTreeMap<CfgNodeId, StoreFacts> = BTreeMap::new();
    node_in_facts.insert(cfg.entry(), StoreFacts::new());

    // Seed inner/sibling loop headers: OR their invariant into the initial
    // state so that downstream code can reason from a state where the
    // invariant holds, not only from the 0-iteration path.
    for (&h, &inv) in &inner_map {
        let e = reach.entry(h).or_insert(Formula::False);
        *e = Formula::or(e.clone(), inv.clone());
    }

    for &node in &order {
        // Accumulated intersection of store facts from all active incoming paths.
        let mut incoming_facts: Option<StoreFacts> = None;

        for edge_id in cfg.incoming_edges(node) {
            if all_back_edges.contains(&edge_id) {
                continue;
            }
            let Ok(edge) = cfg.edge(edge_id) else {
                continue;
            };
            let source_reach = reach.get(&edge.source).cloned().unwrap_or(Formula::False);
            if source_reach == Formula::False {
                continue;
            }
            let Ok(source_node) = cfg.node(edge.source) else {
                continue;
            };

            // Start from the store facts at the source node's INPUT.
            let source_in = node_in_facts.get(&edge.source).cloned().unwrap_or_default();

            // Apply source-node effects: updates both formula and path_facts.
            let mut path_facts = source_in;
            let source_out = apply_effects_sp(
                &source_node.transfer.effects,
                &source_reach,
                &mut path_facts,
            );

            // Apply edge guard, then edge effects (phi assignments etc.).
            let guarded = Formula::and(source_out, edge.guard.clone());
            let through_edge = apply_effects_sp(&edge.effects, &guarded, &mut path_facts);

            // OR the formula contribution into this node's reach.
            let existing = reach.get(&node).cloned().unwrap_or(Formula::False);
            reach.insert(node, Formula::or(existing, through_edge));

            // Intersect the path facts into the incoming_facts accumulator:
            // at a join point we can only assert facts that hold on ALL incoming paths.
            incoming_facts = Some(match incoming_facts {
                None => path_facts,
                Some(prev) => intersect_store_facts(prev, path_facts),
            });
        }

        // Record the merged incoming facts for this node so successors can use them.
        if let Some(facts) = incoming_facts {
            node_in_facts.insert(node, facts);
        }
    }

    // Return the reach at the HEADER OUTPUT (after the header's own effects).
    // The initiation check in check_loop_invariant_verbose uses the unnormalized
    // Candidates are normalized into header-input variable space by
    // normalize_formula_with_defs (which substitutes header loads with
    // select(region, k) terms).  So we return the header-INPUT formula augmented
    // with store facts expressed as select(region, k) = value equations.  This
    // puts the reach and the candidate in the same variable space so the solver
    // can check initiation correctly.
    let header_in = reach.get(&header).cloned().unwrap_or(Formula::True);
    let header_in_facts = node_in_facts.get(&header).cloned().unwrap_or_default();
    header_in_facts
        .iter()
        .fold(header_in, |f, ((region, offset), value)| {
            let select_term = Term::select(Memory::var(region.clone()), Term::int(*offset));
            Formula::and(f, Formula::eq(select_term, value.clone()))
        })
}

/// Propagate a set of seed formulas backward through the CFG and return the
/// resulting per-node state map.
///
/// Back edges in `excluded_edges` are skipped, allowing the computation to
/// proceed in topological order.  `restrict_to`, when set, limits propagation
/// to edges whose both endpoints are in the specified node set (used for
/// intra-loop analysis).  `ignore_body_guards` suppresses edge guards during
/// WP computation (used for the inductiveness check where we want to know the
/// weakest precondition unconditionally inside the body).
///
/// Inner loop headers supplied in `inner` are seeded with their invariants and
/// the corresponding inner body nodes are skipped so that their transfer
/// effects are not double-counted.
///
/// # Parameters
///
/// * `seeds` — initial state at given nodes (e.g., violation conditions).
/// * `excluded_edges` — back edges to skip (enables topological propagation).
/// * `restrict_to` — limit to edges within a subgraph (intra-loop analysis).
/// * `ignore_body_guards` — suppress guards (unconditional WP for inductiveness).
/// * `inner` — inner loop invariants (summarise their bodies).
fn backward_states(
    cfg: &AbstractCfg,
    seeds: &[(CfgNodeId, Formula)],
    excluded_edges: &BTreeSet<CfgEdgeId>,
    restrict_to: Option<&BTreeSet<CfgNodeId>>,
    ignore_body_guards: bool,
    inner: InnerInvariants<'_>,
    inductive_assume: bool,
) -> Option<BTreeMap<CfgNodeId, Formula>> {
    let order = cfg.topological_order_excluding(excluded_edges)?;
    let mut states = cfg
        .node_ids()
        .map(|id| (id, Formula::False))
        .collect::<BTreeMap<_, _>>();
    for (node, formula) in seeds {
        let entry = states.entry(*node).or_insert(Formula::False);
        *entry = Formula::or(entry.clone(), formula.clone());
    }
    let (inner_headers, summarized_inner_nodes) = summarize_inner_loops(cfg, restrict_to, inner);
    for (header, invariant) in &inner_headers {
        let state = states.entry(*header).or_insert(Formula::False);
        *state = Formula::or(state.clone(), invariant.clone());
    }

    for node in order.iter().rev() {
        if summarized_inner_nodes.contains(node) {
            continue;
        }
        for edge_id in cfg.incoming_edges(*node) {
            if excluded_edges.contains(&edge_id) {
                continue;
            }
            let edge = cfg.edge(edge_id).ok()?;
            if let Some(body) = restrict_to {
                if !body.contains(&edge.source) || !body.contains(&edge.target) {
                    continue;
                }
            }
            if summarized_inner_nodes.contains(&edge.source)
                || summarized_inner_nodes.contains(&edge.target)
            {
                continue;
            }
            let target_state = states.get(&edge.target).cloned().unwrap_or(Formula::False);
            let edge_pre = edge.transfer().wp(&target_state);
            let guard = if ignore_body_guards {
                Formula::True
            } else {
                edge.guard.clone()
            };
            let post_at_source = Formula::and(guard, edge_pre);
            let pre_at_source = if inductive_assume {
                cfg.node(edge.source)
                    .ok()?
                    .transfer
                    .wp_inductive(&post_at_source)
            } else {
                cfg.node(edge.source).ok()?.transfer.wp(&post_at_source)
            };
            let existing = states.get(&edge.source).cloned().unwrap_or(Formula::False);
            states.insert(edge.source, Formula::or(existing, pre_at_source));
        }
    }

    Some(states)
}

fn edge_source_requirement(
    cfg: &AbstractCfg,
    edge_id: CfgEdgeId,
    target: &Formula,
) -> Option<Formula> {
    let edge = cfg.edge(edge_id).ok()?;
    let edge_pre = edge.transfer().wp(target);
    let post_at_source = Formula::and(edge.guard.clone(), edge_pre);
    Some(cfg.node(edge.source).ok()?.transfer.wp(&post_at_source))
}

fn summarize_inner_loops(
    cfg: &AbstractCfg,
    restrict_to: Option<&BTreeSet<CfgNodeId>>,
    inner: InnerInvariants<'_>,
) -> (BTreeMap<CfgNodeId, Formula>, BTreeSet<CfgNodeId>) {
    let Some(body) = restrict_to else {
        return (BTreeMap::new(), BTreeSet::new());
    };
    let loop_bodies = detect_loops(cfg)
        .into_iter()
        .map(|info| (info.header, info.body))
        .collect::<BTreeMap<_, _>>();
    let mut headers = BTreeMap::new();
    let mut blocked_nodes = BTreeSet::new();
    for (header, invariant) in inner {
        if !body.contains(header) {
            continue;
        }
        headers.insert(*header, invariant.clone());
        if let Some(inner_body) = loop_bodies.get(header) {
            for node in inner_body {
                if node != header {
                    blocked_nodes.insert(*node);
                }
            }
        }
    }
    (headers, blocked_nodes)
}

/// Collect all integer literal constants from the loop body.
///
/// Scans all assignment targets and memory stores for integer literals, which
/// Collect the memory regions and scalar variable names written by the loop body.
///
/// Returns two sets:
/// - `regions`: every `MemoryStore { region }` target inside the loop body.
/// - `vars`: every `Assign { target }` scalar variable name written inside the loop body.
///
/// Both node-level effects and edge-level phi-assignment effects between body nodes are
/// included.  Used by the loop-relevance pre-filter in `precomputed_satisfy_exit_closure`
/// to decide whether a loop can possibly affect a given exit postcondition.
pub fn loop_write_regions_and_vars(
    info: &LoopInfo,
    cfg: &AbstractCfg,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut regions = BTreeSet::new();
    let mut vars = BTreeSet::new();

    let collect = |effects: &[TransferEffect],
                   regions: &mut BTreeSet<String>,
                   vars: &mut BTreeSet<String>| {
        for effect in effects {
            match effect {
                TransferEffect::MemoryStore { region, .. } => {
                    regions.insert(region.clone());
                }
                TransferEffect::Assign { target, .. } => {
                    vars.insert(target.name().to_string());
                }
                _ => {}
            }
        }
    };

    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        collect(&node.transfer.effects, &mut regions, &mut vars);
        // Also collect phi-node assignments on edges between body nodes.
        for edge_id in cfg.outgoing_edges(*node_id) {
            let Ok(edge) = cfg.edge(edge_id) else {
                continue;
            };
            if info.body.contains(&edge.target) {
                collect(&edge.effects, &mut regions, &mut vars);
            }
        }
    }
    (regions, vars)
}

/// Generate invariant candidates of the form `counter == init || safety`.
///
/// When the preheader stores a constant to a scalar region (e.g. `j = 0`) and the
/// assertion violation at loop exit implies a safety condition (e.g. `array[0] >= menor`),
/// the combined candidate `select(j_region, 0) == 0 || array[0] >= menor` captures
/// invariants that neither the algorithmic nor Houdini phases generate.
///
/// Two candidate sets are generated:
/// 1. **Direct**: `counter == init || NOT(violation_at_exit_target)` — uses the assertion
///    violation formula directly without backward-propagating through the loop body.  This
///    avoids loop-path conditions that inflate the formula and defeat inductiveness.
/// 2. **Propagated**: `counter == init || NOT(exit_header)` — uses the violation condition
///    backward-propagated to the header.  Included as a fallback when the direct form
///    is too weak.
pub fn entry_safety_candidates(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
) -> Vec<Formula> {
    let store_facts = preheader_store_facts_at_header(cfg, info.header, inner);
    if store_facts.is_empty() {
        return vec![];
    }

    // Collect direct violations from exit targets without backward propagation.
    let mut direct_violations = Vec::new();
    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        direct_violations.push(postcondition.clone());
    }

    let mut candidates = Vec::new();

    // Conjunction of all initial scalar store facts (e.g. `j == 0 AND SIZE == 1`).
    // This guards the first disjunct so the exit closure can rule out SIZE == 0 etc.
    let all_scalar_eqs: Vec<Formula> = store_facts
        .iter()
        .filter(|((_, offset), _)| *offset == 0)
        .map(|((region, offset), value)| {
            Formula::eq(
                Term::select(Memory::var(region.clone()), Term::int(*offset)),
                value.clone(),
            )
        })
        .collect();

    if !direct_violations.is_empty() {
        let direct_safety = Formula::not(Formula::or_all(direct_violations));
        // Combined guard: (ALL initial scalar facts) || safety
        if !all_scalar_eqs.is_empty() {
            push_nontrivial(
                &mut candidates,
                Formula::or(
                    Formula::and_all(all_scalar_eqs.clone()),
                    direct_safety.clone(),
                ),
            );
        }
        // Also individual: counter == init || safety (fallback for multi-counter loops)
        for ((region, offset), value) in &store_facts {
            if *offset != 0 {
                continue;
            }
            let counter_eq = Formula::eq(
                Term::select(Memory::var(region.clone()), Term::int(*offset)),
                value.clone(),
            );
            push_nontrivial(
                &mut candidates,
                Formula::or(counter_eq, direct_safety.clone()),
            );
        }
    }

    // Also try the backward-propagated version as a fallback.
    if let Some(exit_violation) =
        exit_violation_at_header(info, cfg, assertion_postconditions, inner)
    {
        let safety = Formula::not(exit_violation);
        if !all_scalar_eqs.is_empty() {
            push_nontrivial(
                &mut candidates,
                Formula::or(Formula::and_all(all_scalar_eqs), safety.clone()),
            );
        }
        for ((region, offset), value) in &store_facts {
            if *offset != 0 {
                continue;
            }
            let counter_eq = Formula::eq(
                Term::select(Memory::var(region.clone()), Term::int(*offset)),
                value.clone(),
            );
            push_nontrivial(&mut candidates, Formula::or(counter_eq, safety.clone()));
        }
    }

    candidates
}

/// Compute the violation condition at the loop header by backward propagation from exit edges.
///
/// Returns `None` if there are no exit postconditions or if propagation fails.
fn exit_violation_at_header(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
) -> Option<Formula> {
    let excluded: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();
    let mut header_violations = Vec::new();
    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        let Some(exit_requirement) = edge_source_requirement(cfg, *exit_edge, postcondition) else {
            continue;
        };
        let Some(exit_states) = backward_states(
            cfg,
            &[(edge.source, exit_requirement)],
            &excluded,
            Some(&info.body),
            true,
            inner,
            false,
        ) else {
            continue;
        };
        let exit_header = exit_states
            .get(&info.header)
            .cloned()
            .unwrap_or(Formula::False);
        if exit_header != Formula::False {
            header_violations.push(exit_header);
        }
    }
    if header_violations.is_empty() {
        return None;
    }
    Some(Formula::or_all(header_violations))
}

/// Return store facts that hold at the loop header on first entry.
///
/// Runs the same forward SP pass as [`forward_reach_at_header`] but returns
/// the accumulated concrete store facts at the header rather than the formula.
fn preheader_store_facts_at_header(
    cfg: &AbstractCfg,
    header: CfgNodeId,
    inner: InnerInvariants<'_>,
) -> StoreFacts {
    let all_back_edges: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();
    let Some(order) = cfg.topological_order_excluding(&all_back_edges) else {
        return StoreFacts::new();
    };
    let inner_map: BTreeMap<CfgNodeId, &Formula> = inner.iter().map(|(h, inv)| (*h, inv)).collect();
    let mut reach: BTreeMap<CfgNodeId, Formula> =
        cfg.node_ids().map(|id| (id, Formula::False)).collect();
    reach.insert(cfg.entry(), Formula::True);
    let mut node_in_facts: BTreeMap<CfgNodeId, StoreFacts> = BTreeMap::new();
    node_in_facts.insert(cfg.entry(), StoreFacts::new());
    for (&h, &inv) in &inner_map {
        let e = reach.entry(h).or_insert(Formula::False);
        *e = Formula::or(e.clone(), inv.clone());
    }
    for &node in &order {
        if node == header {
            // We want the IN-facts at the header; stop processing before the header's own effects.
            break;
        }
        let mut incoming_facts: Option<StoreFacts> = None;
        for edge_id in cfg.incoming_edges(node) {
            if all_back_edges.contains(&edge_id) {
                continue;
            }
            let Ok(edge) = cfg.edge(edge_id) else {
                continue;
            };
            let source_reach = reach.get(&edge.source).cloned().unwrap_or(Formula::False);
            if source_reach == Formula::False {
                continue;
            }
            let Ok(source_node) = cfg.node(edge.source) else {
                continue;
            };
            let source_in = node_in_facts.get(&edge.source).cloned().unwrap_or_default();
            let mut path_facts = source_in;
            let source_out = apply_effects_sp(
                &source_node.transfer.effects,
                &source_reach,
                &mut path_facts,
            );
            let guarded = Formula::and(source_out, edge.guard.clone());
            let through_edge = apply_effects_sp(&edge.effects, &guarded, &mut path_facts);
            let existing = reach.get(&node).cloned().unwrap_or(Formula::False);
            reach.insert(node, Formula::or(existing, through_edge));
            incoming_facts = Some(match incoming_facts {
                None => path_facts,
                Some(prev) => intersect_store_facts(prev, path_facts),
            });
        }
        if let Some(facts) = incoming_facts {
            node_in_facts.insert(node, facts);
        }
    }
    // Now collect facts that arrive at the header from its non-back predecessors.
    let mut header_incoming: Option<StoreFacts> = None;
    for edge_id in cfg.incoming_edges(header) {
        if all_back_edges.contains(&edge_id) {
            continue;
        }
        let Ok(edge) = cfg.edge(edge_id) else {
            continue;
        };
        let source_reach = reach.get(&edge.source).cloned().unwrap_or(Formula::False);
        if source_reach == Formula::False {
            continue;
        }
        let Ok(source_node) = cfg.node(edge.source) else {
            continue;
        };
        let source_in = node_in_facts.get(&edge.source).cloned().unwrap_or_default();
        let mut path_facts = source_in;
        apply_effects_sp(
            &source_node.transfer.effects,
            &source_reach,
            &mut path_facts,
        );
        apply_effects_sp(&edge.effects, &Formula::True, &mut path_facts);
        header_incoming = Some(match header_incoming {
            None => path_facts,
            Some(prev) => intersect_store_facts(prev, path_facts),
        });
    }
    header_incoming.unwrap_or_default()
}

/// are used by [`houdini_candidates`] to construct bound templates.
pub fn collect_loop_body_int_constants(info: &LoopInfo, cfg: &AbstractCfg) -> BTreeSet<i64> {
    let mut constants = BTreeSet::new();
    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        for effect in &node.transfer.effects {
            match effect {
                TransferEffect::Assign {
                    value: AssignValue::Term(Term::Int(value)),
                    ..
                }
                | TransferEffect::MemoryStore {
                    value: Term::Int(value),
                    ..
                } => {
                    constants.insert(*value);
                }
                _ => {}
            }
        }
    }
    constants
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AssignValue, TransferFn};

    #[test]
    fn algorithmic_candidates_include_counter_bounds() {
        let mut cfg = AbstractCfg::new("entry");
        let header = cfg.add_node("header", TransferFn::identity());
        let latch = cfg.add_node(
            "latch",
            TransferFn::new(vec![TransferEffect::Assign {
                target: Var::int("i"),
                value: AssignValue::Term(Term::add(Term::var("i", Sort::Int), Term::int(1))),
            }]),
        );
        let exit = cfg.add_node("exit", TransferFn::identity());
        cfg.add_edge(cfg.entry(), header, Formula::True, vec![])
            .unwrap();
        cfg.add_edge(
            header,
            latch,
            Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
            vec![],
        )
        .unwrap();
        let back_edge = cfg
            .add_edge(
                latch,
                header,
                Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
                vec![],
            )
            .unwrap();
        let exit_edge = cfg
            .add_edge(
                latch,
                exit,
                Formula::not(Formula::lt(
                    Term::var("i", Sort::Int),
                    Term::var("n", Sort::Int),
                )),
                vec![],
            )
            .unwrap();
        let info = LoopInfo {
            header,
            latch,
            back_edge,
            body: BTreeSet::from([header, latch]),
            exit_edges: vec![exit_edge],
            back_edge_guard: Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
            source_location: None,
        };

        let candidates = algorithmic_candidates(&info, &cfg);

        assert!(candidates.contains(&Formula::ge(Term::var("i", Sort::Int), Term::int(0))));
        assert!(candidates.contains(&Formula::le(
            Term::var("i", Sort::Int),
            Term::var("n", Sort::Int)
        )));
        assert!(candidates.contains(&Formula::and(
            Formula::ge(Term::var("i", Sort::Int), Term::int(0)),
            Formula::le(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
        )));
    }

    #[test]
    fn houdini_candidates_include_range_conjunctions() {
        let variable_sorts = BTreeMap::from([("i".to_string(), Sort::Int)]);
        let loop_constants = BTreeSet::from([5]);
        let candidates = houdini_candidates(&variable_sorts, &Formula::True, &loop_constants);
        assert!(candidates.contains(&Formula::and(
            Formula::ge(Term::var("i", Sort::Int), Term::int(0)),
            Formula::le(Term::var("i", Sort::Int), Term::int(5)),
        )));
    }
}
