//! Loop detection and loop-invariant verification.
//!
//! # Responsibilities
//!
//! 1. **Detection** — [`detect_loops`] identifies natural loops in the CFG by
//!    finding back edges and computing the corresponding loop bodies.
//!
//! 2. **Invariant checking** — [`check_loop_invariant_verbose`] performs the
//!    three-part soundness check for a candidate formula:
//!    - **Initiation**: the invariant holds on entry to the loop.
//!    - **Inductiveness**: the invariant is preserved by one loop iteration.
//!    - **Exit closure**: for each exit edge, `invariant ∧ exit_violation` is
//!      infeasible — the invariant cannot co-exist with a violation at any exit.
//!      **Never** skip exit closure and rely on `run_backward` to substitute for
//!      it: `run_backward` blocks back edges and cannot reason about loop-carried
//!      state, so an inductive-but-not-exit-closed invariant can produce a false
//!      `Verified` on an unsafe program.
//!
//! # Invariant strength
//!
//! Only one invariant strength is used:
//!
//! - **[`VerifiedLoopInvariant`]** — all three checks passed: initiation,
//!   inductiveness, AND exit closure.  The invariant is sufficient to discharge
//!   the specific assertion at the loop exits.  This is the only kind passed to
//!   `run_backward`.
//!
//! # Exit closure: current implementation
//!
//! The exit closure check in [`check_loop_invariant_verbose`] is a **one-step**
//! backward analysis: it propagates the bad condition backward from the exit edge
//! through the loop body (back edge excluded) and checks `I_h ∧ exit_header`
//! infeasible.  Combined with inductiveness, this is sound.
//!
//! # Nested loops
//!
//! Loops are processed innermost-first (see [`sort_innermost_first`]).  Already-
//! accepted inner invariants are passed as `inner: InnerInvariants` to
//! [`check_loop_invariant_verbose`] and to [`backward_states`] so that inner
//! loop bodies can be summarised without re-entering them.

#![allow(dead_code)]

use crate::cfg::{
    AbstractCfg, AssignValue, CallMemoryEffect, CfgEdgeId, CfgNodeId, SourceLocation,
    TransferEffect,
};
use crate::formula::{Formula, Memory, SmtModel, Sort, Term, Var};
use crate::smt::oracle::{Oracle, Validity};
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

pub type InnerInvariants<'a> = &'a [(CfgNodeId, Formula)];

/// A loop invariant that has passed all three soundness checks: initiation,
/// inductiveness, and exit closure.
///
/// This is the only invariant type that may be passed to `run_backward` as a
/// verdict-bearing invariant.  Produced by ACHAR synthesis in
/// [`synthesize_loop_invariants`] — never construct directly.
#[derive(Clone, Debug)]
pub struct VerifiedLoopInvariant {
    pub header: CfgNodeId,
    pub formula: Formula,
}

impl VerifiedLoopInvariant {
    pub fn new(header: CfgNodeId, formula: Formula) -> Self {
        Self { header, formula }
    }

    /// Convert to the `(header, formula)` pair format used by `InnerInvariants`.
    pub fn as_pair(&self) -> (CfgNodeId, Formula) {
        (self.header, self.formula.clone())
    }
}

/// Detailed outcome of [`check_loop_invariant_verbose`].
///
/// `Accepted` means all three checks (initiation, inductiveness, exit closure)
/// passed.  The caller wraps the formula into a [`VerifiedLoopInvariant`].
///
/// The failure variants identify *which* condition was the first to fail,
/// enabling targeted logging and CEGIS feedback.
///
/// Each failure variant carries an optional `witness` model — a concrete program
/// state that demonstrates *why* the check failed.  The ACHAR CEGIS loop uses
/// these witnesses to prune remaining candidates cheaply without further SMT calls.
///
/// - **InitiationFailed witness**: a reachable initial state where the candidate is false.
///   Use as a new positive ICE example (states where the invariant *must* hold).
/// - **InductivenessFailed witness**: a pre-state where the candidate holds but the
///   loop body takes execution outside it.  Use as an ICE implication example.
/// - **ExitClosureFailed witness**: a state where the candidate holds but a violation
///   is still reachable through the exit.  Use as a new negative ICE example.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InvariantCheckResult {
    /// All requested soundness checks passed (initiation + inductiveness +
    /// exit closure).  Synthesis wraps this into a [`VerifiedLoopInvariant`].
    Accepted,
    /// The candidate does not hold on entry to the loop.
    InitiationFailed { witness: Option<SmtModel> },
    /// The candidate is not preserved by one iteration of the loop body.
    InductivenessFailed { witness: Option<SmtModel> },
    /// The candidate does not imply the required postcondition at this exit.
    ExitClosureFailed {
        exit_edge: CfgEdgeId,
        witness: Option<SmtModel>,
    },
}

impl InvariantCheckResult {
    pub fn is_accepted(&self) -> bool {
        matches!(self, Self::Accepted)
    }

    pub fn witness(&self) -> Option<&SmtModel> {
        match self {
            Self::Accepted => None,
            Self::InitiationFailed { witness }
            | Self::InductivenessFailed { witness }
            | Self::ExitClosureFailed { witness, .. } => witness.as_ref(),
        }
    }
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
/// `assertion_postconditions`, checks that `candidate AND exit_header` is
/// infeasible — the invariant cannot simultaneously hold and allow a violation
/// to reach the assertion through the exit.
///
/// Pass `&BTreeMap::new()` to skip this check only for interprocedural
/// observer-summary inference where no assertion site is active.  In that case
/// the caller (`infer_cyclic_observer_summary`) subsequently calls
/// `analyze_with_tables` which performs the authoritative discharge.  Skipping
/// exit closure in assertion-verification context is unsound.
///
/// When `assertion_postconditions` is non-empty:
/// - `Accepted` means all three checks → **VerifiedLoopInvariant**, sufficient
///   to pass to `run_backward` as a verdict-bearing invariant.
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

    // Semantic contradiction guard: a candidate equivalent to False vacuously passes
    // all three checks because every conjunction with it is infeasible.  That produces
    // a spuriously accepted invariant that injects False into reach, forcing
    // reach ∧ state = False at entry and a false Verified verdict.
    // Reject before initiation so this path is unreachable.
    if oracle.is_contradiction(&candidate).unwrap_or(false) {
        return InvariantCheckResult::InitiationFailed { witness: None };
    }

    // Initiation: the candidate must hold the first time the loop header is
    // entered.  We compute a forward over-approximation of the reach at the
    // loop header (SP from the function entry through the acyclic skeleton with
    // all back edges excluded, augmented with concrete store facts from the
    // preheader).  The store facts are added as `select(region, k) = value`
    // equations so the solver can determine initiation without needing to track
    // functional memory expressions across the SMT boundary.
    let reach_h = forward_reach_at_header(cfg, info.header, inner);
    let initiation_violation = Formula::and(reach_h.clone(), Formula::not(candidate.clone()));
    match oracle.feasibility_with_model(&initiation_violation) {
        Ok(report) => match report.feasibility {
            crate::smt::oracle::Feasibility::Feasible => {
                return InvariantCheckResult::InitiationFailed {
                    witness: report.model,
                };
            }
            crate::smt::oracle::Feasibility::Unknown => {
                return InvariantCheckResult::InitiationFailed { witness: None };
            }
            crate::smt::oracle::Feasibility::Infeasible => {}
        },
        Err(_) => return InvariantCheckResult::InitiationFailed { witness: None },
    }

    // Vacuous-initiation guard: reject candidates that only pass initiation
    // because reach_h is False (loop header unreachable in the acyclic
    // skeleton) or because the candidate is never actually satisfied at any
    // reachable loop entry.  Both cases make reach_h ∧ candidate infeasible.
    // Accepting such a candidate injects False into reach, forcing
    // reach ∧ state = False at entry and producing a spurious Verified verdict.
    let reach_at_entry = Formula::and(reach_h, candidate.clone());
    match oracle.feasibility_with_model(&reach_at_entry) {
        Ok(report) if report.feasibility != crate::smt::oracle::Feasibility::Feasible => {
            return InvariantCheckResult::InitiationFailed { witness: None };
        }
        Err(_) => return InvariantCheckResult::InitiationFailed { witness: None },
        _ => {}
    }

    // Inductiveness and exit-closure checks restrict propagation to the loop
    // body and exclude all back edges to prevent cycles within the body.
    let excluded: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();

    let Some(back_edge_requirement) = edge_source_requirement(cfg, info.back_edge, &candidate)
    else {
        return InvariantCheckResult::InductivenessFailed { witness: None };
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
        return InvariantCheckResult::InductivenessFailed { witness: None };
    };
    let inductive_header = inductive_states
        .get(&info.header)
        .cloned()
        .unwrap_or(Formula::False);
    match oracle.implies_with_model(&candidate, &inductive_header) {
        Ok((Validity::Valid, _)) => {}
        Ok((Validity::Invalid, model)) => {
            return InvariantCheckResult::InductivenessFailed { witness: model }
        }
        Ok((Validity::Unknown, _)) | Err(_) => {
            return InvariantCheckResult::InductivenessFailed { witness: None }
        }
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
                witness: None,
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
                witness: None,
            };
        };
        let exit_header = exit_states
            .get(&info.header)
            .cloned()
            .unwrap_or(Formula::False);
        log::trace!(
            target: "loop_invariant",
            "exit closure: candidate={} postcondition={} exit_header={}",
            crate::analysis::backward::pretty_formula(&candidate),
            crate::analysis::backward::pretty_formula(postcondition),
            crate::analysis::backward::pretty_formula(&exit_header),
        );
        // Exit closure: the invariant must be INCONSISTENT with the violation condition
        // at the exit. "I AND exit_header infeasible" means "if I holds, no violation
        // can reach the assertion through this exit" — the correct safety criterion.
        let combined = Formula::and(candidate.clone(), exit_header.clone());
        match oracle.feasibility_with_model(&combined) {
            Ok(report) => match report.feasibility {
                crate::smt::oracle::Feasibility::Infeasible => {}
                crate::smt::oracle::Feasibility::Feasible
                | crate::smt::oracle::Feasibility::Unknown => {
                    return InvariantCheckResult::ExitClosureFailed {
                        exit_edge: *exit_edge,
                        witness: report.model,
                    };
                }
            },
            Err(_) => {
                return InvariantCheckResult::ExitClosureFailed {
                    exit_edge: *exit_edge,
                    witness: None,
                };
            }
        }
    }

    InvariantCheckResult::Accepted
}

// ── Forward reach (initiation support) ───────────────────────────────────────

/// Concrete store facts accumulated during the forward SP pass.
/// Maps `(region_name, constant_offset)` to the value last stored there.
pub(crate) type StoreFacts = BTreeMap<(String, i64), Term>;

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
            _ => {}
        }
    }
    formula
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
/// Returns the reach formula at the header's INPUT augmented with concrete
/// `select(region, k) = value` equations from the preheader stores, putting
/// the reach and normalised candidates in the same variable space.
///
/// # Approximation note
///
/// Sibling loops whose back edges are excluded contribute only their
/// 0-iteration path to the reach, which is an under-approximation for variables
/// the sibling loop modifies.  Seeding sibling headers with their invariants
/// partially compensates: it adds the invariant as an additional OR-branch at
/// the header, so subsequent code can propagate from a state where the invariant
/// holds.
pub(crate) fn forward_reach_at_header(
    cfg: &AbstractCfg,
    header: CfgNodeId,
    inner: InnerInvariants<'_>,
) -> Formula {
    let all_back_edges: BTreeSet<CfgEdgeId> = cfg.detect_back_edges().into_iter().collect();
    let Some(order) = cfg.topological_order_excluding(&all_back_edges) else {
        return Formula::True;
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

    let header_in = reach.get(&header).cloned().unwrap_or(Formula::True);
    let header_in_facts = node_in_facts.get(&header).cloned().unwrap_or_default();
    header_in_facts
        .iter()
        .fold(header_in, |f, ((region, offset), value)| {
            let select_term = Term::select(Memory::var(region.clone()), Term::int(*offset));
            Formula::and(f, Formula::eq(select_term, value.clone()))
        })
}

// ── Backward state propagation ────────────────────────────────────────────────

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

/// Extract the counter variable from a back-edge guard of the form `counter < bound`
/// or `counter <= bound`.  Returns `None` for all other guard shapes.
pub(crate) fn extract_back_edge_counter(info: &LoopInfo) -> Option<Var> {
    match &info.back_edge_guard {
        Formula::Lt(Term::Var(counter), _) | Formula::Le(Term::Var(counter), _) => {
            (counter.sort() == Sort::Int).then(|| counter.clone())
        }
        _ => None,
    }
}

/// Return the top-level conjuncts of a formula.
///
/// If `formula` is `And(items)`, returns references to each item.
/// Otherwise returns a one-element slice containing the formula itself.
pub(crate) fn formula_conjuncts(formula: &Formula) -> Vec<&Formula> {
    match formula {
        Formula::And(items) => items.iter().collect(),
        other => vec![other],
    }
}

/// Negate a comparison precisely: Lt↔Ge, Le↔Gt, Gt↔Le, Ge↔Lt, Not(f)→f.
///
/// Returns `None` for compound formulas (And, Or, Implies) where precise negation
/// would require De Morgan expansion — callers should wrap with `Formula::not` instead.
pub(crate) fn negate_comparison(formula: &Formula) -> Option<Formula> {
    Some(match formula {
        Formula::Lt(l, r) => Formula::ge(l.clone(), r.clone()),
        Formula::Le(l, r) => Formula::gt(l.clone(), r.clone()),
        Formula::Gt(l, r) => Formula::le(l.clone(), r.clone()),
        Formula::Ge(l, r) => Formula::lt(l.clone(), r.clone()),
        Formula::Not(inner) => *inner.clone(),
        _ => return None,
    })
}

/// Return store facts that hold at the loop header on first entry.
///
/// Runs the same forward SP pass as [`forward_reach_at_header`] but returns
/// the accumulated concrete store facts at the header rather than the formula.
pub(crate) fn preheader_store_facts_at_header(
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
