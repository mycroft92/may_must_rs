//! Local propagation rules for the SMASH-paper analysis directions.
//!
//! [`RuleEngine`] owns the per-node [`NodeSummary`] map for one CFG and drives
//! the propagation passes that implement the paper's directions:
//!
//! - **Forward MAY** (over-approx SP): [`forward_may_post`],
//!   [`forward_may_usesummary`].  Widens `reach` via disjunction.  In
//!   SMASH-paper terminology this is the MAY family — used to prune backward
//!   not-may propagation in [`notmay_pre_pruned`].
//! - **Backward NOT-MAY** (over-approx WP): [`notmay_pre`],
//!   [`notmay_pre_usesummary`], [`notmay_pre_pruned`].  Propagates `state`
//!   (WP of the violation post) backward.  Proves safety when `reach ∧ state`
//!   at the entry is infeasible.
//! - **Forward MUST** (under-approx, feasibility-checked SP):
//!   [`forward_must_post`] (scaffolding).  Currently NOT wired into
//!   [`run_to_fixpoint`] because `TransferFn::sp` does not yet model memory.
//!   The functional realization of forward MUST is backward NOT-MAY on a CFG
//!   that is acyclic — either natively, or after BMC unrolling.  See
//!   [`crate::may_must_analysis::bmc::bmc_check`] and
//!   `design_notes/SMASH_FORWARD_MUST.md`.
//!
//! # Debug logging convention
//!
//! Every rule application emits a `log::debug!(target: "rules", ...)` line
//! whose first token is the rule name in `[brackets]` and whose body names
//! the formula it added (or the action it took).  This makes a trace of
//! a fixpoint run mechanically reconstructible — `RUST_LOG=rules=debug`
//! shows exactly which rule changed which node summary, in order.  The
//! verdict-producing methods ([`verified`], [`bugfound`], [`must_bugfound`])
//! follow the same convention.
//!
//! [`run_to_fixpoint`]: RuleEngine::run_to_fixpoint
//! [`verified`]: RuleEngine::verified
//! [`bugfound`]: RuleEngine::bugfound
//! [`forward_may_post`]: RuleEngine::forward_may_post
//! [`forward_may_usesummary`]: RuleEngine::forward_may_usesummary
//! [`forward_must_post`]: RuleEngine::forward_must_post
//! [`notmay_pre`]: RuleEngine::notmay_pre
//! [`notmay_pre_usesummary`]: RuleEngine::notmay_pre_usesummary
//! [`notmay_pre_pruned`]: RuleEngine::notmay_pre_pruned
//! [`must_bugfound`]: RuleEngine::must_bugfound

#![allow(dead_code)]

use crate::common::abstract_cfg::{
    AbstractCfg, AbstractEdge, CfgEdgeId, CfgNodeId, TransferEffect,
};
use crate::common::formula::{Formula, SmtModel};
use crate::common::oracle::{Feasibility, Oracle, OracleError, Validity};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::summaries::SummaryTables;
use std::collections::{BTreeMap, BTreeSet};

/// The outcome of checking one assertion with the bidirectional analysis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Judgement {
    /// The assertion holds on all reachable paths: `reach ∧ state` is
    /// unsatisfiable at the procedure entry.
    Verified,
    /// A potential counterexample was found.  `model` carries a concrete
    /// witness state when the SMT solver produced one; `None` means the solver
    /// confirmed feasibility but did not return a model.
    BugFound { model: Option<SmtModel> },
    /// The analysis could not conclude either way (e.g. the oracle returned
    /// `Unknown`).
    Unknown,
}

/// Errors that can arise while applying propagation rules.
#[derive(Debug, thiserror::Error)]
pub enum RuleError {
    /// An edge identifier referenced during propagation is not present in the
    /// CFG.
    #[error("unknown edge id: {edge:?}")]
    UnknownEdge { edge: CfgEdgeId },
    /// A node identifier referenced during propagation is not present in the
    /// CFG.
    #[error("unknown node id: {node:?}")]
    UnknownNode { node: CfgNodeId },
    /// An error returned by the SMT oracle (e.g. solver timeout or internal
    /// error).
    #[error(transparent)]
    Oracle(#[from] OracleError),
}

/// Fixpoint engine for a single procedure's bidirectional may/must analysis.
///
/// Maintains one [`NodeSummary`] per CFG node and a set of *blocked* edges.
/// A blocked edge has been permanently pruned — its `reach ∧ state` was found
/// infeasible, so no further propagation can flow through it.
///
/// Typical usage:
/// 1. [`new`] — bind to a CFG.
/// 2. [`init`] — seed all node summaries (entry = `(True, False)`, rest =
///    `(False, False)`).
/// 3. Inject any initial `state` formulas at assertion nodes via [`set_state`].
/// 4. [`run_to_fixpoint`] — iterate until stable.
/// 5. Query [`verified`] or [`bugfound`] for the result.
///
/// [`new`]: RuleEngine::new
/// [`init`]: RuleEngine::init
/// [`set_state`]: RuleEngine::set_state
pub struct RuleEngine<'a> {
    cfg: &'a AbstractCfg,
    summaries: BTreeMap<CfgNodeId, NodeSummary>,
    blocked_edges: BTreeSet<CfgEdgeId>,
}

impl<'a> RuleEngine<'a> {
    /// Creates a new engine bound to `cfg`.  Call [`init`] before running any
    /// rules.
    ///
    /// [`init`]: RuleEngine::init
    pub fn new(cfg: &'a AbstractCfg) -> Self {
        Self {
            cfg,
            summaries: BTreeMap::new(),
            blocked_edges: BTreeSet::new(),
        }
    }

    /// Returns the underlying CFG.
    pub fn cfg(&self) -> &AbstractCfg {
        self.cfg
    }

    /// Returns the full map of current node summaries.
    pub fn summaries(&self) -> &BTreeMap<CfgNodeId, NodeSummary> {
        &self.summaries
    }

    /// Returns the summary for `id`, or [`RuleError::UnknownNode`] if `id` is
    /// not in the CFG.
    pub fn summary(&self, id: CfgNodeId) -> Result<&NodeSummary, RuleError> {
        self.summaries
            .get(&id)
            .ok_or(RuleError::UnknownNode { node: id })
    }

    /// Returns a mutable reference to the summary for `id`, or
    /// [`RuleError::UnknownNode`] if `id` is not in the CFG.
    pub fn summary_mut(&mut self, id: CfgNodeId) -> Result<&mut NodeSummary, RuleError> {
        self.summaries
            .get_mut(&id)
            .ok_or(RuleError::UnknownNode { node: id })
    }

    /// Returns the number of edges that have been permanently blocked.
    pub fn blocked_count(&self) -> usize {
        self.blocked_edges.len()
    }

    /// Returns `true` if `edge` has been permanently blocked.
    pub fn is_blocked(&self, edge: CfgEdgeId) -> bool {
        self.blocked_edges.contains(&edge)
    }

    /// Permanently blocks `edge`, preventing it from carrying any further
    /// forward or backward propagation.
    pub fn block_edge(&mut self, edge: CfgEdgeId) {
        self.blocked_edges.insert(edge);
    }

    /// Initialises all node summaries to their seed values.
    ///
    /// The entry node receives `(True, False)` (unconditionally reachable, no
    /// violation known).  All other nodes receive `(False, False)` (not yet
    /// reachable, no violation known).  Any previously blocked edges are
    /// **not** cleared; call this only before the first fixpoint run.
    pub fn init(&mut self) {
        self.summaries.clear();
        for id in self.cfg.node_ids() {
            let summary = if id == self.cfg.entry() {
                NodeSummary::entry(id)
            } else {
                NodeSummary::unreachable(id)
            };
            self.summaries.insert(id, summary);
        }
    }

    /// Directly sets the `state` formula for `node`.
    ///
    /// Used to seed the backward analysis at assertion nodes before the
    /// fixpoint loop begins.  Overwrites any previously accumulated `state`.
    pub fn set_state(&mut self, node: CfgNodeId, formula: Formula) -> Result<(), RuleError> {
        self.summary_mut(node)?.state = formula;
        Ok(())
    }

    /// **Forward MUST rule** — under-approximate concrete reachability
    /// propagation across `edge`.  Paper-correct.
    ///
    /// **Currently inert** in [`run_to_fixpoint`] because `TransferFn::sp`
    /// does not model memory (`sp_one` for `MemoryStore` / `Load` is a
    /// no-op), so the propagated `must_reach` would mis-evaluate any
    /// memory-using program.  Today the functional realization of
    /// forward MUST is backward NOT-MAY on an acyclic CFG (native or
    /// BMC-unrolled) — see `design_notes/SMASH_FORWARD_MUST.md`.
    ///
    /// **Keep**: this rule is paper-equivalent and will become active
    /// when SP is upgraded to handle memory (tracked in TODO.md under
    /// "Memory-aware forward SP").  Removing it would walk back paper
    /// equivalence.
    ///
    /// Computes the strongest-postcondition of `source.must_reach` through
    /// the source node's transfer function, the edge guard, and the edge's
    /// own transfer (PHI assignments).  Then **feasibility-checks** the
    /// result via the SMT oracle.  Only feasible propagations are joined
    /// into `target.must_reach`.
    ///
    /// This is the SMASH-paper **MUST** direction: the under-approximate
    /// counterpart to forward MAY.  Every disjunct in `target.must_reach`
    /// after this rule fires corresponds to a real concrete reachable
    /// execution.  Combined with the assertion's violation formula, it
    /// soundly detects BugFound on acyclic CFGs (cyclic CFGs are unrolled
    /// first via [`crate::may_must_analysis::bmc::bmc_check`]).
    ///
    /// Skips blocked edges silently.  Skips when `source.must_reach` is
    /// already `False` (no concrete path reaches the source).
    pub fn forward_must_post(
        &mut self,
        edge_id: CfgEdgeId,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        // NOTE: Deliberately NOT checking `is_blocked` here.  Back-edges
        // are typically blocked for the backward direction (so
        // `notmay_pre` doesn't loop), but forward MUST *needs* back-edge
        // propagation to iterate the loop body concretely.  The fixpoint's
        // `max_iterations` cap (`edges + 1`) bounds the total work.  Per
        // SMASH-paper Fig 8–10 + the DART concolic-execution model in
        // `design_notes/SMASH_FORWARD_MUST.md`, forward MUST enumerates
        // concrete paths whose depth is determined by feasibility, not by
        // a global edge-blocking decision.
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        log::debug!(
            target: "rules",
            "[forward_must_post] {:?}→{:?}: entered",
            edge.source, edge.target
        );

        let source_must = self.summary(edge.source)?.must_reach.clone();
        if source_must == Formula::False {
            log::debug!(
                target: "rules",
                "[forward_must_post] {:?}→{:?}: source must_reach is False — skip",
                edge.source, edge.target
            );
            return Ok(());
        }

        // SP through source node's transfer, then edge guard, then edge's effects.
        let source_post = self
            .cfg
            .node(edge.source)
            .map_err(|_| RuleError::UnknownNode { node: edge.source })?
            .transfer
            .sp(&source_must);
        let guarded = Formula::and(source_post, edge.guard.clone());
        let through_edge = edge.transfer().sp(&guarded);

        // Feasibility-check the propagated state.  Only join if SAT — the
        // under-approximation invariant requires every disjunct in
        // `must_reach` to have at least one model corresponding to a real
        // execution.
        let feas = oracle.feasibility(&through_edge)?;
        if feas != Feasibility::Feasible {
            log::debug!(
                target: "rules",
                "[forward_must_post] {:?}→{:?}: feasibility={:?} — skip",
                edge.source, edge.target, feas
            );
            return Ok(());
        }

        log::debug!(
            target: "rules",
            "[forward_must_post] {:?}→{:?}: must_reach += {}",
            edge.source,
            edge.target,
            fmt_formula(&through_edge),
        );
        self.summary_mut(edge.target)?
            .join_must_reach(&through_edge);
        Ok(())
    }

    /// **Forward MUST rule with callee summaries.**  At a call edge,
    /// applies callee's `MustSummary` (primary, under-approximate
    /// witness) and `NotMaySummary` (auxiliary, narrows away
    /// counterfactual states) to enrich `must_reach[target]`.
    ///
    /// Soundness:
    /// - **Must summary** `(pre_s, post_s)` says: "from some state
    ///   satisfying `pre_s`, the callee reaches a state satisfying
    ///   `post_s`".  If `caller.must_reach ⇒ pre_s` (caller's concrete
    ///   state lies in summary's pre-range), then `post_s` is
    ///   concretely reachable after the call — join `post_s` into
    ///   `target.must_reach`.
    /// - **NotMay summary** `(pre_s, post_s)` says: "from `pre_s`, the
    ///   callee cannot reach `post_s`".  If `caller.must_reach ⇒ pre_s`,
    ///   then `¬post_s` holds after the call — join `¬post_s` into
    ///   `target.must_reach` (narrowing).
    ///
    /// Both checks gate on **`caller.must_reach ⇒ summary.pre`** via
    /// the SMT oracle.  Skipped if `caller.must_reach == False` (no
    /// concrete path reaches this call).
    pub fn forward_must_usesummary(
        &mut self,
        edge_id: CfgEdgeId,
        tables: &SummaryTables,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        if self.is_blocked(edge_id) {
            return Ok(());
        }
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        let Some(callee) = callee_of(
            self.cfg
                .node(edge.source)
                .map_err(|_| RuleError::UnknownNode { node: edge.source })?,
        ) else {
            return Ok(());
        };
        let caller_must = self.summary(edge.source)?.must_reach.clone();
        if caller_must == Formula::False {
            return Ok(());
        }

        // Must summaries — primary source of concrete reach contribution.
        for summary in tables.must(&callee) {
            let applies = if matches!(summary.precondition, Formula::True) {
                true
            } else {
                matches!(
                    oracle.implies(&caller_must, &summary.precondition)?,
                    Validity::Valid
                )
            };
            if !applies {
                continue;
            }
            log::debug!(
                target: "rules",
                "[forward_must_usesummary] {:?}→{:?}: callee '{}' must-summary applies: must_reach += {}",
                edge.source, edge.target, callee, fmt_formula(&summary.postcondition),
            );
            self.summary_mut(edge.target)?
                .join_must_reach(&summary.postcondition);
        }

        // NotMay summaries — auxiliary; their negation narrows the
        // post-call concrete state.  Per the user's cross-direction
        // requirement: forward MUST consults both summary kinds.
        for summary in tables.notmay(&callee) {
            let applies = if matches!(summary.precondition, Formula::True) {
                true
            } else {
                matches!(
                    oracle.implies(&caller_must, &summary.precondition)?,
                    Validity::Valid
                )
            };
            if !applies {
                continue;
            }
            let narrowing = Formula::not(summary.postcondition.clone());
            log::debug!(
                target: "rules",
                "[forward_must_usesummary] {:?}→{:?}: callee '{}' notmay-summary narrows: must_reach ∧= {}",
                edge.source, edge.target, callee, fmt_formula(&narrowing),
            );
            // For NotMay narrowing we conjoin (not disjoin) because the
            // narrowing is universally true at the call's post-state.
            let target_must = self.summary(edge.target)?.must_reach.clone();
            let narrowed = Formula::and(target_must, narrowing);
            if oracle.feasibility(&narrowed)? == Feasibility::Feasible {
                self.summary_mut(edge.target)?.must_reach = narrowed;
            }
        }
        Ok(())
    }

    /// **Forward MAY rule** — propagates `reach` across `edge` via SP.
    ///
    /// Computes `source.reach ∧ edge.guard` and joins the result into
    /// `target.reach`.  The join is a disjunction, so this is an
    /// over-approximation (SMASH-paper "MAY" semantics), not an
    /// under-approximation.
    ///
    /// Renamed from `must_post` in v0.15.0 to reflect honest semantics.  Skips
    /// blocked edges silently.
    pub fn forward_may_post(&mut self, edge_id: CfgEdgeId) -> Result<(), RuleError> {
        if self.is_blocked(edge_id) {
            return Ok(());
        }
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        let source_reach = self.summary(edge.source)?.reach.clone();
        let propagated = Formula::and(source_reach, edge.guard);
        log::debug!(
            target: "rules",
            "[forward_may_post] {:?}→{:?}: reach += {}",
            edge.source,
            edge.target,
            fmt_formula(&propagated),
        );
        self.summary_mut(edge.target)?.join_reach(&propagated);
        Ok(())
    }

    /// **Backward rule** — propagates `state` (violation precondition) across
    /// `edge`.
    ///
    /// Computes the weakest precondition of `target.state` through the edge
    /// transfer function and the edge guard, then joins the result into
    /// `source.state`.  Skips blocked edges silently.
    pub fn notmay_pre(&mut self, edge_id: CfgEdgeId) -> Result<(), RuleError> {
        if self.is_blocked(edge_id) {
            return Ok(());
        }
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        let target_state = self.summary(edge.target)?.state.clone();
        let edge_pre = edge.transfer().wp(&target_state);
        let post_at_source = Formula::and(edge.guard, edge_pre);
        let pre_at_source = self
            .cfg
            .node(edge.source)
            .map_err(|_| RuleError::UnknownNode { node: edge.source })?
            .transfer
            .wp(&post_at_source);
        log::debug!(
            target: "rules",
            "[notmay_pre] {:?}→{:?}: state += {}",
            edge.source,
            edge.target,
            fmt_formula(&pre_at_source),
        );
        self.summary_mut(edge.source)?.join_state(&pre_at_source);
        Ok(())
    }

    /// **Backward rule with pruning** — runs [`notmay_pre`] then checks
    /// whether the source node's `reach ∧ state` has become infeasible.
    ///
    /// If the oracle reports infeasibility, `edge` is permanently blocked and
    /// `source.state` is reset to `False`, preventing spurious further
    /// propagation through this path.
    ///
    /// [`notmay_pre`]: RuleEngine::notmay_pre
    pub fn notmay_pre_pruned(
        &mut self,
        edge_id: CfgEdgeId,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        self.notmay_pre(edge_id)?;
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?;
        let combined = self.summary(edge.source)?.combined();
        if oracle.feasibility(&combined)? == Feasibility::Infeasible {
            log::debug!(
                target: "rules",
                "[notmay_pre_pruned] {:?}→{:?}: reach∧state infeasible — edge blocked, state := False",
                edge.source,
                edge.target,
            );
            self.block_edge(edge_id);
            self.summary_mut(edge.source)?.state = Formula::False;
        }
        Ok(())
    }

    /// **Backward rule with callee summaries** — applies not-may summaries
    /// from `tables` at a call edge.
    ///
    /// If the target node is a call site and `tables` contains a not-may
    /// summary whose postcondition is implied by the current `target.state`
    /// under a feasible precondition, the edge is permanently blocked (the
    /// callee is already known safe under those conditions).
    pub fn notmay_pre_usesummary(
        &mut self,
        edge_id: CfgEdgeId,
        tables: &SummaryTables,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        if self.is_blocked(edge_id) {
            return Ok(());
        }
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        let Some(callee) = callee_of(
            self.cfg
                .node(edge.target)
                .map_err(|_| RuleError::UnknownNode { node: edge.target })?,
        ) else {
            return Ok(());
        };
        for summary in tables.notmay(&callee) {
            let source_reach = self.summary(edge.source)?.reach.clone();
            let feasible =
                oracle.feasibility(&Formula::and(source_reach, summary.precondition.clone()))?;
            let target_state = self.summary(edge.target)?.state.clone();
            let valid = oracle.implies(&target_state, &summary.postcondition)?;
            if feasible != Feasibility::Infeasible && valid == Validity::Valid {
                log::debug!(
                    target: "rules",
                    "[notmay_pre_usesummary] {:?}→{:?}: callee '{}' summary discharges state — edge blocked, state := False",
                    edge.source,
                    edge.target,
                    callee,
                );
                self.block_edge(edge_id);
                self.summary_mut(edge.source)?.state = Formula::False;
                break;
            }
        }
        Ok(())
    }

    /// **Forward MAY rule with callee summaries** — applies forward-may
    /// summaries from `tables` at a call edge, gated by a **precondition
    /// implication check** (subsumption).
    ///
    /// Soundness condition: only join the summary's `postcondition` into
    /// `target.reach` when `caller.reach ⇒ summary.precondition`.  Without
    /// this check, callers whose reach is outside the summary's pre-range
    /// would receive a `post` that doesn't actually hold for them.
    ///
    /// For legacy summaries with `precondition: True` (the eager-inlined
    /// `compute_return_summary` shape) the implication is trivially Valid,
    /// so this rule reduces to the v0.15 behaviour.  For paper-equivalent
    /// contextual summaries with non-True preconditions, mismatched call
    /// contexts are silently skipped — sound; the caller's analysis simply
    /// doesn't learn the post for that summary.
    pub fn forward_may_usesummary(
        &mut self,
        edge_id: CfgEdgeId,
        tables: &SummaryTables,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        if self.is_blocked(edge_id) {
            return Ok(());
        }
        let edge = self
            .cfg
            .edge(edge_id)
            .map_err(|_| RuleError::UnknownEdge { edge: edge_id })?
            .clone();
        let Some(callee) = callee_of(
            self.cfg
                .node(edge.source)
                .map_err(|_| RuleError::UnknownNode { node: edge.source })?,
        ) else {
            return Ok(());
        };
        let caller_reach = self.summary(edge.source)?.reach.clone();
        for summary in tables.forward_may(&callee) {
            // Cheap shortcut for the legacy True-precondition case.
            let applies = if matches!(summary.precondition, Formula::True) {
                true
            } else {
                matches!(
                    oracle.implies(&caller_reach, &summary.precondition)?,
                    Validity::Valid
                )
            };
            if !applies {
                log::debug!(
                    target: "rules",
                    "[forward_may_usesummary] {:?}→{:?}: callee '{}' summary skipped — \
                     caller.reach does not imply summary.precondition",
                    edge.source, edge.target, callee,
                );
                continue;
            }
            log::debug!(
                target: "rules",
                "[forward_may_usesummary] {:?}→{:?}: callee '{}' may-summary applies: reach += {}",
                edge.source,
                edge.target,
                callee,
                fmt_formula(&summary.postcondition),
            );
            self.summary_mut(edge.target)?
                .join_reach(&summary.postcondition);
        }
        Ok(())
    }

    /// Runs interleaved forward and backward passes to a fixpoint.
    ///
    /// Each iteration:
    /// 1. Forward MAY pass over `order` — applies [`forward_may_post`] and
    ///    [`forward_may_usesummary`] on outgoing edges (SP, over-approximate).
    /// 2. Forward MUST pass over `order` — applies [`forward_must_post`] on
    ///    outgoing edges (SP + per-step SMT feasibility check;
    ///    under-approximate, "MUST" semantics).
    /// 3. Backward NOT-MAY pass over `order` in reverse — applies
    ///    [`notmay_pre`], [`notmay_pre_usesummary`], and [`notmay_pre_pruned`]
    ///    on incoming edges (WP, over-approximate).
    ///
    /// Passes 1 and 3 are MAY-family (over-approximations).  Pass 2 is the
    /// MUST direction (under-approximate, feasibility-checked) — its result
    /// at the assertion site combined with the violation formula is the only
    /// sound BugFound witness for cyclic CFGs once they have been unrolled
    /// via [`crate::may_must_analysis::bmc::bmc_check`].
    ///
    /// Terminates when no new edges are blocked between two consecutive
    /// iterations, or after `|edges| + 1` iterations as a safety bound.
    /// `tables` provides interprocedural summaries; `oracle` is used for
    /// feasibility queries during pruning.
    ///
    /// [`forward_may_post`]: RuleEngine::forward_may_post
    /// [`forward_may_usesummary`]: RuleEngine::forward_may_usesummary
    /// [`notmay_pre`]: RuleEngine::notmay_pre
    /// [`notmay_pre_usesummary`]: RuleEngine::notmay_pre_usesummary
    /// [`notmay_pre_pruned`]: RuleEngine::notmay_pre_pruned
    pub fn run_to_fixpoint(
        &mut self,
        order: &[CfgNodeId],
        tables: &SummaryTables,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let max_iterations = self.cfg.edges().len() + 1;
        for _ in 0..=max_iterations {
            let blocked_before = self.blocked_count();
            for node in order {
                for edge in self.cfg.outgoing_edges(*node) {
                    self.forward_may_post(edge)?;
                    self.forward_may_usesummary(edge, tables, oracle)?;
                    // NOTE: `forward_must_post` / `forward_must_usesummary`
                    // are NOT wired here.  Their soundness requires
                    // memory-aware SP (Skolemized stores + scalar
                    // assigns) which is too expensive on loop unrolling
                    // (4000+ character formulas tripping SMT timeouts).
                    // The paper-equivalent forward-MUST realization for
                    // cyclic CFGs is the DART-style bounded-input path
                    // enumeration that lives in `bmc::bmc_check`; the
                    // orchestrator invokes it via `analyze_with_tables`
                    // when the may-side cannot prove safety.  See
                    // `design_notes/SMASH_FORWARD_MUST.md`.
                }
            }
            for node in order.iter().rev() {
                for edge in self.cfg.incoming_edges(*node) {
                    self.notmay_pre(edge)?;
                    self.notmay_pre_usesummary(edge, tables, oracle)?;
                    self.notmay_pre_pruned(edge, oracle)?;
                }
            }
            if blocked_before == self.blocked_count() {
                break;
            }
        }
        Ok(())
    }

    /// Returns `true` when the analysis has **verified** the assertion.
    ///
    /// Queries the oracle with the entry node's `reach ∧ state`.  Infeasibility
    /// means no reachable state can violate the assertion, so the assertion
    /// holds on all reachable paths.
    pub fn verified(&self, entry: CfgNodeId, oracle: &Oracle) -> Result<bool, RuleError> {
        let summary = self.summary(entry)?;
        let result = oracle.check_summary(summary)?;
        let verified = result.feasibility == Feasibility::Infeasible;
        log::debug!(
            target: "rules",
            "[verified] entry {:?}: reach={} state={} → {}",
            entry,
            fmt_formula(&summary.reach),
            fmt_formula(&summary.state),
            if verified { "Verified (reach∧state UNSAT)" } else { "not verified" }
        );
        Ok(verified)
    }

    /// Returns a potential counterexample if a bug was found, or `None` if the
    /// analysis could not confirm a violation.
    ///
    /// # Soundness (v0.15.0+)
    ///
    /// This check inspects `reach ∧ state` at the entry node.  In SMASH-paper
    /// terms both components are **MAY-family over-approximations**:
    ///
    /// - `reach` is forward SP, widened at loop headers by injected invariants
    ///   and at call sites by MAY summaries (disjunctive `join_reach`).
    /// - `state` is backward WP, propagated over the same widened control flow.
    ///
    /// Combining two over-approximations and finding a satisfying model does
    /// **not** in general prove a real bug — the witness may sit entirely in
    /// the over-approximation gap (a state that's spuriously in both reach
    /// and state without corresponding to any concrete execution).  This is
    /// the root cause of the historical false-UNSAFE verdicts on
    /// `linear_sea.ch`, `veris_NetBSD-libc_loop.i`, and `bin-suffix-5`.
    ///
    /// Sound BugFound verdicts require an **under-approximate** witness — see
    /// [`crate::may_must_analysis::bmc::bmc_check`] (MUST direction in the
    /// SMASH orchestrator).
    ///
    /// To keep this method usable for legitimately acyclic CFGs without
    /// MAY-summary widening — where SP/WP are precise modulo SMT — the caller
    /// must explicitly confirm the CFG is acyclic via the `cfg_is_acyclic`
    /// parameter.  When the CFG has back edges, this method returns `None`
    /// (no bug reported); callers should defer to BMC for those programs.
    pub fn bugfound(
        &self,
        entry: CfgNodeId,
        oracle: &Oracle,
        cfg_is_acyclic: bool,
    ) -> Result<Option<Option<SmtModel>>, RuleError> {
        if !cfg_is_acyclic {
            log::debug!(
                target: "rules",
                "[bugfound] entry {:?}: cfg is cyclic — skipping unsound reach∧state \
                 heuristic (deferring bug-finding to BMC)",
                entry,
            );
            return Ok(None);
        }
        let summary = self.summary(entry)?;
        let result = oracle.check_summary(summary)?;
        match result.feasibility {
            Feasibility::Feasible => {
                log::debug!(
                    target: "rules",
                    "[bugfound] entry {:?}: reach∧state SAT on acyclic CFG → BugFound (witness retained)",
                    entry,
                );
                Ok(Some(result.model))
            }
            Feasibility::Infeasible | Feasibility::Unknown => {
                log::debug!(
                    target: "rules",
                    "[bugfound] entry {:?}: reach∧state {:?} → no bug",
                    entry, result.feasibility,
                );
                Ok(None)
            }
        }
    }

    /// **Paper-equivalent BugFound check** — under-approximate forward MUST.
    ///
    /// Conjoins `must_reach[assertion_site]` (a sound under-approximation of
    /// concrete states reachable at the assertion) with the violation
    /// formula `¬obligation` and asks the SMT oracle for a satisfying model.
    /// If SAT, returns the model as a real bug witness.
    ///
    /// Soundness: every disjunct in `must_reach` was added only after
    /// [`forward_must_post`] confirmed it feasible.  Therefore any model of
    /// `must_reach ∧ ¬obligation` corresponds to a real execution that
    /// reaches the assertion site and violates the obligation.
    ///
    /// Caller responsibility: the CFG passed to this engine should be
    /// **acyclic**.  Cyclic CFGs must be unrolled (via
    /// [`crate::may_must_analysis::bmc::bmc_check`]) before forward MUST
    /// produces a meaningful `must_reach`.
    pub fn must_bugfound(
        &self,
        assertion_site: CfgNodeId,
        violation: &Formula,
        oracle: &Oracle,
    ) -> Result<Option<Option<SmtModel>>, RuleError> {
        let must_reach_pre = &self.summary(assertion_site)?.must_reach;
        if *must_reach_pre == Formula::False {
            log::debug!(
                target: "rules",
                "[must_bugfound] site {:?}: must_reach is False — no concrete witness",
                assertion_site,
            );
            return Ok(None);
        }
        let post = self
            .cfg
            .node(assertion_site)
            .map_err(|_| RuleError::UnknownNode {
                node: assertion_site,
            })?
            .transfer
            .sp(must_reach_pre);
        let combined = Formula::and(post, violation.clone());
        let report = oracle.feasibility_with_model(&combined)?;
        match report.feasibility {
            Feasibility::Feasible => {
                log::debug!(
                    target: "rules",
                    "[must_bugfound] site {:?}: SP(site.transfer, must_reach) ∧ ¬obligation SAT → real BugFound",
                    assertion_site,
                );
                Ok(Some(report.model))
            }
            Feasibility::Infeasible | Feasibility::Unknown => {
                log::debug!(
                    target: "rules",
                    "[must_bugfound] site {:?}: {:?} — no real witness",
                    assertion_site, report.feasibility,
                );
                Ok(None)
            }
        }
    }
}

/// Extracts the callee name from a node's transfer function if the node
/// represents a non-assertion call site.
///
/// Returns `None` if the node has no `Call` effect, or if the only call is to
/// `may_assert` (the internal assertion intrinsic).
pub fn callee_of(node: &crate::common::abstract_cfg::AbstractNode) -> Option<String> {
    node.transfer
        .effects
        .iter()
        .find_map(|effect| match effect {
            TransferEffect::Call { callee, .. } if callee != "may_assert" => Some(callee.clone()),
            _ => None,
        })
}

/// Convenience accessor: returns `Some(&edge)` for `id` if it exists in `cfg`,
/// or `None` otherwise.
pub fn edge_view(cfg: &AbstractCfg, id: CfgEdgeId) -> Option<&AbstractEdge> {
    cfg.edge(id).ok()
}

/// Format a formula for diff-debug logging, truncating long conjunctions.
fn fmt_formula(formula: &Formula) -> String {
    const WRAP: usize = 120;
    let s = formula.to_string();
    if s.len() <= WRAP {
        s
    } else {
        format!("{} …(+{})", &s[..WRAP], s.len() - WRAP)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{TransferEffect, TransferFn};

    fn tiny_cfg() -> (AbstractCfg, CfgNodeId, CfgNodeId, CfgEdgeId) {
        let mut cfg = AbstractCfg::new("entry");
        let n1 = cfg.add_node("n1", TransferFn::identity());
        let edge = cfg
            .add_edge(
                cfg.entry(),
                n1,
                Formula::bool_var("g"),
                vec![TransferEffect::Nop],
            )
            .unwrap();
        cfg.mark_exit(n1).unwrap();
        cfg.ensure_single_exit().unwrap();
        let entry = cfg.entry();
        (cfg, entry, n1, edge)
    }

    #[test]
    fn init_marks_entry_reachable_only() {
        let (cfg, entry, n1, _) = tiny_cfg();
        let mut engine = RuleEngine::new(&cfg);
        engine.init();
        assert_eq!(engine.summary(entry).unwrap().reach, Formula::True);
        assert_eq!(engine.summary(n1).unwrap().reach, Formula::False);
    }

    #[test]
    fn forward_may_post_propagates_guarded_reachability() {
        let (cfg, _, n1, edge) = tiny_cfg();
        let mut engine = RuleEngine::new(&cfg);
        engine.init();
        engine.forward_may_post(edge).unwrap();
        assert_eq!(
            engine.summary(n1).unwrap().reach,
            Formula::or(
                Formula::False,
                Formula::and(Formula::True, Formula::bool_var("g"))
            )
        );
    }

    #[test]
    fn notmay_pre_propagates_backward_state() {
        let (cfg, entry, n1, edge) = tiny_cfg();
        let mut engine = RuleEngine::new(&cfg);
        engine.init();
        engine.set_state(n1, Formula::bool_var("bad")).unwrap();
        engine.notmay_pre(edge).unwrap();
        assert_ne!(engine.summary(entry).unwrap().state, Formula::False);
    }
}
