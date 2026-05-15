//! Local propagation rules for the bidirectional may/must fixpoint.
//!
//! [`RuleEngine`] owns the per-node [`NodeSummary`] map for one CFG and drives
//! the two interleaved propagation passes:
//!
//! - **Forward pass** (`must_post` / `must_post_usesummary`): propagates
//!   `reach` along outgoing edges, accumulating reachability evidence.
//! - **Backward pass** (`notmay_pre` / `notmay_pre_usesummary`): propagates
//!   `state` (WP of violation) backward along incoming edges.
//!
//! After each backward step an optional pruning check
//! (`notmay_pre_pruned`) uses the [`Oracle`] to detect edges whose
//! `reach ∧ state` is already infeasible, permanently blocking those paths
//! from further propagation.
//!
//! [`run_to_fixpoint`] orchestrates both passes until no new edges are blocked.
//! The caller then inspects the entry-node summary with [`verified`] /
//! [`bugfound`] to obtain the final [`Judgement`].
//!
//! [`run_to_fixpoint`]: RuleEngine::run_to_fixpoint
//! [`verified`]: RuleEngine::verified
//! [`bugfound`]: RuleEngine::bugfound

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

    /// **Forward rule** — propagates `reach` across `edge`.
    ///
    /// Computes `source.reach ∧ edge.guard` and joins the result into
    /// `target.reach`.  Skips blocked edges silently.
    pub fn must_post(&mut self, edge_id: CfgEdgeId) -> Result<(), RuleError> {
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
                self.block_edge(edge_id);
                self.summary_mut(edge.source)?.state = Formula::False;
                break;
            }
        }
        Ok(())
    }

    /// **Forward rule with callee summaries** — applies must summaries from
    /// `tables` at a call edge.
    ///
    /// If the source node is a call site, joins each matching must-summary
    /// postcondition into `target.reach`, propagating reachability information
    /// derived from the callee's proven postconditions.
    pub fn must_post_usesummary(
        &mut self,
        edge_id: CfgEdgeId,
        tables: &SummaryTables,
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
        for summary in tables.must(&callee) {
            self.summary_mut(edge.target)?
                .join_reach(&summary.postcondition);
        }
        Ok(())
    }

    /// Runs interleaved forward and backward passes to a fixpoint.
    ///
    /// Each iteration:
    /// 1. Forward pass over `order` — applies [`must_post`] and
    ///    [`must_post_usesummary`] on outgoing edges.
    /// 2. Backward pass over `order` in reverse — applies [`notmay_pre`],
    ///    [`notmay_pre_usesummary`], and [`notmay_pre_pruned`] on incoming
    ///    edges.
    ///
    /// Terminates when no new edges are blocked between two consecutive
    /// iterations, or after `|edges| + 1` iterations as a safety bound.
    /// `tables` provides interprocedural summaries; `oracle` is used for
    /// feasibility queries during pruning.
    ///
    /// [`must_post`]: RuleEngine::must_post
    /// [`must_post_usesummary`]: RuleEngine::must_post_usesummary
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
                    self.must_post(edge)?;
                    self.must_post_usesummary(edge, tables)?;
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
        let result = oracle.check_summary(self.summary(entry)?)?;
        Ok(result.feasibility == Feasibility::Infeasible)
    }

    /// Returns a potential counterexample if a bug was found, or `None` if the
    /// analysis could not confirm a violation.
    ///
    /// Returns `Some(model)` when the oracle finds `reach ∧ state` feasible at
    /// the entry node, where `model` is `Some(witness)` if the solver produced
    /// a concrete state or `None` if it only confirmed feasibility without a
    /// model.  Returns `None` when the combined formula is infeasible or the
    /// oracle returns `Unknown`.
    pub fn bugfound(
        &self,
        entry: CfgNodeId,
        oracle: &Oracle,
    ) -> Result<Option<Option<SmtModel>>, RuleError> {
        let result = oracle.check_summary(self.summary(entry)?)?;
        Ok(match result.feasibility {
            Feasibility::Feasible => Some(result.model),
            Feasibility::Infeasible | Feasibility::Unknown => None,
        })
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
    fn must_post_propagates_guarded_reachability() {
        let (cfg, _, n1, edge) = tiny_cfg();
        let mut engine = RuleEngine::new(&cfg);
        engine.init();
        engine.must_post(edge).unwrap();
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
