#![allow(dead_code)]

use crate::common::abstract_cfg::{
    AbstractCfg, AbstractEdge, CfgEdgeId, CfgNodeId, TransferEffect,
};
use crate::common::formula::{Formula, SmtModel};
use crate::common::oracle::{Feasibility, Oracle, OracleError, Validity};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::summaries::SummaryTables;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Judgement {
    Verified,
    BugFound { model: Option<SmtModel> },
    Unknown,
}

#[derive(Debug, thiserror::Error)]
pub enum RuleError {
    #[error("unknown edge id: {edge:?}")]
    UnknownEdge { edge: CfgEdgeId },
    #[error("unknown node id: {node:?}")]
    UnknownNode { node: CfgNodeId },
    #[error(transparent)]
    Oracle(#[from] OracleError),
}

pub struct RuleEngine<'a> {
    cfg: &'a AbstractCfg,
    summaries: BTreeMap<CfgNodeId, NodeSummary>,
    blocked_edges: BTreeSet<CfgEdgeId>,
}

impl<'a> RuleEngine<'a> {
    pub fn new(cfg: &'a AbstractCfg) -> Self {
        Self {
            cfg,
            summaries: BTreeMap::new(),
            blocked_edges: BTreeSet::new(),
        }
    }

    pub fn cfg(&self) -> &AbstractCfg {
        self.cfg
    }

    pub fn summaries(&self) -> &BTreeMap<CfgNodeId, NodeSummary> {
        &self.summaries
    }

    pub fn summary(&self, id: CfgNodeId) -> Result<&NodeSummary, RuleError> {
        self.summaries
            .get(&id)
            .ok_or(RuleError::UnknownNode { node: id })
    }

    pub fn summary_mut(&mut self, id: CfgNodeId) -> Result<&mut NodeSummary, RuleError> {
        self.summaries
            .get_mut(&id)
            .ok_or(RuleError::UnknownNode { node: id })
    }

    pub fn blocked_count(&self) -> usize {
        self.blocked_edges.len()
    }

    pub fn is_blocked(&self, edge: CfgEdgeId) -> bool {
        self.blocked_edges.contains(&edge)
    }

    pub fn block_edge(&mut self, edge: CfgEdgeId) {
        self.blocked_edges.insert(edge);
    }

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

    pub fn set_state(&mut self, node: CfgNodeId, formula: Formula) -> Result<(), RuleError> {
        self.summary_mut(node)?.state = formula;
        Ok(())
    }

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

    pub fn verified(&self, entry: CfgNodeId, oracle: &Oracle) -> Result<bool, RuleError> {
        let result = oracle.check_summary(self.summary(entry)?)?;
        Ok(result.feasibility == Feasibility::Infeasible)
    }

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

pub fn callee_of(node: &crate::common::abstract_cfg::AbstractNode) -> Option<String> {
    node.transfer
        .effects
        .iter()
        .find_map(|effect| match effect {
            TransferEffect::Call { callee, .. } if callee != "may_assert" => Some(callee.clone()),
            _ => None,
        })
}

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
