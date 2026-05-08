use crate::analysis::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, SmtModel};
use crate::analysis::node_summary::NodeSummary;
use crate::analysis::oracle::{Feasibility, Oracle, OracleError};
use std::collections::BTreeMap;

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
}

impl<'a> RuleEngine<'a> {
    pub fn new(cfg: &'a AbstractCfg) -> Self {
        Self {
            cfg,
            summaries: BTreeMap::new(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::abstract_cfg::{TransferEffect, TransferFn};

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
