//! Paper-state carriers for path summaries `Pi_n`, obligations `Omega_n`, and
//! tracked local facts `N_e`.
//!
//! This module stores analysis-owned facts keyed by CFG node/edge identifiers.
//! It does not perform solver reasoning or transfer semantics by itself.

use crate::analysis::cfg::{CfgEdgeId, CfgNodeId};
use crate::analysis::formula::Formula;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathSummary {
    predicate: Formula,
}

impl PathSummary {
    pub fn reachable() -> Self {
        Self {
            predicate: Formula::True,
        }
    }

    pub fn unreachable() -> Self {
        Self {
            predicate: Formula::False,
        }
    }

    pub fn predicate(&self) -> &Formula {
        &self.predicate
    }

    pub fn refine(&mut self, guard: Formula) {
        self.predicate = Formula::and(self.predicate.clone(), guard);
    }

    pub fn join(&mut self, incoming: &PathSummary) {
        self.predicate = Formula::or(self.predicate.clone(), incoming.predicate.clone());
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TrackedFacts {
    facts: Vec<Formula>,
}

impl TrackedFacts {
    pub fn push(&mut self, fact: Formula) {
        self.facts.push(fact);
    }

    pub fn formulas(&self) -> &[Formula] {
        &self.facts
    }

    pub fn collapse(&self) -> Formula {
        Formula::and_all(self.facts.clone())
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Obligations {
    obligations: Vec<Formula>,
}

impl Obligations {
    pub fn push(&mut self, formula: Formula) {
        self.obligations.push(formula);
    }

    pub fn formulas(&self) -> &[Formula] {
        &self.obligations
    }

    pub fn collapse(&self) -> Formula {
        Formula::and_all(self.obligations.clone())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeState {
    path_summary: PathSummary,
    facts: TrackedFacts,
    obligations: Obligations,
}

impl NodeState {
    pub fn entry() -> Self {
        Self {
            path_summary: PathSummary::reachable(),
            facts: TrackedFacts::default(),
            obligations: Obligations::default(),
        }
    }

    pub fn unreachable() -> Self {
        Self {
            path_summary: PathSummary::unreachable(),
            facts: TrackedFacts::default(),
            obligations: Obligations::default(),
        }
    }

    pub fn path_summary(&self) -> &PathSummary {
        &self.path_summary
    }

    pub fn path_summary_mut(&mut self) -> &mut PathSummary {
        &mut self.path_summary
    }

    pub fn facts(&self) -> &TrackedFacts {
        &self.facts
    }

    pub fn facts_mut(&mut self) -> &mut TrackedFacts {
        &mut self.facts
    }

    pub fn obligations(&self) -> &Obligations {
        &self.obligations
    }

    pub fn obligations_mut(&mut self) -> &mut Obligations {
        &mut self.obligations
    }
}

#[derive(Clone, Debug, Default)]
pub struct AnalysisState {
    nodes: BTreeMap<CfgNodeId, NodeState>,
    node_visits: BTreeMap<CfgNodeId, usize>,
    edge_visits: BTreeMap<CfgEdgeId, usize>,
}

impl AnalysisState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn ensure_entry_state(&mut self, node: CfgNodeId) -> &mut NodeState {
        self.nodes.entry(node).or_insert_with(NodeState::entry)
    }

    pub fn ensure_node_state(&mut self, node: CfgNodeId) -> &mut NodeState {
        self.nodes
            .entry(node)
            .or_insert_with(NodeState::unreachable)
    }

    pub fn node_state(&self, node: CfgNodeId) -> Option<&NodeState> {
        self.nodes.get(&node)
    }

    pub fn increment_node_visit(&mut self, node: CfgNodeId) -> usize {
        let count = self.node_visits.entry(node).or_default();
        *count += 1;
        *count
    }

    pub fn increment_edge_visit(&mut self, edge: CfgEdgeId) -> usize {
        let count = self.edge_visits.entry(edge).or_default();
        *count += 1;
        *count
    }

    pub fn node_visit_count(&self, node: CfgNodeId) -> usize {
        self.node_visits.get(&node).copied().unwrap_or(0)
    }

    pub fn edge_visit_count(&self, edge: CfgEdgeId) -> usize {
        self.edge_visits.get(&edge).copied().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::cfg::{CfgEdgeId, CfgNodeId};
    use crate::analysis::formula::{Term, Var};

    #[test]
    fn path_summary_refinement_conjoins_guards() {
        let mut summary = PathSummary::reachable();
        summary.refine(Formula::bool_var("p"));
        summary.refine(Formula::bool_var("q"));
        assert_eq!(
            summary.predicate(),
            &Formula::and(Formula::bool_var("p"), Formula::bool_var("q"))
        );
    }

    #[test]
    fn path_summary_join_disjoins_incoming_paths() {
        let mut summary = PathSummary::unreachable();
        summary.join(&PathSummary {
            predicate: Formula::bool_var("p"),
        });
        summary.join(&PathSummary {
            predicate: Formula::bool_var("q"),
        });
        assert_eq!(
            summary.predicate(),
            &Formula::or(Formula::bool_var("p"), Formula::bool_var("q"))
        );
    }

    #[test]
    fn tracked_facts_and_obligations_collapse_to_conjunctions() {
        let mut facts = TrackedFacts::default();
        facts.push(Formula::eq(Term::Var(Var::int("x")), Term::int(1)));
        facts.push(Formula::eq(Term::Var(Var::int("y")), Term::int(2)));
        let mut obligations = Obligations::default();
        obligations.push(Formula::bool_var("safe"));
        obligations.push(Formula::not(Formula::bool_var("bad")));

        assert_eq!(
            facts.collapse(),
            Formula::and(
                Formula::eq(Term::Var(Var::int("x")), Term::int(1)),
                Formula::eq(Term::Var(Var::int("y")), Term::int(2))
            )
        );
        assert_eq!(
            obligations.collapse(),
            Formula::and(
                Formula::bool_var("safe"),
                Formula::not(Formula::bool_var("bad"))
            )
        );
    }

    #[test]
    fn node_state_stores_summaries_facts_and_obligations() {
        let mut state = NodeState::entry();
        state.path_summary_mut().refine(Formula::bool_var("path"));
        state
            .facts_mut()
            .push(Formula::eq(Term::Var(Var::int("x")), Term::int(3)));
        state
            .obligations_mut()
            .push(Formula::not(Formula::bool_var("assert_ok")));

        assert_eq!(state.path_summary().predicate(), &Formula::bool_var("path"));
        assert_eq!(state.facts().formulas().len(), 1);
        assert_eq!(state.obligations().formulas().len(), 1);
    }

    #[test]
    fn analysis_state_tracks_nodes_and_visit_counters() {
        let mut state = AnalysisState::new();
        let entry = CfgNodeId(0);
        let edge = CfgEdgeId(0);
        assert_eq!(state.ensure_entry_state(entry), &NodeState::entry());
        assert_eq!(state.increment_node_visit(entry), 1);
        assert_eq!(state.increment_node_visit(entry), 2);
        assert_eq!(state.increment_edge_visit(edge), 1);
        assert_eq!(state.node_visit_count(entry), 2);
        assert_eq!(state.edge_visit_count(edge), 1);
        assert!(state.node_state(entry).is_some());
    }
}
