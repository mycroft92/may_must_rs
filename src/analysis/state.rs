//! Analysis-owned state carriers layered on top of the paper CFG.
//!
//! This module does not store the rule frame itself; `rules.rs` owns `Π_n`,
//! `Ω_n`, and `N_e`. What lives here are the executable-state pieces used by
//! the bounded checker and by witness replay:
//!
//! - accumulated path predicates
//! - asserted local facts
//! - pending obligations
//! - the current integer-array memory model and pointer bindings
//! - temporary visit counters for bounded exploration
//!
//! These carriers are deliberately operational rather than declarative. The
//! paper-rule frame itself lives in `rules.rs`; `state.rs` supports the bounded
//! executor, transfer interpretation, and witness replay.

use crate::analysis::cfg::{CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, Memory, Term, Var};
use std::collections::BTreeMap;

/// Accumulated path predicate for one symbolic frontier state.
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

    pub fn as_formula(&self) -> Formula {
        self.predicate.clone()
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

    pub fn clear(&mut self) {
        self.obligations.clear();
    }

    pub fn collapse(&self) -> Formula {
        Formula::and_all(self.obligations.clone())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointerValue {
    region: String,
    offset: Term,
}

impl PointerValue {
    pub fn new(region: impl Into<String>, offset: Term) -> Self {
        Self {
            region: region.into(),
            offset,
        }
    }

    pub fn region(&self) -> &str {
        &self.region
    }

    pub fn offset(&self) -> &Term {
        &self.offset
    }
}

/// Symbolic state carried by the bounded executor and witness replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeState {
    path_summary: PathSummary,
    facts: TrackedFacts,
    obligations: Obligations,
    memory_regions: BTreeMap<String, Memory>,
    pointers: BTreeMap<String, PointerValue>,
    memory_epoch: usize,
}

impl NodeState {
    pub fn entry() -> Self {
        Self {
            path_summary: PathSummary::reachable(),
            facts: TrackedFacts::default(),
            obligations: Obligations::default(),
            memory_regions: BTreeMap::new(),
            pointers: BTreeMap::new(),
            memory_epoch: 0,
        }
    }

    pub fn unreachable() -> Self {
        Self {
            path_summary: PathSummary::unreachable(),
            facts: TrackedFacts::default(),
            obligations: Obligations::default(),
            memory_regions: BTreeMap::new(),
            pointers: BTreeMap::new(),
            memory_epoch: 0,
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

    pub fn clear_obligations(&mut self) {
        self.obligations.clear();
    }

    pub fn bind_alloca_pointer(&mut self, target: impl Into<String>, region: impl Into<String>) {
        let target = target.into();
        let region = region.into();
        self.ensure_region(&region);
        self.pointers
            .insert(target, PointerValue::new(region, Term::int(0)));
    }

    pub fn bind_pointer_offset(
        &mut self,
        target: impl Into<String>,
        base: &str,
        offset: Term,
    ) -> PointerValue {
        let target = target.into();
        let base_pointer = self.resolve_pointer(base);
        let offset = if base_pointer.offset() == &Term::int(0) {
            offset
        } else {
            Term::add(base_pointer.offset().clone(), offset)
        };
        let resolved = PointerValue::new(base_pointer.region().to_string(), offset);
        self.pointers.insert(target, resolved.clone());
        resolved
    }

    pub fn load_from_pointer(&mut self, target: &Var, source: &str) {
        let pointer = self.resolve_pointer(source);
        let memory = self.current_memory(pointer.region()).clone();
        self.facts_mut().push(Formula::eq(
            Term::Var(target.clone()),
            Term::select(memory, pointer.offset().clone()),
        ));
    }

    pub fn store_to_pointer(&mut self, target: &str, value: Term) {
        let pointer = self.resolve_pointer(target);
        let next_memory = Memory::store(
            self.current_memory(pointer.region()).clone(),
            pointer.offset().clone(),
            value,
        );
        self.memory_regions
            .insert(pointer.region().to_string(), next_memory);
    }

    pub fn havoc_memory(&mut self) {
        self.memory_epoch += 1;
        let regions = self.memory_regions.keys().cloned().collect::<Vec<_>>();
        for region in regions {
            self.memory_regions
                .insert(region.clone(), Memory::var(self.memory_symbol(&region)));
        }
    }

    pub fn memory_summary(&self) -> String {
        if self.memory_regions.is_empty() {
            "[]".to_string()
        } else {
            let parts = self
                .memory_regions
                .iter()
                .map(|(region, memory)| format!("{region}={memory}"))
                .collect::<Vec<_>>();
            format!("[{}]", parts.join(", "))
        }
    }

    pub fn feasibility_formula(&self) -> Formula {
        Formula::and_all([self.path_summary.as_formula(), self.facts.collapse()])
    }

    pub fn obligation_query_formula(&self) -> Formula {
        Formula::and_all([self.feasibility_formula(), self.obligations.collapse()])
    }

    fn resolve_pointer(&mut self, name: &str) -> PointerValue {
        if let Some(pointer) = self.pointers.get(name) {
            return pointer.clone();
        }
        let region = format!("{name}$region");
        self.ensure_region(&region);
        let pointer = PointerValue::new(region, Term::int(0));
        self.pointers.insert(name.to_string(), pointer.clone());
        pointer
    }

    fn ensure_region(&mut self, region: &str) {
        if self.memory_regions.contains_key(region) {
            return;
        }
        self.memory_regions
            .insert(region.to_string(), Memory::var(self.memory_symbol(region)));
    }

    fn current_memory(&self, region: &str) -> &Memory {
        self.memory_regions
            .get(region)
            .expect("memory region should exist before use")
    }

    fn memory_symbol(&self, region: &str) -> String {
        format!("{region}$mem{}", self.memory_epoch)
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
    use crate::analysis::formula::{Memory, Term, Var};

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
        assert_eq!(
            state.feasibility_formula(),
            Formula::and(
                Formula::bool_var("path"),
                Formula::eq(Term::Var(Var::int("x")), Term::int(3))
            )
        );
        assert_eq!(
            state.obligation_query_formula(),
            Formula::and_all([
                Formula::bool_var("path"),
                Formula::eq(Term::Var(Var::int("x")), Term::int(3)),
                Formula::not(Formula::bool_var("assert_ok")),
            ])
        );
    }

    #[test]
    fn memory_regions_are_updated_and_havoced() {
        let mut state = NodeState::entry();
        state.bind_alloca_pointer("%ptr", "stack.ptr");
        state.store_to_pointer("%ptr", Term::int(7));
        state.load_from_pointer(&Var::int("%x"), "%ptr");

        assert_eq!(
            state.facts().collapse(),
            Formula::eq(
                Term::Var(Var::int("%x")),
                Term::select(
                    Memory::store(Memory::var("stack.ptr$mem0"), Term::int(0), Term::int(7),),
                    Term::int(0),
                ),
            )
        );

        state.havoc_memory();
        assert_eq!(state.memory_summary(), "[stack.ptr=stack.ptr$mem1]");
    }

    #[test]
    fn unknown_pointer_sources_are_treated_as_external_regions() {
        let mut state = NodeState::entry();
        state.store_to_pointer("%arg", Term::int(3));
        assert_eq!(
            state.memory_summary(),
            "[%arg$region=(store %arg$region$mem0 0 3)]"
        );
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
