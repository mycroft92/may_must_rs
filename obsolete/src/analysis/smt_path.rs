//! Cloneable path state for the SMT-backed analyzer.
//!
//! `StateEncoding` owns a concrete Z3 solver, which makes it the right object
//! for one encoding/check but the wrong object to clone into two branch paths.
//! This state keeps solver-independent bindings and path formulas. It creates
//! fresh `StateEncoding`s only when it needs to ask the solver about
//! feasibility or summary relations.

#![allow(dead_code)]

use crate::analysis::predicates::{Formula, IntTerm, PredicateResult};
use crate::analysis::state::SummaryPhase;
use std::collections::HashMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtPathState {
    function: String,
    int_bindings: HashMap<String, IntTerm>,
    bool_bindings: HashMap<String, Formula>,
    // Deliberate temporary simplification for the first executable SMT path:
    // memory here is a path-local map from a syntactic pointer key to one
    // integer term. This lets unoptimized `alloca`/`store`/`load` smoke tests
    // run, but it is not the final memory model. It does not model aliasing,
    // object identity, offsets, byte layout, arrays, structs, globals, heap
    // objects, or function-boundary memory summaries.
    memory_bindings: HashMap<String, IntTerm>,
    path_conditions: Vec<Formula>,
    return_value: Option<IntTerm>,
    trace: Vec<String>,
}

impl SmtPathState {
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            int_bindings: HashMap::new(),
            bool_bindings: HashMap::new(),
            memory_bindings: HashMap::new(),
            path_conditions: Vec::new(),
            return_value: None,
            trace: Vec::new(),
        }
    }

    /// Build an entry state whose formal parameters are summary pre-boundary
    /// symbols. The first implementation assumes integer parameters.
    pub fn with_formal_params(function: impl Into<String>, params: &[String]) -> Self {
        let mut state = Self::new(function);
        for (index, param) in params.iter().enumerate() {
            state.bind_int(param, IntTerm::summary_param(SummaryPhase::Pre, index));
        }
        state
    }

    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn int_bindings(&self) -> &HashMap<String, IntTerm> {
        &self.int_bindings
    }

    pub fn bool_bindings(&self) -> &HashMap<String, Formula> {
        &self.bool_bindings
    }

    pub fn memory_bindings(&self) -> &HashMap<String, IntTerm> {
        &self.memory_bindings
    }

    pub fn path_conditions(&self) -> &[Formula] {
        &self.path_conditions
    }

    pub fn trace(&self) -> &[String] {
        &self.trace
    }

    pub fn push_trace(&mut self, step: impl Into<String>) {
        self.trace.push(step.into());
    }

    pub fn bind_int(&mut self, name: impl AsRef<str>, value: IntTerm) {
        self.int_bindings.insert(normalize_name(name), value);
    }

    pub fn bind_bool(&mut self, name: impl AsRef<str>, value: Formula) {
        self.bool_bindings.insert(normalize_name(name), value);
    }

    pub fn bind_memory_int(&mut self, ptr: impl AsRef<str>, value: IntTerm) {
        self.memory_bindings.insert(normalize_name(ptr), value);
    }

    pub fn int_value(&self, name: impl AsRef<str>) -> IntTerm {
        let name = normalize_name(name);
        self.int_bindings
            .get(&name)
            .cloned()
            .unwrap_or_else(|| IntTerm::ssa(name))
    }

    pub fn bool_value(&self, name: impl AsRef<str>) -> Formula {
        let name = normalize_name(name);
        self.bool_bindings
            .get(&name)
            .cloned()
            .unwrap_or_else(|| Formula::bool_ssa(name))
    }

    pub fn memory_int_value(&self, ptr: impl AsRef<str>) -> Option<IntTerm> {
        self.memory_bindings.get(&normalize_name(ptr)).cloned()
    }

    pub fn assume(&mut self, condition: Formula) {
        match condition {
            Formula::True => {}
            Formula::False => self.path_conditions.push(Formula::False),
            other if !self.path_conditions.iter().any(|known| known == &other) => {
                self.path_conditions.push(other);
            }
            _ => {}
        }
    }

    pub fn path_condition(&self) -> Formula {
        Formula::and(self.path_conditions.clone())
    }

    pub fn is_feasible(&self) -> PredicateResult<bool> {
        self.path_condition().is_satisfiable_in(&self.function)
    }

    pub fn fork_with_assumption(&self, condition: Formula) -> PredicateResult<Option<Self>> {
        let mut forked = self.clone();
        forked.assume(condition);
        if forked.is_feasible()? {
            Ok(Some(forked))
        } else {
            Ok(None)
        }
    }

    pub fn bind_return_int(&mut self, value: IntTerm) {
        self.return_value = Some(value);
    }

    pub fn return_value(&self) -> Option<&IntTerm> {
        self.return_value.as_ref()
    }

    /// Build the scalar return part of a function-summary relation:
    ///
    /// ```text
    /// post.ret == returned_term
    /// ```
    pub fn return_summary_relation(&self) -> Option<Formula> {
        self.return_value
            .as_ref()
            .map(|value| Formula::eq(IntTerm::summary_return(SummaryPhase::Post), value.clone()))
    }
}

fn normalize_name(name: impl AsRef<str>) -> String {
    let name = name.as_ref();
    if name.starts_with('%') {
        name.to_string()
    } else {
        format!("%{name}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formal_params_are_pre_boundary_terms() {
        let params = vec!["%x".to_string(), "%y".to_string()];
        let state = SmtPathState::with_formal_params("sum", &params);

        assert_eq!(
            state.int_value("%x"),
            IntTerm::summary_param(SummaryPhase::Pre, 0)
        );
        assert_eq!(
            state.int_value("%y"),
            IntTerm::summary_param(SummaryPhase::Pre, 1)
        );
    }

    #[test]
    fn branch_fork_prunes_infeasible_assumption() {
        let mut state = SmtPathState::new("main");
        state.bind_int("%x", IntTerm::int(4));

        let feasible = state
            .fork_with_assumption(Formula::eq(state.int_value("%x"), IntTerm::int(4)))
            .unwrap();
        let infeasible = state
            .fork_with_assumption(Formula::eq(state.int_value("%x"), IntTerm::int(5)))
            .unwrap();

        assert!(feasible.is_some());
        assert!(infeasible.is_none());
    }

    #[test]
    fn return_summary_relation_uses_post_return_boundary() {
        let mut state = SmtPathState::with_formal_params("inc", &["%x".to_string()]);
        let ret = IntTerm::add(state.int_value("%x"), IntTerm::int(1));
        state.bind_return_int(ret);

        let relation = state.return_summary_relation().unwrap();
        let param = IntTerm::summary_param(SummaryPhase::Pre, 0);
        let post_ret = IntTerm::summary_return(SummaryPhase::Post);

        assert_eq!(
            relation
                .entails_in(&Formula::gt(post_ret, param), "inc")
                .unwrap(),
            true
        );
    }
}
