//! SMT-backed oracle queries over paper formulas and state carriers.
//!
//! This module owns satisfiability and implication checks for the paper-level
//! objects built in `formula.rs` and `state.rs`. It is the only analysis
//! module that should talk to the raw solver layer.

use crate::analysis::formula::{Formula, FormulaError};
use crate::analysis::state::{NodeState, PathSummary};
use crate::smt::solver::SmtScope;
use thiserror::Error;
use z3::SatResult;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Feasibility {
    Feasible,
    Infeasible,
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Validity {
    Valid,
    Invalid,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FeasibilityReport {
    /// Satisfiability status of the queried formula.
    pub feasibility: Feasibility,
    /// Optional model rendered by the raw solver for feasible/unknown queries.
    pub model: Option<String>,
}

#[derive(Debug, Default)]
pub struct Oracle;

#[derive(Debug, Error, Eq, PartialEq)]
pub enum OracleError {
    #[error(transparent)]
    Formula(#[from] FormulaError),
}

impl Oracle {
    pub fn new() -> Self {
        Self
    }

    pub fn feasibility(&self, formula: &Formula) -> Result<Feasibility, OracleError> {
        Ok(self.feasibility_with_model(formula)?.feasibility)
    }

    pub fn feasibility_with_model(
        &self,
        formula: &Formula,
    ) -> Result<FeasibilityReport, OracleError> {
        let mut scope = SmtScope::new();
        scope.assert_formula(formula)?;
        let result = scope.check();
        let model = matches!(result, SatResult::Sat | SatResult::Unknown)
            .then(|| scope.model_string())
            .flatten();
        Ok(FeasibilityReport {
            feasibility: match result {
                SatResult::Sat => Feasibility::Feasible,
                SatResult::Unsat => Feasibility::Infeasible,
                SatResult::Unknown => Feasibility::Unknown,
            },
            model,
        })
    }

    pub fn path_summary_feasibility(
        &self,
        path_summary: &PathSummary,
    ) -> Result<Feasibility, OracleError> {
        self.feasibility(path_summary.predicate())
    }

    pub fn state_feasibility(&self, state: &NodeState) -> Result<Feasibility, OracleError> {
        self.feasibility(&state.feasibility_formula())
    }

    pub fn state_feasibility_with_model(
        &self,
        state: &NodeState,
    ) -> Result<FeasibilityReport, OracleError> {
        self.feasibility_with_model(&state.feasibility_formula())
    }

    pub fn obligation_feasibility(&self, state: &NodeState) -> Result<Feasibility, OracleError> {
        self.feasibility(&state.obligation_query_formula())
    }

    pub fn implies(
        &self,
        assumptions: &Formula,
        conclusion: &Formula,
    ) -> Result<Validity, OracleError> {
        let counterexample = Formula::and(assumptions.clone(), Formula::not(conclusion.clone()));
        Ok(match self.feasibility(&counterexample)? {
            Feasibility::Feasible => Validity::Invalid,
            Feasibility::Infeasible => Validity::Valid,
            Feasibility::Unknown => Validity::Unknown,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Sort, Term, Var};

    #[test]
    fn formula_feasibility_distinguishes_sat_and_unsat() {
        let oracle = Oracle::new();

        let sat = oracle
            .feasibility(&Formula::eq(Term::var("x", Sort::Int), Term::int(2)))
            .unwrap();
        let unsat = oracle
            .feasibility(&Formula::and(
                Formula::eq(Term::var("x", Sort::Int), Term::int(0)),
                Formula::gt(Term::var("x", Sort::Int), Term::int(1)),
            ))
            .unwrap();

        assert_eq!(sat, Feasibility::Feasible);
        assert_eq!(unsat, Feasibility::Infeasible);
    }

    #[test]
    fn path_summary_feasibility_queries_the_summary_predicate() {
        let oracle = Oracle::new();
        let mut summary = PathSummary::reachable();
        summary.refine(Formula::bool_var("p"));
        summary.refine(Formula::not(Formula::bool_var("p")));

        assert_eq!(
            oracle.path_summary_feasibility(&summary).unwrap(),
            Feasibility::Infeasible
        );
    }

    #[test]
    fn state_feasibility_conjoins_path_summaries_and_facts() {
        let oracle = Oracle::new();
        let mut state = NodeState::entry();
        state.path_summary_mut().refine(Formula::bool_var("path"));
        state
            .facts_mut()
            .push(Formula::eq(Term::Var(Var::int("x")), Term::int(3)));
        state
            .facts_mut()
            .push(Formula::gt(Term::Var(Var::int("x")), Term::int(1)));

        assert_eq!(
            oracle.state_feasibility(&state).unwrap(),
            Feasibility::Feasible
        );
    }

    #[test]
    fn obligation_feasibility_includes_negated_assertions() {
        let oracle = Oracle::new();
        let mut state = NodeState::entry();
        state
            .facts_mut()
            .push(Formula::eq(Term::Var(Var::int("x")), Term::int(3)));
        state
            .obligations_mut()
            .push(Formula::gt(Term::Var(Var::int("x")), Term::int(4)));

        assert_eq!(
            oracle.obligation_feasibility(&state).unwrap(),
            Feasibility::Infeasible
        );
    }

    #[test]
    fn implication_checks_for_counterexample_feasibility() {
        let oracle = Oracle::new();
        let assumptions = Formula::eq(Term::var("x", Sort::Int), Term::int(3));

        assert_eq!(
            oracle
                .implies(
                    &assumptions,
                    &Formula::gt(Term::var("x", Sort::Int), Term::int(1))
                )
                .unwrap(),
            Validity::Valid
        );
        assert_eq!(
            oracle
                .implies(
                    &assumptions,
                    &Formula::gt(Term::var("x", Sort::Int), Term::int(4))
                )
                .unwrap(),
            Validity::Invalid
        );
    }

    #[test]
    fn feasibility_with_model_returns_a_model_for_sat_queries() {
        let oracle = Oracle::new();
        let report = oracle
            .feasibility_with_model(&Formula::eq(Term::var("x", Sort::Int), Term::int(11)))
            .unwrap();

        assert_eq!(report.feasibility, Feasibility::Feasible);
        let model = report.model.expect("sat query should expose a model");
        assert!(model.contains("x"));
        assert!(model.contains("11"));
    }
}
