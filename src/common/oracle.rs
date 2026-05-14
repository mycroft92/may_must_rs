#![allow(dead_code)]

use crate::common::formula::{collect_select_indices, Formula, FormulaError, SmtModel};
use crate::common::smt::solver::SmtScope;
use crate::may_must_analysis::chc::{ChcSession, HornModel};
use crate::may_must_analysis::node_summary::NodeSummary;
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
    pub feasibility: Feasibility,
    pub model: Option<SmtModel>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Oracle;

#[derive(Debug, thiserror::Error)]
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
        let indices = collect_select_indices(formula);
        let report = match scope.check() {
            SatResult::Sat => FeasibilityReport {
                feasibility: Feasibility::Feasible,
                model: scope.model_bindings(&indices),
            },
            SatResult::Unsat => FeasibilityReport {
                feasibility: Feasibility::Infeasible,
                model: None,
            },
            SatResult::Unknown => FeasibilityReport {
                feasibility: Feasibility::Unknown,
                model: scope.model_bindings(&indices),
            },
        };
        Ok(report)
    }

    pub fn check_summary(&self, summary: &NodeSummary) -> Result<FeasibilityReport, OracleError> {
        self.feasibility_with_model(&summary.combined())
    }

    pub fn implies(
        &self,
        assumptions: &Formula,
        conclusion: &Formula,
    ) -> Result<Validity, OracleError> {
        let counterexample = Formula::and(assumptions.clone(), Formula::not(conclusion.clone()));
        let result = match self.feasibility(&counterexample)? {
            Feasibility::Infeasible => Validity::Valid,
            Feasibility::Feasible => Validity::Invalid,
            Feasibility::Unknown => Validity::Unknown,
        };
        Ok(result)
    }

    pub fn check_chc_property(
        &self,
        model: &HornModel,
        callee_models: &[HornModel],
        property: &Formula,
    ) -> Result<Validity, OracleError> {
        let mut models = callee_models.to_vec();
        models.push(model.clone());
        let session = ChcSession::new(&models);
        Ok(session.check_property(&model.function, model, property))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::CfgNodeId;
    use crate::common::formula::{Sort, Term};

    #[test]
    fn feasibility_sat_formula() {
        let oracle = Oracle::new();
        let formula = Formula::eq(Term::var("x", Sort::Int), Term::int(1));
        let report = oracle.feasibility_with_model(&formula).unwrap();
        assert_eq!(report.feasibility, Feasibility::Feasible);
        assert!(report.model.is_some());
    }

    #[test]
    fn feasibility_unsat_formula() {
        let oracle = Oracle::new();
        let formula = Formula::and(
            Formula::eq(Term::var("x", Sort::Int), Term::int(1)),
            Formula::eq(Term::var("x", Sort::Int), Term::int(2)),
        );
        let report = oracle.feasibility_with_model(&formula).unwrap();
        assert_eq!(report.feasibility, Feasibility::Infeasible);
        assert!(report.model.is_none());
    }

    #[test]
    fn implication_validity() {
        let oracle = Oracle::new();
        let assumptions = Formula::eq(Term::var("x", Sort::Int), Term::int(1));
        let conclusion = Formula::le(Term::var("x", Sort::Int), Term::int(1));
        assert_eq!(
            oracle.implies(&assumptions, &conclusion).unwrap(),
            Validity::Valid
        );
    }

    #[test]
    fn check_summary_uses_combined_formula() {
        let oracle = Oracle::new();
        let summary = NodeSummary {
            node: CfgNodeId(0),
            reach: Formula::True,
            state: Formula::False,
        };
        let report = oracle.check_summary(&summary).unwrap();
        assert_eq!(report.feasibility, Feasibility::Infeasible);
    }
}
