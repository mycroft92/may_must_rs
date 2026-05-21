//! SMT query boundary for the bidirectional may/must analysis.
//!
//! This module is the **only** place where Z3 (via [`SmtScope`]) is invoked.  All other
//! analysis code must go through the [`Oracle`] struct rather than creating solver
//! scopes directly.  This keeps the policy about how SMT results are interpreted
//! (Feasible/Infeasible/Unknown) in one place and makes it straightforward to swap
//! solvers or add caching.
//!
//! # Query types
//!
//! The analysis relies on two kinds of SMT queries:
//!
//! - **Feasibility** ([`Oracle::feasibility`] / [`Oracle::feasibility_with_model`]):
//!   asks *"does there exist an assignment that satisfies this formula?"*  In the
//!   analysis context this answers *"is there a reachable execution that violates the
//!   assertion?"* – a `Feasible` answer means a potential counterexample exists, while
//!   `Infeasible` means the formula (typically `reach ∧ state`) is unsatisfiable and
//!   the assertion is verified.
//!
//! - **Implication / Validity** ([`Oracle::implies`]):
//!   asks *"does `assumptions` entail `conclusion`?"*  Used to check whether a
//!   candidate loop invariant actually holds at all exit edges, i.e. whether
//!   `invariant ∧ exit_condition → postcondition`.
//!
//! # Return value conventions
//!
//! [`Feasibility::Unknown`] and [`Validity::Unknown`] are returned when Z3 reports
//! `unknown` (e.g. due to timeout or non-linear arithmetic).  Callers must treat
//! `Unknown` as a **non-result** and fall back to a conservative (unsound-towards-
//! `Verified`) decision – typically reporting `UNKNOWN` to the user.

#![allow(dead_code)]

use crate::analysis::backward::node_summary::NodeSummary;
use crate::formula::{collect_select_indices, Formula, FormulaError, SmtModel};
use crate::smt::solver::SmtScope;
use z3::SatResult;

/// Whether a formula has a satisfying assignment under the SMT solver.
///
/// `Feasible` means Z3 found a model (a potential counterexample path exists).
/// `Infeasible` means Z3 proved unsatisfiability (the path is impossible; the
/// assertion is verified if the formula was `reach ∧ state`).
/// `Unknown` means Z3 could not determine satisfiability; treat as inconclusive.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Feasibility {
    Feasible,
    Infeasible,
    Unknown,
}

/// Whether `assumptions → conclusion` is universally valid.
///
/// `Valid` means no counterexample exists (the implication holds for all inputs).
/// `Invalid` means Z3 found an assignment where `assumptions` holds but `conclusion`
/// does not.  `Unknown` means the solver timed out or returned inconclusive.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Validity {
    Valid,
    Invalid,
    Unknown,
}

/// The result of a feasibility query, optionally including a concrete witness.
///
/// When `feasibility` is `Feasible` or `Unknown` the solver may produce a partial model
/// (variable assignments) that is useful for counterexample reporting.  `model` is `None`
/// when the formula is unsatisfiable or when the solver did not produce bindings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FeasibilityReport {
    pub feasibility: Feasibility,
    pub model: Option<SmtModel>,
}

/// Stateless SMT query dispatcher.
///
/// `Oracle` is a zero-sized type that acts as a namespace for all SMT queries.  Being
/// stateless means it can be freely cloned or constructed anywhere without coordination,
/// and every query opens and closes its own Z3 scope.  If query-level caching is ever
/// needed it should be added here without changing the call sites.
#[derive(Clone, Copy, Debug, Default)]
pub struct Oracle;

/// Errors that can occur while preparing or dispatching an SMT query.
///
/// Currently the only failure mode is a [`FormulaError`] during formula-to-Z3 lowering
/// (e.g. a sort mismatch that was not caught at construction time).
#[derive(Debug, thiserror::Error)]
pub enum OracleError {
    #[error(transparent)]
    Formula(#[from] FormulaError),
}

impl Oracle {
    /// Creates a new Oracle instance.  Because `Oracle` is zero-sized this is equivalent
    /// to [`Oracle::default`].
    pub fn new() -> Self {
        Self
    }

    /// Tests whether `formula` is satisfiable, discarding any witness model.
    ///
    /// Convenience wrapper around [`Oracle::feasibility_with_model`] for callers that only
    /// need the yes/no/unknown answer and do not need variable bindings for reporting.
    pub fn feasibility(&self, formula: &Formula) -> Result<Feasibility, OracleError> {
        Ok(self.feasibility_with_model(formula)?.feasibility)
    }

    /// Tests whether `formula` is satisfiable and returns a model when one is available.
    ///
    /// Opens a fresh Z3 scope, asserts `formula`, and calls `check()`.  Select-expression
    /// indices present in the formula are collected upfront so the model extraction can
    /// populate concrete array-read results.
    ///
    /// This is the primary entry point used by [`backward.rs`] to check whether
    /// `reach ∧ state` is feasible at the CFG entry – infeasibility means the assertion
    /// is verified on all reachable paths.
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

    /// Checks whether the combined `reach ∧ state` formula of a [`NodeSummary`] is feasible.
    ///
    /// `reach` overapproximates the set of reachable states at the node; `state` encodes
    /// the conditions under which the assertion obligation can be violated.  Their
    /// conjunction being infeasible means no reachable execution can violate the assertion
    /// at this node – i.e. the node is verified.
    pub fn check_summary(&self, summary: &NodeSummary) -> Result<FeasibilityReport, OracleError> {
        self.feasibility_with_model(&summary.combined())
    }

    /// Checks whether `assumptions → conclusion` is valid (universally true).
    ///
    /// Internally this is reduced to a *refutation* query: if `assumptions ∧ ¬conclusion`
    /// is infeasible then the implication holds.  This avoids introducing a universal
    /// quantifier in Z3.
    ///
    /// Typical use: checking that a candidate loop invariant `I` satisfies exit closure,
    /// i.e. `I ∧ ¬loop_condition → postcondition`.
    pub fn implies(
        &self,
        assumptions: &Formula,
        conclusion: &Formula,
    ) -> Result<Validity, OracleError> {
        let (validity, _) = self.implies_with_model(assumptions, conclusion)?;
        Ok(validity)
    }

    /// Returns `true` if `formula` is semantically unsatisfiable (equivalent to `False`).
    ///
    /// A candidate that is semantically False vacuously passes initiation, inductiveness,
    /// and exit closure (all checks become infeasible), producing a spuriously accepted
    /// invariant.  Use this as a pre-check before the three-part invariant test.
    ///
    /// Returns `false` conservatively when the solver returns `Unknown`.
    pub fn is_contradiction(&self, formula: &Formula) -> Result<bool, OracleError> {
        Ok(self.feasibility(formula)? == Feasibility::Infeasible)
    }

    /// Like [`Oracle::implies`] but also returns a counterexample model when the
    /// implication does not hold.
    ///
    /// The model witnesses a state where `assumptions` holds but `conclusion` does
    /// not — useful as an ICE implication example for loop invariant synthesis.
    pub fn implies_with_model(
        &self,
        assumptions: &Formula,
        conclusion: &Formula,
    ) -> Result<(Validity, Option<SmtModel>), OracleError> {
        let counterexample = Formula::and(assumptions.clone(), Formula::not(conclusion.clone()));
        let report = self.feasibility_with_model(&counterexample)?;
        let validity = match report.feasibility {
            Feasibility::Infeasible => Validity::Valid,
            Feasibility::Feasible => Validity::Invalid,
            Feasibility::Unknown => Validity::Unknown,
        };
        Ok((validity, report.model))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::CfgNodeId;
    use crate::formula::{Sort, Term};

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
