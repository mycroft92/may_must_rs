#![allow(dead_code)]

use crate::common::formula::{Formula, Sort, Term, Var};
use crate::common::oracle::Validity;
use crate::common::smt::solver::SmtScope;
use z3::SatResult;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallRef {
    pub callee: String,
    pub actual_args: Vec<Term>,
    pub result_var: Var,
    pub result_sort: Sort,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HornModel {
    pub function: String,
    pub params: Vec<Var>,
    pub retval_var: Var,
    pub summary_formula: Formula,
    pub call_refs: Vec<CallRef>,
}

#[derive(Default)]
pub struct ChcSession {
    models: Vec<HornModel>,
}

impl ChcSession {
    pub fn new(models: &[HornModel]) -> Self {
        Self {
            models: models.to_vec(),
        }
    }

    pub fn check_property(
        &self,
        function: &str,
        model: &HornModel,
        property: &Formula,
    ) -> Validity {
        let summary = self
            .models
            .iter()
            .find(|candidate| candidate.function == function)
            .map(|candidate| candidate.summary_formula.clone())
            .unwrap_or_else(|| model.summary_formula.clone());
        let mut scope = SmtScope::new();
        if scope
            .assert_formula(&Formula::and(summary, Formula::not(property.clone())))
            .is_err()
        {
            return Validity::Unknown;
        }
        match scope.check() {
            SatResult::Unsat => Validity::Valid,
            SatResult::Sat => Validity::Invalid,
            SatResult::Unknown => Validity::Unknown,
        }
    }
}

pub fn default_property_templates(retval_name: &str) -> Vec<Formula> {
    let retval = Term::Var(Var::int(retval_name));
    vec![
        Formula::ge(retval.clone(), Term::int(0)),
        Formula::le(retval.clone(), Term::int(0)),
        Formula::gt(retval.clone(), Term::int(-1)),
        Formula::lt(retval, Term::int(1)),
    ]
}

pub fn param_relative_templates(retval_name: &str, params: &[Var]) -> Vec<Formula> {
    let retval = Term::Var(Var::int(retval_name));
    let mut formulas = Vec::new();
    for param in params.iter().filter(|param| param.sort() == Sort::Int) {
        let term = Term::Var(param.clone());
        formulas.push(Formula::ge(retval.clone(), term.clone()));
        formulas.push(Formula::ge(retval.clone(), Term::neg(term.clone())));
        formulas.push(Formula::eq(retval.clone(), term));
    }
    formulas
}

pub fn solve_loop_chc(
    counter: Var,
    bound: Var,
    init: Option<i64>,
    increment: i64,
    violation: Option<Formula>,
) -> Option<Formula> {
    let counter_term = Term::Var(counter);
    let bound_term = Term::Var(bound);
    let lower = init.map(|value| Formula::ge(counter_term.clone(), Term::int(value)));
    let upper = if increment >= 0 {
        Some(Formula::le(counter_term, bound_term))
    } else {
        None
    };
    let mut parts = Vec::new();
    if let Some(lower) = lower {
        parts.push(lower);
    }
    if let Some(upper) = upper {
        parts.push(upper);
    }
    if let Some(violation) = violation {
        if violation == Formula::False {
            return Some(Formula::and_all(parts));
        }
    }
    if parts.is_empty() {
        None
    } else {
        Some(Formula::and_all(parts))
    }
}
