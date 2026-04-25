//! Minimal SMT wrapper for the reconstructed milestone.
//!
//! This module owns the raw Z3 interaction needed to lower `analysis::formula`
//! values into solver constraints. It is intentionally small: no paper-level
//! oracle policy lives here yet.

use crate::analysis::formula::{Formula, FormulaError, Rational, Sort, Term};
use std::collections::BTreeMap;
use z3::ast::{Bool, Int, Real};
use z3::{SatResult, Solver};

#[derive(Debug, Default)]
pub struct SmtScope {
    solver: Solver,
    bool_vars: BTreeMap<String, Bool>,
    int_vars: BTreeMap<String, Int>,
    real_vars: BTreeMap<String, Real>,
}

impl SmtScope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assert_formula(&mut self, formula: &Formula) -> Result<(), FormulaError> {
        formula.validate()?;
        let lowered = self.lower_formula(formula)?;
        self.solver.assert(&lowered);
        Ok(())
    }

    pub fn check(&self) -> SatResult {
        self.solver.check()
    }

    pub fn reset(&mut self) {
        self.solver.reset();
    }

    fn lower_formula(&mut self, formula: &Formula) -> Result<Bool, FormulaError> {
        match formula {
            Formula::True => Ok(Bool::from_bool(true)),
            Formula::False => Ok(Bool::from_bool(false)),
            Formula::Var(var) => match var.sort() {
                Sort::Bool => Ok(self.bool_var(var.name())),
                sort => Err(FormulaError::ExpectedBooleanSort { found: sort }),
            },
            Formula::Not(inner) => Ok(self.lower_formula(inner)?.not()),
            Formula::And(items) => {
                let lowered = items
                    .iter()
                    .map(|item| self.lower_formula(item))
                    .collect::<Result<Vec<_>, _>>()?;
                let refs = lowered.iter().collect::<Vec<_>>();
                Ok(Bool::and(&refs))
            }
            Formula::Or(items) => {
                let lowered = items
                    .iter()
                    .map(|item| self.lower_formula(item))
                    .collect::<Result<Vec<_>, _>>()?;
                let refs = lowered.iter().collect::<Vec<_>>();
                Ok(Bool::or(&refs))
            }
            Formula::Implies(lhs, rhs) => {
                Ok(self.lower_formula(lhs)?.implies(self.lower_formula(rhs)?))
            }
            Formula::Eq(lhs, rhs) => match (self.lower_term(lhs)?, self.lower_term(rhs)?) {
                (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => Ok(lhs.eq(&rhs)),
                (EncodedTerm::Real(lhs), EncodedTerm::Real(rhs)) => Ok(lhs.eq(&rhs)),
                (EncodedTerm::Int(_), EncodedTerm::Real(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Int,
                    right: Sort::Real,
                }),
                (EncodedTerm::Real(_), EncodedTerm::Int(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Real,
                    right: Sort::Int,
                }),
            },
            Formula::Lt(lhs, rhs) => {
                compare_terms(self.lower_term(lhs)?, self.lower_term(rhs)?, Comparison::Lt)
            }
            Formula::Le(lhs, rhs) => {
                compare_terms(self.lower_term(lhs)?, self.lower_term(rhs)?, Comparison::Le)
            }
            Formula::Gt(lhs, rhs) => {
                compare_terms(self.lower_term(lhs)?, self.lower_term(rhs)?, Comparison::Gt)
            }
            Formula::Ge(lhs, rhs) => {
                compare_terms(self.lower_term(lhs)?, self.lower_term(rhs)?, Comparison::Ge)
            }
        }
    }

    fn lower_term(&mut self, term: &Term) -> Result<EncodedTerm, FormulaError> {
        match term {
            Term::Var(var) => match var.sort() {
                Sort::Int => Ok(EncodedTerm::Int(self.int_var(var.name()))),
                Sort::Real => Ok(EncodedTerm::Real(self.real_var(var.name()))),
                Sort::Bool => Err(FormulaError::ExpectedNumericSort { found: Sort::Bool }),
            },
            Term::Int(value) => Ok(EncodedTerm::Int(Int::from_i64(*value))),
            Term::Real(value) => Ok(EncodedTerm::Real(self.real_constant(value))),
            Term::Add(lhs, rhs) => combine_terms(
                self.lower_term(lhs)?,
                self.lower_term(rhs)?,
                ArithmeticOp::Add,
            ),
            Term::Sub(lhs, rhs) => combine_terms(
                self.lower_term(lhs)?,
                self.lower_term(rhs)?,
                ArithmeticOp::Sub,
            ),
            Term::Mul(lhs, rhs) => combine_terms(
                self.lower_term(lhs)?,
                self.lower_term(rhs)?,
                ArithmeticOp::Mul,
            ),
            Term::Div(lhs, rhs) => match (self.lower_term(lhs)?, self.lower_term(rhs)?) {
                (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => {
                    Ok(EncodedTerm::Int(lhs.div(&rhs)))
                }
                (EncodedTerm::Real(lhs), EncodedTerm::Real(rhs)) => {
                    Ok(EncodedTerm::Real(lhs.div(&rhs)))
                }
                (EncodedTerm::Int(_), EncodedTerm::Real(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Int,
                    right: Sort::Real,
                }),
                (EncodedTerm::Real(_), EncodedTerm::Int(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Real,
                    right: Sort::Int,
                }),
            },
            Term::Neg(inner) => match self.lower_term(inner)? {
                EncodedTerm::Int(value) => Ok(EncodedTerm::Int(-value)),
                EncodedTerm::Real(value) => Ok(EncodedTerm::Real(-value)),
            },
        }
    }

    fn bool_var(&mut self, name: &str) -> Bool {
        self.bool_vars
            .entry(name.to_string())
            .or_insert_with(|| Bool::new_const(name))
            .clone()
    }

    fn int_var(&mut self, name: &str) -> Int {
        self.int_vars
            .entry(name.to_string())
            .or_insert_with(|| Int::new_const(name))
            .clone()
    }

    fn real_var(&mut self, name: &str) -> Real {
        self.real_vars
            .entry(name.to_string())
            .or_insert_with(|| Real::new_const(name))
            .clone()
    }

    fn real_constant(&self, value: &Rational) -> Real {
        Real::from_rational(value.numerator(), value.denominator())
    }
}

enum EncodedTerm {
    Int(Int),
    Real(Real),
}

enum Comparison {
    Lt,
    Le,
    Gt,
    Ge,
}

enum ArithmeticOp {
    Add,
    Sub,
    Mul,
}

fn combine_terms(
    lhs: EncodedTerm,
    rhs: EncodedTerm,
    op: ArithmeticOp,
) -> Result<EncodedTerm, FormulaError> {
    match (lhs, rhs) {
        (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => Ok(EncodedTerm::Int(match op {
            ArithmeticOp::Add => Int::add(&[&lhs, &rhs]),
            ArithmeticOp::Sub => Int::sub(&[&lhs, &rhs]),
            ArithmeticOp::Mul => Int::mul(&[&lhs, &rhs]),
        })),
        (EncodedTerm::Real(lhs), EncodedTerm::Real(rhs)) => Ok(EncodedTerm::Real(match op {
            ArithmeticOp::Add => Real::add(&[&lhs, &rhs]),
            ArithmeticOp::Sub => Real::sub(&[&lhs, &rhs]),
            ArithmeticOp::Mul => Real::mul(&[&lhs, &rhs]),
        })),
        (EncodedTerm::Int(_), EncodedTerm::Real(_)) => Err(FormulaError::MixedSorts {
            left: Sort::Int,
            right: Sort::Real,
        }),
        (EncodedTerm::Real(_), EncodedTerm::Int(_)) => Err(FormulaError::MixedSorts {
            left: Sort::Real,
            right: Sort::Int,
        }),
    }
}

fn compare_terms(
    lhs: EncodedTerm,
    rhs: EncodedTerm,
    comparison: Comparison,
) -> Result<Bool, FormulaError> {
    match (lhs, rhs) {
        (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => Ok(match comparison {
            Comparison::Lt => lhs.lt(&rhs),
            Comparison::Le => lhs.le(&rhs),
            Comparison::Gt => lhs.gt(&rhs),
            Comparison::Ge => lhs.ge(&rhs),
        }),
        (EncodedTerm::Real(lhs), EncodedTerm::Real(rhs)) => Ok(match comparison {
            Comparison::Lt => lhs.lt(&rhs),
            Comparison::Le => lhs.le(&rhs),
            Comparison::Gt => lhs.gt(&rhs),
            Comparison::Ge => lhs.ge(&rhs),
        }),
        (EncodedTerm::Int(_), EncodedTerm::Real(_)) => Err(FormulaError::MixedSorts {
            left: Sort::Int,
            right: Sort::Real,
        }),
        (EncodedTerm::Real(_), EncodedTerm::Int(_)) => Err(FormulaError::MixedSorts {
            left: Sort::Real,
            right: Sort::Int,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Formula, Term};

    #[test]
    fn basic_scope_usage_works() {
        let mut smt = SmtScope::new();
        smt.assert_formula(&Formula::eq(Term::var("x", Sort::Int), Term::int(2)))
            .unwrap();
        assert_eq!(smt.check(), SatResult::Sat);
    }
}
