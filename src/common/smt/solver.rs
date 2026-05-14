#![allow(dead_code)]

//! Minimal SMT wrapper for the reconstructed milestone.
//!
//! This module owns the raw Z3 interaction needed to lower `analysis::formula`
//! values into solver constraints. It is intentionally small:
//!
//! - variable and array caches live here;
//! - model rendering lives here;
//! - integer-array memory equalities are lowered here;
//! - paper-level decisions about when to ask SAT/validity questions do not.
//!
//! That policy split keeps `analysis::oracle` in charge of the proof/search
//! logic while `solver.rs` stays a mechanical lowering layer.

use crate::common::formula::{
    Formula, FormulaError, Memory, ModelValue, Rational, SmtModel, Sort, Term, Var,
};
use std::collections::BTreeMap;
use z3::ast::{Array, Bool, Int, Real};
use z3::{SatResult, Solver, Sort as Z3Sort};

/// One reusable Z3 scope plus cached variable declarations for the paper terms.
#[derive(Debug, Default)]
pub struct SmtScope {
    solver: Solver,
    bool_vars: BTreeMap<String, Bool>,
    int_vars: BTreeMap<String, Int>,
    real_vars: BTreeMap<String, Real>,
    memory_vars: BTreeMap<String, Array>,
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

    pub fn model_string(&self) -> Option<String> {
        self.solver.get_model().map(|model| model.to_string())
    }

    pub fn model_bindings(&self, extra_indices: &[i64]) -> Option<SmtModel> {
        let model = self.solver.get_model()?;
        let mut result = SmtModel::default();

        for (name, ast) in &self.bool_vars {
            if let Some(value) = model.eval(ast, true).and_then(|value| value.as_bool()) {
                result
                    .scalar
                    .push((Var::bool(name.clone()), ModelValue::Bool(value)));
            }
        }
        for (name, ast) in &self.int_vars {
            if let Some(value) = model.eval(ast, true).and_then(|value| value.as_i64()) {
                result
                    .scalar
                    .push((Var::int(name.clone()), ModelValue::Int(value)));
            }
        }
        for (name, ast) in &self.real_vars {
            if let Some((num, den)) = model.eval(ast, true).and_then(|value| value.as_rational()) {
                result.scalar.push((
                    Var::real(name.clone()),
                    ModelValue::Real(Rational::new(num, den)),
                ));
            }
        }

        let mut indices = vec![0];
        indices.extend_from_slice(extra_indices);
        indices.sort_unstable();
        indices.dedup();
        for (name, memory) in &self.memory_vars {
            let values = indices
                .iter()
                .filter_map(|index| {
                    let selected = memory.select(&Int::from_i64(*index)).as_int()?;
                    model.eval(&selected, true)?.as_i64()
                })
                .collect::<Vec<_>>();
            if let Some(first) = values.first().copied() {
                if values.iter().all(|value| *value == first) {
                    result.memory.push((
                        name.clone(),
                        ModelValue::ArrayDefault(Box::new(ModelValue::Int(first))),
                    ));
                } else {
                    for (index, value) in indices.iter().zip(values.iter()) {
                        result.scalar.push((
                            Var::int(format!("{name}[{index}]")),
                            ModelValue::Int(*value),
                        ));
                    }
                }
            }
        }

        Some(result)
    }

    pub fn reset(&mut self) {
        self.solver.reset();
    }

    pub fn formula_to_z3(&mut self, formula: &Formula) -> Result<Bool, FormulaError> {
        self.lower_formula(formula)
    }

    pub fn term_to_z3_int(&mut self, term: &Term) -> Result<Int, FormulaError> {
        match self.lower_term(term)? {
            EncodedTerm::Int(value) => Ok(value),
            EncodedTerm::Real(_) => Err(FormulaError::ExpectedIntegerSort { found: Sort::Real }),
        }
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
            Formula::MemoryEq(lhs, rhs) => Ok(self.lower_memory(lhs)?.eq(&self.lower_memory(rhs)?)),
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
            Term::BoolToInt(value) => {
                let condition = self.lower_formula(value)?;
                Ok(EncodedTerm::Int(
                    condition.ite(&Int::from_i64(1), &Int::from_i64(0)),
                ))
            }
            Term::Select(memory, index) => {
                let memory = self.lower_memory(memory)?;
                let index = match self.lower_term(index)? {
                    EncodedTerm::Int(index) => index,
                    EncodedTerm::Real(_) => {
                        return Err(FormulaError::ExpectedIntegerSort { found: Sort::Real });
                    }
                };
                Ok(EncodedTerm::Int(memory.select(&index).as_int().expect(
                    "int memory array select should lower to an int term",
                )))
            }
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

    fn lower_memory(&mut self, memory: &Memory) -> Result<Array, FormulaError> {
        match memory {
            Memory::Var(name) => Ok(self.memory_var(name)),
            Memory::Store(memory, index, value) => {
                let memory = self.lower_memory(memory)?;
                let index = match self.lower_term(index)? {
                    EncodedTerm::Int(index) => index,
                    EncodedTerm::Real(_) => {
                        return Err(FormulaError::ExpectedIntegerSort { found: Sort::Real });
                    }
                };
                let value = match self.lower_term(value)? {
                    EncodedTerm::Int(value) => value,
                    EncodedTerm::Real(_) => {
                        return Err(FormulaError::ExpectedIntegerSort { found: Sort::Real });
                    }
                };
                Ok(memory.store(&index, &value))
            }
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

    fn memory_var(&mut self, name: &str) -> Array {
        self.memory_vars
            .entry(name.to_string())
            .or_insert_with(|| Array::new_const(name, &Z3Sort::int(), &Z3Sort::int()))
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

pub fn formula_to_z3(scope: &mut SmtScope, formula: &Formula) -> Result<Bool, FormulaError> {
    scope.formula_to_z3(formula)
}

pub fn term_to_z3_int(scope: &mut SmtScope, term: &Term) -> Result<Int, FormulaError> {
    scope.term_to_z3_int(term)
}

pub fn quick_sat_check(condition: Bool) -> SatResult {
    let solver = Solver::new();
    solver.assert(&condition);
    solver.check()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::formula::{Formula, Memory, Term};

    #[test]
    fn basic_scope_usage_works() {
        let mut smt = SmtScope::new();
        smt.assert_formula(&Formula::eq(Term::var("x", Sort::Int), Term::int(2)))
            .unwrap();
        assert_eq!(smt.check(), SatResult::Sat);
    }

    #[test]
    fn memory_selects_and_stores_lower_to_z3_arrays() {
        let mut smt = SmtScope::new();
        smt.assert_formula(&Formula::eq(
            Term::select(
                Memory::store(Memory::var("mem0"), Term::int(0), Term::int(7)),
                Term::int(0),
            ),
            Term::int(7),
        ))
        .unwrap();
        assert_eq!(smt.check(), SatResult::Sat);
    }

    #[test]
    fn sat_queries_can_render_a_model() {
        let mut smt = SmtScope::new();
        smt.assert_formula(&Formula::eq(Term::var("x", Sort::Int), Term::int(9)))
            .unwrap();

        assert_eq!(smt.check(), SatResult::Sat);
        let model = smt
            .model_string()
            .expect("sat query should expose a solver model");
        assert!(model.contains("x"));
        assert!(model.contains("9"));
    }
}
