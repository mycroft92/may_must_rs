#![allow(dead_code)]

//! Raw Z3 lowering layer — the only place in the codebase that touches Z3 ASTs
//! directly.
//!
//! # Design
//!
//! This module owns the mechanical translation from the analysis formula types
//! ([`Formula`], [`Term`], [`Memory`]) to Z3 AST nodes.  It is intentionally
//! kept small and policy-free:
//!
//! - Variable and array declarations are cached inside [`SmtScope`] so that
//!   the same Z3 variable is reused for every occurrence of a name.
//! - Model extraction and rendering live here so that callers never need to
//!   touch Z3's `Model` type.
//! - Memory regions are modelled as Z3 `Array(Int, Int)` — every named region
//!   gets its own array constant.  Array equality is expressed via Z3's
//!   built-in array equality.
//! - Decisions about *when* to ask satisfiability or validity questions are
//!   **not** made here; they belong in `oracle.rs`.
//!
//! # Scope / stack model
//!
//! [`SmtScope`] wraps a single Z3 `Solver` instance together with maps from
//! variable names to their cached Z3 AST nodes.  Because Z3's solver is
//! stateful (it accumulates asserted formulas), callers must call [`SmtScope::reset`]
//! to clear all assertions between independent queries.  There is no push/pop
//! mechanism — each query is performed in a fresh logical context by resetting
//! the solver and re-asserting from scratch.  The variable caches persist
//! across resets so that Z3 constant declarations are not duplicated.
//!
//! # Memory regions
//!
//! The adapter introduces named memory regions (`stack0`, `stack1`, `fn$__ext_N`,
//! …).  Each region is a `Memory::Var(name)` in the formula layer and becomes
//! a Z3 `Array(Int, Int)` constant here.  Store operations are modelled with
//! Z3's functional-update `store(array, index, value)` term.

use crate::formula::{
    Formula, FormulaError, Memory, ModelValue, Rational, SmtModel, Sort, Term, Var,
};
use std::collections::BTreeMap;
use z3::ast::{Array, Bool, Int, Real};
use z3::{SatResult, Solver, Sort as Z3Sort};

/// A Z3 solver instance together with cached variable declarations.
///
/// All variables are declared lazily on first use and stored in type-segregated
/// maps so that the same Z3 AST constant is returned for every reference to a
/// given name.  This is required by Z3: each call to `Bool::new_const(name)`
/// creates a *fresh* constant even if `name` matches an existing one, which
/// would silently produce incorrect results.
///
/// Use [`SmtScope::reset`] between logically independent queries.  The solver
/// state is cleared but the variable caches are retained.
///
/// # Scope / stack model
///
/// There is no explicit push/pop mechanism here. Instead:
/// - Each query calls [`SmtScope::reset`] to clear all assertions.
/// - Variable declarations (caches) persist across resets.
/// - Policy decisions about when to query belong in `oracle.rs`.
///
/// # Fields
///
/// * `solver` — the Z3 `Solver` instance (stateful, must be reset between queries).
/// * `bool_vars`, `int_vars`, `real_vars` — caches for scalar variables.
/// * `memory_vars` — caches for memory regions (`Array(Int, Int)`).
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

    /// Lower and assert a formula into the solver.
    ///
    /// The formula is validated (sort-checking) before lowering.  Returns an
    /// error if validation or lowering fails; the solver state is not modified
    /// in that case.
    ///
    /// # Idempotence
    ///
    /// Calling this multiple times with the same formula adds the formula
    /// multiple times to the solver (no de-duplication).
    pub fn assert_formula(&mut self, formula: &Formula) -> Result<(), FormulaError> {
        formula.validate()?;
        let lowered = self.lower_formula(formula)?;
        self.solver.assert(&lowered);
        Ok(())
    }

    /// Run the satisfiability check on all currently asserted formulas.
    ///
    /// Returns `SatResult::Sat`, `SatResult::Unsat`, or `SatResult::Unknown`.
    /// A `Sat` result makes the model accessible via [`SmtScope::model_bindings`]
    /// and [`SmtScope::model_string`].
    ///
    /// # Note
    ///
    /// This can be called multiple times on the same solver state; later calls
    /// may return different results if formulas are asserted between calls.
    pub fn check(&self) -> SatResult {
        self.solver.check()
    }

    /// Return the raw Z3 model as a string, or `None` if no model is available.
    ///
    /// This is a low-level diagnostic accessor; callers that need structured
    /// values should use [`SmtScope::model_bindings`] instead.
    ///
    /// # Availability
    ///
    /// Only available after a `Sat` result from [`SmtScope::check`].
    pub fn model_string(&self) -> Option<String> {
        self.solver.get_model().map(|model| model.to_string())
    }

    /// Extract a structured model from the solver after a `Sat` result.
    ///
    /// Concrete values are collected for all cached bool, int, and real
    /// variables.  Memory arrays are sampled at index `0` and any indices
    /// listed in `extra_indices`.  If all sampled values are equal the array is
    /// summarised as `ArrayDefault(value)`; otherwise individual `name[index]`
    /// bindings are emitted.
    ///
    /// Returns `None` if no model is available (e.g., the last [`SmtScope::check`]
    /// was `Unsat` or has not been called yet).
    ///
    /// # Parameters
    ///
    /// * `extra_indices` — memory array indices to sample (in addition to index 0).
    ///
    /// # Output
    ///
    /// An [`SmtModel`] with:
    /// - `scalar` — concrete values for all variables.
    /// - `memory` — summarised array values (default or individual indices).
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

    /// Clear all asserted formulas and the model, preparing the solver for a
    /// new independent query.  Variable caches are retained.
    ///
    /// # Semantics
    ///
    /// After reset:
    /// - All assertions are cleared.
    /// - The model (if any) becomes unavailable.
    /// - Variable declarations remain cached for reuse.
    /// - The solver is ready for a fresh set of assertions.
    pub fn reset(&mut self) {
        self.solver.reset();
    }

    /// Lower a [`Formula`] to a Z3 [`Bool`] AST without asserting it.
    ///
    /// Useful when the caller needs to combine several formula results before
    /// asserting (e.g., building an implication for a validity check in
    /// `oracle.rs`).
    ///
    /// # Use case
    ///
    /// This is the building block for constructing complex formulas such as
    /// `formula1.implies(formula2)` before asserting them.
    pub fn formula_to_z3(&mut self, formula: &Formula) -> Result<Bool, FormulaError> {
        self.lower_formula(formula)
    }

    /// Lower a [`Term`] that is expected to have integer sort to a Z3 [`Int`] AST.
    ///
    /// Returns an error if the term lowers to a real sort.
    ///
    /// # Purpose
    ///
    /// Used by callers (e.g., `oracle.rs`) that construct compound formulas
    /// and need access to Z3 integer terms before building comparisons.
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
            Term::Rem(lhs, rhs) => match (self.lower_term(lhs)?, self.lower_term(rhs)?) {
                (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => {
                    Ok(EncodedTerm::Int(lhs.rem(&rhs)))
                }
                (EncodedTerm::Int(_), EncodedTerm::Real(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Int,
                    right: Sort::Real,
                }),
                (EncodedTerm::Real(_), EncodedTerm::Int(_)) => Err(FormulaError::MixedSorts {
                    left: Sort::Real,
                    right: Sort::Int,
                }),
                (EncodedTerm::Real(_), EncodedTerm::Real(_)) => {
                    Err(FormulaError::ExpectedIntegerSort { found: Sort::Real })
                }
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

/// Convenience wrapper: lower a formula using `scope`.
///
/// Delegates to [`SmtScope::formula_to_z3`].  Exists so that callers holding a
/// mutable reference to `scope` can call this as a free function rather than
/// dereferencing `scope.formula_to_z3(...)`.
pub fn formula_to_z3(scope: &mut SmtScope, formula: &Formula) -> Result<Bool, FormulaError> {
    scope.formula_to_z3(formula)
}

/// Convenience wrapper: lower a term to a Z3 integer using `scope`.
///
/// Delegates to [`SmtScope::term_to_z3_int`].  Exists for the same reasons as
/// [`formula_to_z3`].
pub fn term_to_z3_int(scope: &mut SmtScope, term: &Term) -> Result<Int, FormulaError> {
    scope.term_to_z3_int(term)
}

/// Create a temporary single-use solver and check whether a condition is satisfiable.
///
/// Unlike [`SmtScope::check`] this does not accumulate state — the solver is
/// created and immediately discarded.  Suitable for one-off checks that do not
/// need model extraction.
///
/// # Use case
///
/// For lightweight feasibility checks where the overhead of managing a solver
/// instance is acceptable (e.g., in early filters before full analysis).
///
/// # Note
///
/// The passed [`Bool`] must have been lowered by a [`SmtScope`] instance
/// (or contain only literals and operations on globally-valid Z3 constants).
pub fn quick_sat_check(condition: Bool) -> SatResult {
    let solver = Solver::new();
    solver.assert(&condition);
    solver.check()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{Formula, Memory, Term};

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
