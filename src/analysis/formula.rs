//! Formula vocabulary for paper predicates such as `Gamma_e`, `Pi_n`, and
//! obligations.
//!
//! This module is deliberately solver-independent. The only job here is to
//! model the paper's Boolean and arithmetic predicates with explicit sorts.

use std::fmt;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum Sort {
    Bool,
    Int,
    Real,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Var {
    name: String,
    sort: Sort,
}

impl Var {
    pub fn new(name: impl Into<String>, sort: Sort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    pub fn bool(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Bool)
    }

    pub fn int(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Int)
    }

    pub fn real(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Real)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "rational denominator must be non-zero");
        let sign = if den < 0 { -1 } else { 1 };
        let num = num * sign;
        let den = den.abs();
        let gcd = gcd_i64(num, den);
        Self {
            num: num / gcd,
            den: den / gcd,
        }
    }

    pub fn integer(value: i64) -> Self {
        Self::new(value, 1)
    }

    pub fn numerator(&self) -> i64 {
        self.num
    }

    pub fn denominator(&self) -> i64 {
        self.den
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    Var(Var),
    Int(i64),
    Real(Rational),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Div(Box<Term>, Box<Term>),
    Neg(Box<Term>),
}

impl Term {
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Self::Var(Var::new(name, sort))
    }

    pub fn int(value: i64) -> Self {
        Self::Int(value)
    }

    pub fn real(num: i64, den: i64) -> Self {
        Self::Real(Rational::new(num, den))
    }

    pub fn add(lhs: Term, rhs: Term) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }

    pub fn sub(lhs: Term, rhs: Term) -> Self {
        Self::Sub(Box::new(lhs), Box::new(rhs))
    }

    pub fn mul(lhs: Term, rhs: Term) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }

    pub fn div(lhs: Term, rhs: Term) -> Self {
        Self::Div(Box::new(lhs), Box::new(rhs))
    }

    pub fn neg(term: Term) -> Self {
        Self::Neg(Box::new(term))
    }

    pub fn sort(&self) -> Result<Sort, FormulaError> {
        match self {
            Term::Var(var) => {
                if var.sort() == Sort::Bool {
                    Err(FormulaError::ExpectedNumericSort { found: Sort::Bool })
                } else {
                    Ok(var.sort())
                }
            }
            Term::Int(_) => Ok(Sort::Int),
            Term::Real(_) => Ok(Sort::Real),
            Term::Add(lhs, rhs)
            | Term::Sub(lhs, rhs)
            | Term::Mul(lhs, rhs)
            | Term::Div(lhs, rhs) => unify_numeric_sorts(lhs.sort()?, rhs.sort()?),
            Term::Neg(term) => {
                let sort = term.sort()?;
                if sort == Sort::Bool {
                    Err(FormulaError::ExpectedNumericSort { found: sort })
                } else {
                    Ok(sort)
                }
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(var) => write!(f, "{var}"),
            Term::Int(value) => write!(f, "{value}"),
            Term::Real(value) => write!(f, "{value}"),
            Term::Add(lhs, rhs) => write!(f, "({lhs} + {rhs})"),
            Term::Sub(lhs, rhs) => write!(f, "({lhs} - {rhs})"),
            Term::Mul(lhs, rhs) => write!(f, "({lhs} * {rhs})"),
            Term::Div(lhs, rhs) => write!(f, "({lhs} / {rhs})"),
            Term::Neg(term) => write!(f, "(-{term})"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Formula {
    True,
    False,
    Var(Var),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Eq(Term, Term),
    Lt(Term, Term),
    Le(Term, Term),
    Gt(Term, Term),
    Ge(Term, Term),
}

pub type Predicate = Formula;

impl Formula {
    pub fn bool_var(name: impl Into<String>) -> Self {
        Self::Var(Var::bool(name))
    }

    pub fn not(formula: Formula) -> Self {
        Self::Not(Box::new(formula))
    }

    pub fn and_all<I>(formulas: I) -> Self
    where
        I: IntoIterator<Item = Formula>,
    {
        let mut items = Vec::new();
        for formula in formulas {
            match formula {
                Formula::True => {}
                Formula::And(inner) => items.extend(inner),
                other => items.push(other),
            }
        }
        match items.len() {
            0 => Formula::True,
            1 => items.into_iter().next().unwrap(),
            _ => Formula::And(items),
        }
    }

    pub fn and(lhs: Formula, rhs: Formula) -> Self {
        Self::and_all([lhs, rhs])
    }

    pub fn or_all<I>(formulas: I) -> Self
    where
        I: IntoIterator<Item = Formula>,
    {
        let mut items = Vec::new();
        for formula in formulas {
            match formula {
                Formula::False => {}
                Formula::Or(inner) => items.extend(inner),
                other => items.push(other),
            }
        }
        match items.len() {
            0 => Formula::False,
            1 => items.into_iter().next().unwrap(),
            _ => Formula::Or(items),
        }
    }

    pub fn or(lhs: Formula, rhs: Formula) -> Self {
        Self::or_all([lhs, rhs])
    }

    pub fn implies(lhs: Formula, rhs: Formula) -> Self {
        Self::Implies(Box::new(lhs), Box::new(rhs))
    }

    pub fn iff(lhs: Formula, rhs: Formula) -> Self {
        Formula::and(
            Formula::implies(lhs.clone(), rhs.clone()),
            Formula::implies(rhs, lhs),
        )
    }

    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Self::Eq(lhs, rhs)
    }

    pub fn lt(lhs: Term, rhs: Term) -> Self {
        Self::Lt(lhs, rhs)
    }

    pub fn le(lhs: Term, rhs: Term) -> Self {
        Self::Le(lhs, rhs)
    }

    pub fn gt(lhs: Term, rhs: Term) -> Self {
        Self::Gt(lhs, rhs)
    }

    pub fn ge(lhs: Term, rhs: Term) -> Self {
        Self::Ge(lhs, rhs)
    }

    pub fn validate(&self) -> Result<(), FormulaError> {
        match self {
            Formula::True | Formula::False => Ok(()),
            Formula::Var(var) => {
                if var.sort() == Sort::Bool {
                    Ok(())
                } else {
                    Err(FormulaError::ExpectedBooleanSort { found: var.sort() })
                }
            }
            Formula::Not(inner) => inner.validate(),
            Formula::And(items) | Formula::Or(items) => {
                for item in items {
                    item.validate()?;
                }
                Ok(())
            }
            Formula::Implies(lhs, rhs) => {
                lhs.validate()?;
                rhs.validate()
            }
            Formula::Eq(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                unify_numeric_sorts(lhs_sort, rhs_sort).map(|_| ())
            }
            Formula::Lt(lhs, rhs)
            | Formula::Le(lhs, rhs)
            | Formula::Gt(lhs, rhs)
            | Formula::Ge(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                unify_numeric_sorts(lhs_sort, rhs_sort).map(|_| ())
            }
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Var(var) => write!(f, "{var}"),
            Formula::Not(inner) => write!(f, "(!{inner})"),
            Formula::And(items) => write_joined(f, items, " && "),
            Formula::Or(items) => write_joined(f, items, " || "),
            Formula::Implies(lhs, rhs) => write!(f, "({lhs} => {rhs})"),
            Formula::Eq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
            Formula::Lt(lhs, rhs) => write!(f, "({lhs} < {rhs})"),
            Formula::Le(lhs, rhs) => write!(f, "({lhs} <= {rhs})"),
            Formula::Gt(lhs, rhs) => write!(f, "({lhs} > {rhs})"),
            Formula::Ge(lhs, rhs) => write!(f, "({lhs} >= {rhs})"),
        }
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum FormulaError {
    #[error("expected a Boolean sort but found {found}")]
    ExpectedBooleanSort { found: Sort },
    #[error("expected a numeric sort but found {found}")]
    ExpectedNumericSort { found: Sort },
    #[error("mixed sorts are not allowed: {left} vs {right}")]
    MixedSorts { left: Sort, right: Sort },
}

fn unify_numeric_sorts(lhs: Sort, rhs: Sort) -> Result<Sort, FormulaError> {
    if lhs == Sort::Bool {
        return Err(FormulaError::ExpectedNumericSort { found: lhs });
    }
    if rhs == Sort::Bool {
        return Err(FormulaError::ExpectedNumericSort { found: rhs });
    }
    if lhs != rhs {
        return Err(FormulaError::MixedSorts {
            left: lhs,
            right: rhs,
        });
    }
    Ok(lhs)
}

fn gcd_i64(lhs: i64, rhs: i64) -> i64 {
    let mut a = lhs.abs();
    let mut b = rhs.abs();
    while b != 0 {
        let tmp = a % b;
        a = b;
        b = tmp;
    }
    a.max(1)
}

fn write_joined(f: &mut fmt::Formatter<'_>, items: &[Formula], joiner: &str) -> fmt::Result {
    write!(f, "(")?;
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            write!(f, "{joiner}")?;
        }
        write!(f, "{item}")?;
    }
    write!(f, ")")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::solver::SmtScope;
    use z3::SatResult;

    #[test]
    fn sat_integer_constraint_lowering() {
        let formula = Formula::and(
            Formula::eq(Term::var("x", Sort::Int), Term::int(3)),
            Formula::gt(Term::var("x", Sort::Int), Term::int(1)),
        );
        let mut smt = SmtScope::new();
        smt.assert_formula(&formula).unwrap();
        assert_eq!(smt.check(), SatResult::Sat);
    }

    #[test]
    fn unsat_contradictory_constraint_lowering() {
        let formula = Formula::and(
            Formula::eq(Term::var("x", Sort::Int), Term::int(0)),
            Formula::gt(Term::var("x", Sort::Int), Term::int(2)),
        );
        let mut smt = SmtScope::new();
        smt.assert_formula(&formula).unwrap();
        assert_eq!(smt.check(), SatResult::Unsat);
    }

    #[test]
    fn boolean_implication_lowering() {
        let formula = Formula::and(
            Formula::bool_var("p"),
            Formula::implies(Formula::bool_var("p"), Formula::bool_var("q")),
        );
        let mut smt = SmtScope::new();
        smt.assert_formula(&formula).unwrap();
        smt.assert_formula(&Formula::not(Formula::bool_var("q")))
            .unwrap();
        assert_eq!(smt.check(), SatResult::Unsat);
    }

    #[test]
    fn reject_non_boolean_atoms() {
        let formula = Formula::Var(Var::int("x"));
        let mut smt = SmtScope::new();
        let error = smt.assert_formula(&formula).unwrap_err();
        assert_eq!(
            error,
            FormulaError::ExpectedBooleanSort { found: Sort::Int }
        );
    }

    #[test]
    fn reject_mixed_sort_equalities() {
        let formula = Formula::eq(Term::var("x", Sort::Int), Term::var("y", Sort::Real));
        let mut smt = SmtScope::new();
        let error = smt.assert_formula(&formula).unwrap_err();
        assert_eq!(
            error,
            FormulaError::MixedSorts {
                left: Sort::Int,
                right: Sort::Real,
            }
        );
    }
}
