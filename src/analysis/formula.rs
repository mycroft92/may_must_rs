#![allow(dead_code)]

use std::cmp::Ordering;
use std::fmt;
use thiserror::Error;

pub type SmtModel = String;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "rational denominator cannot be zero");
        let mut num = num;
        let mut den = den;
        if den < 0 {
            num = -num;
            den = -den;
        }
        let g = gcd(num, den);
        Self {
            num: num / g,
            den: den / g,
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

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.num * other.den).cmp(&(other.num * self.den))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Memory {
    Var(String),
    Store(Box<Memory>, Box<Term>, Box<Term>),
}

impl Memory {
    pub fn var(name: impl Into<String>) -> Self {
        Memory::Var(name.into())
    }

    pub fn store(memory: Memory, index: Term, value: Term) -> Self {
        Memory::Store(Box::new(memory), Box::new(index), Box::new(value))
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Memory::Var(name) => write!(f, "{name}"),
            Memory::Store(mem, idx, val) => write!(f, "store({mem}, {idx}, {val})"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Var(Var),
    Int(i64),
    Real(Rational),
    BoolToInt(Box<Formula>),
    Select(Box<Memory>, Box<Term>),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Div(Box<Term>, Box<Term>),
    Neg(Box<Term>),
}

impl Term {
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Term::Var(Var::new(name, sort))
    }

    pub fn int(value: i64) -> Self {
        Term::Int(value)
    }

    pub fn real(value: Rational) -> Self {
        Term::Real(value)
    }

    pub fn bool_to_int(value: Formula) -> Self {
        Term::BoolToInt(Box::new(value))
    }

    pub fn select(memory: Memory, index: Term) -> Self {
        Term::Select(Box::new(memory), Box::new(index))
    }

    pub fn add(lhs: Term, rhs: Term) -> Self {
        Term::Add(Box::new(lhs), Box::new(rhs))
    }

    pub fn sub(lhs: Term, rhs: Term) -> Self {
        Term::Sub(Box::new(lhs), Box::new(rhs))
    }

    pub fn mul(lhs: Term, rhs: Term) -> Self {
        Term::Mul(Box::new(lhs), Box::new(rhs))
    }

    pub fn div(lhs: Term, rhs: Term) -> Self {
        Term::Div(Box::new(lhs), Box::new(rhs))
    }

    pub fn neg(inner: Term) -> Self {
        Term::Neg(Box::new(inner))
    }

    pub fn sort(&self) -> Result<Sort, FormulaError> {
        match self {
            Term::Var(var) => Ok(var.sort()),
            Term::Int(_) => Ok(Sort::Int),
            Term::Real(_) => Ok(Sort::Real),
            Term::BoolToInt(value) => {
                value.validate()?;
                Ok(Sort::Int)
            }
            Term::Select(_, index) => {
                let index_sort = index.sort()?;
                if index_sort != Sort::Int {
                    return Err(FormulaError::ExpectedIntegerSort { found: index_sort });
                }
                Ok(Sort::Int)
            }
            Term::Add(lhs, rhs)
            | Term::Sub(lhs, rhs)
            | Term::Mul(lhs, rhs)
            | Term::Div(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    return Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    });
                }
                if lhs_sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(lhs_sort)
            }
            Term::Neg(inner) => {
                let sort = inner.sort()?;
                if sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(sort)
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
            Term::BoolToInt(value) => write!(f, "bool_to_int({value})"),
            Term::Select(memory, index) => write!(f, "select({memory}, {index})"),
            Term::Add(lhs, rhs) => write!(f, "({lhs} + {rhs})"),
            Term::Sub(lhs, rhs) => write!(f, "({lhs} - {rhs})"),
            Term::Mul(lhs, rhs) => write!(f, "({lhs} * {rhs})"),
            Term::Div(lhs, rhs) => write!(f, "({lhs} / {rhs})"),
            Term::Neg(inner) => write!(f, "(-{inner})"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Formula {
    True,
    False,
    Var(Var),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Eq(Term, Term),
    MemoryEq(Memory, Memory),
    Lt(Term, Term),
    Le(Term, Term),
    Gt(Term, Term),
    Ge(Term, Term),
}

impl Formula {
    pub fn bool_var(name: impl Into<String>) -> Self {
        Formula::Var(Var::bool(name))
    }

    pub fn not(inner: Formula) -> Self {
        Formula::Not(Box::new(inner))
    }

    pub fn and(lhs: Formula, rhs: Formula) -> Self {
        Formula::And(vec![lhs, rhs]).simplify()
    }

    pub fn and_many(items: impl IntoIterator<Item = Formula>) -> Self {
        Formula::And(items.into_iter().collect()).simplify()
    }

    pub fn or(lhs: Formula, rhs: Formula) -> Self {
        Formula::Or(vec![lhs, rhs]).simplify()
    }

    pub fn or_many(items: impl IntoIterator<Item = Formula>) -> Self {
        Formula::Or(items.into_iter().collect()).simplify()
    }

    pub fn implies(lhs: Formula, rhs: Formula) -> Self {
        Formula::Implies(Box::new(lhs), Box::new(rhs)).simplify()
    }

    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Formula::Eq(lhs, rhs)
    }

    pub fn memory_eq(lhs: Memory, rhs: Memory) -> Self {
        Formula::MemoryEq(lhs, rhs)
    }

    pub fn lt(lhs: Term, rhs: Term) -> Self {
        Formula::Lt(lhs, rhs)
    }

    pub fn le(lhs: Term, rhs: Term) -> Self {
        Formula::Le(lhs, rhs)
    }

    pub fn gt(lhs: Term, rhs: Term) -> Self {
        Formula::Gt(lhs, rhs)
    }

    pub fn ge(lhs: Term, rhs: Term) -> Self {
        Formula::Ge(lhs, rhs)
    }

    pub fn validate(&self) -> Result<(), FormulaError> {
        match self {
            Formula::True | Formula::False => Ok(()),
            Formula::Var(var) => {
                if var.sort() != Sort::Bool {
                    Err(FormulaError::ExpectedBooleanSort { found: var.sort() })
                } else {
                    Ok(())
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
                rhs.validate()?;
                Ok(())
            }
            Formula::Eq(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    })
                } else if lhs_sort == Sort::Bool {
                    Err(FormulaError::ExpectedNumericSort { found: Sort::Bool })
                } else {
                    Ok(())
                }
            }
            Formula::MemoryEq(lhs, rhs) => {
                validate_memory(lhs)?;
                validate_memory(rhs)?;
                Ok(())
            }
            Formula::Lt(lhs, rhs)
            | Formula::Le(lhs, rhs)
            | Formula::Gt(lhs, rhs)
            | Formula::Ge(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    return Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    });
                }
                if lhs_sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(())
            }
        }
    }

    fn simplify(self) -> Self {
        match self {
            Formula::And(items) => {
                let mut flat = Vec::new();
                for item in items {
                    match item {
                        Formula::True => {}
                        Formula::False => return Formula::False,
                        Formula::And(inner) => flat.extend(inner),
                        other => flat.push(other),
                    }
                }
                if flat.is_empty() {
                    Formula::True
                } else if flat.len() == 1 {
                    flat.into_iter().next().unwrap()
                } else {
                    Formula::And(flat)
                }
            }
            Formula::Or(items) => {
                let mut flat = Vec::new();
                for item in items {
                    match item {
                        Formula::False => {}
                        Formula::True => return Formula::True,
                        Formula::Or(inner) => flat.extend(inner),
                        other => flat.push(other),
                    }
                }
                if flat.is_empty() {
                    Formula::False
                } else if flat.len() == 1 {
                    flat.into_iter().next().unwrap()
                } else {
                    Formula::Or(flat)
                }
            }
            Formula::Implies(lhs, rhs) => {
                if matches!(*lhs, Formula::False) || matches!(*rhs, Formula::True) {
                    Formula::True
                } else if matches!(*lhs, Formula::True) {
                    *rhs
                } else {
                    Formula::Implies(lhs, rhs)
                }
            }
            other => other,
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
            Formula::And(items) => write_joined(f, " && ", items),
            Formula::Or(items) => write_joined(f, " || ", items),
            Formula::Implies(lhs, rhs) => write!(f, "({lhs} => {rhs})"),
            Formula::Eq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
            Formula::MemoryEq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
            Formula::Lt(lhs, rhs) => write!(f, "({lhs} < {rhs})"),
            Formula::Le(lhs, rhs) => write!(f, "({lhs} <= {rhs})"),
            Formula::Gt(lhs, rhs) => write!(f, "({lhs} > {rhs})"),
            Formula::Ge(lhs, rhs) => write!(f, "({lhs} >= {rhs})"),
        }
    }
}

fn validate_memory(memory: &Memory) -> Result<(), FormulaError> {
    match memory {
        Memory::Var(_) => Ok(()),
        Memory::Store(inner, index, value) => {
            validate_memory(inner)?;
            let index_sort = index.sort()?;
            let value_sort = value.sort()?;
            if index_sort != Sort::Int {
                return Err(FormulaError::ExpectedIntegerSort { found: index_sort });
            }
            if value_sort != Sort::Int {
                return Err(FormulaError::ExpectedIntegerSort { found: value_sort });
            }
            Ok(())
        }
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    let mut a = a.abs();
    let mut b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 {
        1
    } else {
        a
    }
}

fn write_joined(f: &mut fmt::Formatter<'_>, sep: &str, items: &[Formula]) -> fmt::Result {
    write!(f, "(")?;
    for (idx, item) in items.iter().enumerate() {
        if idx > 0 {
            write!(f, "{sep}")?;
        }
        write!(f, "{item}")?;
    }
    write!(f, ")")
}

#[derive(Debug, Error, Clone, Eq, PartialEq)]
pub enum FormulaError {
    #[error("expected Boolean sort, found {found}")]
    ExpectedBooleanSort { found: Sort },
    #[error("expected numeric sort, found {found}")]
    ExpectedNumericSort { found: Sort },
    #[error("expected integer sort, found {found}")]
    ExpectedIntegerSort { found: Sort },
    #[error("mixed sorts: {left} vs {right}")]
    MixedSorts { left: Sort, right: Sort },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rational_is_reduced() {
        let value = Rational::new(6, 8);
        assert_eq!(value.numerator(), 3);
        assert_eq!(value.denominator(), 4);
    }

    #[test]
    fn boolean_var_validation_rejects_non_bool() {
        let formula = Formula::Var(Var::int("x"));
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::ExpectedBooleanSort { .. })
        ));
    }

    #[test]
    fn numeric_equality_requires_matching_sorts() {
        let formula = Formula::eq(Term::int(1), Term::real(Rational::integer(1)));
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::MixedSorts { .. })
        ));
    }

    #[test]
    fn logical_simplification_shortcuts() {
        let formula = Formula::and(Formula::True, Formula::bool_var("p"));
        assert_eq!(formula, Formula::bool_var("p"));
    }

    #[test]
    fn memory_store_requires_integer_index_and_value() {
        let formula = Formula::memory_eq(
            Memory::store(
                Memory::var("m"),
                Term::real(Rational::new(1, 2)),
                Term::int(3),
            ),
            Memory::var("m"),
        );
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::ExpectedIntegerSort { .. })
        ));
    }

    #[test]
    fn display_is_stable() {
        let formula = Formula::implies(
            Formula::bool_var("a"),
            Formula::eq(Term::var("x", Sort::Int), Term::int(4)),
        );
        assert_eq!(formula.to_string(), "(a => (x == 4))");
    }

    #[test]
    fn bool_to_int_is_integer_sorted() {
        assert_eq!(
            Term::bool_to_int(Formula::bool_var("b")).sort(),
            Ok(Sort::Int)
        );
    }
}
