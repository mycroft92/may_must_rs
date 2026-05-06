//! Formula vocabulary for paper predicates such as `Gamma_e`, `Pi_n`, and
//! obligations.
//!
//! This module is deliberately solver-independent. The only job here is to
//! model the paper's Boolean, arithmetic, and integer-array predicates with
//! explicit sorts.
//!
//! Besides the raw syntax trees, this file now also owns the variable-space
//! helpers that the driver needs to operationalize summary reuse:
//!
//! - free-variable discovery
//! - alpha renaming with fresh names
//! - interface substitution from callee summaries into caller formulas
//! - explicit integer-array memory equalities used by memory-aware summaries
//!
//! The intent is to keep all variable-space manipulation explicit and solver
//! independent. `oracle.rs` answers satisfiability and implication questions,
//! but it should not decide how formulas are renamed or instantiated.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Hash, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
pub enum Memory {
    Var(String),
    Store(Box<Memory>, Box<Term>, Box<Term>),
}

impl Memory {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn store(memory: Memory, index: Term, value: Term) -> Self {
        Self::Store(Box::new(memory), Box::new(index), Box::new(value))
    }

    pub fn validate(&self) -> Result<(), FormulaError> {
        match self {
            Memory::Var(_) => Ok(()),
            Memory::Store(memory, index, value) => {
                memory.validate()?;
                expect_integer_sort(index.sort()?)?;
                expect_integer_sort(value.sort()?)?;
                Ok(())
            }
        }
    }

    pub fn free_symbol_names(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        collect_memory_variables(self, &mut names);
        names
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Memory::Var(name) => write!(f, "{name}"),
            Memory::Store(memory, index, value) => {
                write!(f, "(store {memory} {index} {value})")
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
pub enum Term {
    Var(Var),
    Int(i64),
    Real(Rational),
    Select(Box<Memory>, Box<Term>),
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

    pub fn select(memory: Memory, index: Term) -> Self {
        Self::Select(Box::new(memory), Box::new(index))
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
            Term::Select(memory, index) => {
                memory.validate()?;
                expect_integer_sort(index.sort()?)?;
                Ok(Sort::Int)
            }
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
            Term::Select(memory, index) => write!(f, "(select {memory} {index})"),
            Term::Add(lhs, rhs) => write!(f, "({lhs} + {rhs})"),
            Term::Sub(lhs, rhs) => write!(f, "({lhs} - {rhs})"),
            Term::Mul(lhs, rhs) => write!(f, "({lhs} * {rhs})"),
            Term::Div(lhs, rhs) => write!(f, "({lhs} / {rhs})"),
            Term::Neg(term) => write!(f, "(-{term})"),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
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

    pub fn memory_eq(lhs: Memory, rhs: Memory) -> Self {
        Self::MemoryEq(lhs, rhs)
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
            Formula::MemoryEq(lhs, rhs) => {
                lhs.validate()?;
                rhs.validate()
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

    /// Returns the symbol names that occur syntactically in this formula,
    /// including scalar variables and memory variables.
    pub fn free_variable_names(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        collect_formula_variables(self, &mut names);
        names
    }

    /// Checks whether the formula mentions only the given visible variables.
    pub fn mentions_only(&self, visible: &BTreeSet<String>) -> bool {
        self.free_variable_names()
            .into_iter()
            .all(|name| visible.contains(&name))
    }

    /// Alpha-renames scalar variables using an explicit mapping.
    pub fn alpha_rename(&self, mapping: &BTreeMap<String, Var>) -> Self {
        rename_formula(self, mapping)
    }

    /// Alpha-renames memory variables using an explicit string mapping.
    pub fn alpha_rename_memory(&self, mapping: &BTreeMap<String, String>) -> Self {
        rename_formula_memory(self, mapping)
    }

    /// Simultaneously substitutes scalar integer/real variables by terms and
    /// scalar Boolean variables by predicates, while also substituting memory
    /// variables by memory expressions.
    pub fn substitute_interface(
        &self,
        term_subst: &BTreeMap<String, Term>,
        bool_subst: &BTreeMap<String, Formula>,
        memory_subst: &BTreeMap<String, Memory>,
    ) -> Self {
        substitute_formula(self, term_subst, bool_subst, memory_subst)
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
            Formula::MemoryEq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
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
    #[error("expected an integer sort but found {found}")]
    ExpectedIntegerSort { found: Sort },
    #[error("mixed sorts are not allowed: {left} vs {right}")]
    MixedSorts { left: Sort, right: Sort },
}

fn expect_integer_sort(sort: Sort) -> Result<(), FormulaError> {
    if sort == Sort::Int {
        Ok(())
    } else {
        Err(FormulaError::ExpectedIntegerSort { found: sort })
    }
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// Generates fresh variable names for alpha-renaming without consulting the
/// solver.
pub struct FreshNameGenerator {
    next: usize,
}

impl FreshNameGenerator {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn freshened_var(&mut self, var: &Var, stem: &str) -> Var {
        let fresh = Var::new(format!("{stem}${}${}", var.name(), self.next), var.sort());
        self.next += 1;
        fresh
    }

    pub fn freshened_name(&mut self, base: &str, stem: &str) -> String {
        let fresh = format!("{stem}${base}${}", self.next);
        self.next += 1;
        fresh
    }
}

fn collect_formula_variables(formula: &Formula, names: &mut BTreeSet<String>) {
    match formula {
        Formula::True | Formula::False => {}
        Formula::Var(var) => {
            names.insert(var.name().to_string());
        }
        Formula::Not(inner) => collect_formula_variables(inner, names),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_formula_variables(item, names);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_formula_variables(lhs, names);
            collect_formula_variables(rhs, names);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_term_variables(lhs, names);
            collect_term_variables(rhs, names);
        }
        Formula::MemoryEq(lhs, rhs) => {
            collect_memory_variables(lhs, names);
            collect_memory_variables(rhs, names);
        }
    }
}

fn collect_term_variables(term: &Term, names: &mut BTreeSet<String>) {
    match term {
        Term::Var(var) => {
            names.insert(var.name().to_string());
        }
        Term::Int(_) | Term::Real(_) => {}
        Term::Select(memory, index) => {
            collect_memory_variables(memory, names);
            collect_term_variables(index, names);
        }
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            collect_term_variables(lhs, names);
            collect_term_variables(rhs, names);
        }
        Term::Neg(inner) => collect_term_variables(inner, names),
    }
}

fn collect_memory_variables(memory: &Memory, names: &mut BTreeSet<String>) {
    match memory {
        Memory::Var(name) => {
            names.insert(name.clone());
        }
        Memory::Store(inner, index, value) => {
            collect_memory_variables(inner, names);
            collect_term_variables(index, names);
            collect_term_variables(value, names);
        }
    }
}

fn rename_formula(formula: &Formula, mapping: &BTreeMap<String, Var>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(
            mapping
                .get(var.name())
                .cloned()
                .unwrap_or_else(|| var.clone()),
        ),
        Formula::Not(inner) => Formula::not(rename_formula(inner, mapping)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| rename_formula(item, mapping))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| rename_formula(item, mapping))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => {
            Formula::implies(rename_formula(lhs, mapping), rename_formula(rhs, mapping))
        }
        Formula::Eq(lhs, rhs) => Formula::eq(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Formula::MemoryEq(lhs, rhs) => {
            Formula::memory_eq(rename_memory(lhs, mapping), rename_memory(rhs, mapping))
        }
        Formula::Lt(lhs, rhs) => Formula::lt(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Formula::Le(lhs, rhs) => Formula::le(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Formula::Gt(lhs, rhs) => Formula::gt(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Formula::Ge(lhs, rhs) => Formula::ge(rename_term(lhs, mapping), rename_term(rhs, mapping)),
    }
}

fn rename_formula_memory(formula: &Formula, mapping: &BTreeMap<String, String>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => Formula::not(rename_formula_memory(inner, mapping)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| rename_formula_memory(item, mapping))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| rename_formula_memory(item, mapping))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            rename_formula_memory(lhs, mapping),
            rename_formula_memory(rhs, mapping),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            rename_memory_by_name(lhs, mapping),
            rename_memory_by_name(rhs, mapping),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
    }
}

fn rename_term(term: &Term, mapping: &BTreeMap<String, Var>) -> Term {
    match term {
        Term::Var(var) => Term::Var(
            mapping
                .get(var.name())
                .cloned()
                .unwrap_or_else(|| var.clone()),
        ),
        Term::Int(value) => Term::int(*value),
        Term::Real(value) => Term::Real(value.clone()),
        Term::Select(memory, index) => {
            Term::select(rename_memory(memory, mapping), rename_term(index, mapping))
        }
        Term::Add(lhs, rhs) => Term::add(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Term::Sub(lhs, rhs) => Term::sub(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Term::Mul(lhs, rhs) => Term::mul(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Term::Div(lhs, rhs) => Term::div(rename_term(lhs, mapping), rename_term(rhs, mapping)),
        Term::Neg(inner) => Term::neg(rename_term(inner, mapping)),
    }
}

fn rename_memory(memory: &Memory, mapping: &BTreeMap<String, Var>) -> Memory {
    match memory {
        Memory::Var(name) => {
            if let Some(var) = mapping.get(name) {
                Memory::var(var.name())
            } else {
                Memory::var(name.clone())
            }
        }
        Memory::Store(inner, index, value) => Memory::store(
            rename_memory(inner, mapping),
            rename_term(index, mapping),
            rename_term(value, mapping),
        ),
    }
}

fn rename_term_memory(term: &Term, mapping: &BTreeMap<String, String>) -> Term {
    match term {
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::int(*value),
        Term::Real(value) => Term::Real(value.clone()),
        Term::Select(memory, index) => Term::select(
            rename_memory_by_name(memory, mapping),
            rename_term_memory(index, mapping),
        ),
        Term::Add(lhs, rhs) => Term::add(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Term::Div(lhs, rhs) => Term::div(
            rename_term_memory(lhs, mapping),
            rename_term_memory(rhs, mapping),
        ),
        Term::Neg(inner) => Term::neg(rename_term_memory(inner, mapping)),
    }
}

fn rename_memory_by_name(memory: &Memory, mapping: &BTreeMap<String, String>) -> Memory {
    match memory {
        Memory::Var(name) => {
            Memory::var(mapping.get(name).cloned().unwrap_or_else(|| name.clone()))
        }
        Memory::Store(inner, index, value) => Memory::store(
            rename_memory_by_name(inner, mapping),
            rename_term_memory(index, mapping),
            rename_term_memory(value, mapping),
        ),
    }
}

fn substitute_formula(
    formula: &Formula,
    term_subst: &BTreeMap<String, Term>,
    bool_subst: &BTreeMap<String, Formula>,
    memory_subst: &BTreeMap<String, Memory>,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => bool_subst
            .get(var.name())
            .cloned()
            .unwrap_or_else(|| Formula::Var(var.clone())),
        Formula::Not(inner) => Formula::not(substitute_formula(
            inner,
            term_subst,
            bool_subst,
            memory_subst,
        )),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| substitute_formula(item, term_subst, bool_subst, memory_subst))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| substitute_formula(item, term_subst, bool_subst, memory_subst))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_formula(lhs, term_subst, bool_subst, memory_subst),
            substitute_formula(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_memory(lhs, term_subst, bool_subst, memory_subst),
            substitute_memory(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
    }
}

fn substitute_term(
    term: &Term,
    term_subst: &BTreeMap<String, Term>,
    bool_subst: &BTreeMap<String, Formula>,
    memory_subst: &BTreeMap<String, Memory>,
) -> Term {
    match term {
        Term::Var(var) => term_subst
            .get(var.name())
            .cloned()
            .unwrap_or_else(|| Term::Var(var.clone())),
        Term::Int(value) => Term::int(*value),
        Term::Real(value) => Term::Real(value.clone()),
        Term::Select(memory, index) => Term::select(
            substitute_memory(memory, term_subst, bool_subst, memory_subst),
            substitute_term(index, term_subst, bool_subst, memory_subst),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_term(lhs, term_subst, bool_subst, memory_subst),
            substitute_term(rhs, term_subst, bool_subst, memory_subst),
        ),
        Term::Neg(inner) => Term::neg(substitute_term(inner, term_subst, bool_subst, memory_subst)),
    }
}

fn substitute_memory(
    memory: &Memory,
    term_subst: &BTreeMap<String, Term>,
    bool_subst: &BTreeMap<String, Formula>,
    memory_subst: &BTreeMap<String, Memory>,
) -> Memory {
    match memory {
        Memory::Var(name) => memory_subst.get(name).cloned().unwrap_or_else(|| {
            if let Some(Term::Var(var)) = term_subst.get(name) {
                Memory::var(var.name())
            } else {
                Memory::var(name.clone())
            }
        }),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_memory(inner, term_subst, bool_subst, memory_subst),
            substitute_term(index, term_subst, bool_subst, memory_subst),
            substitute_term(value, term_subst, bool_subst, memory_subst),
        ),
    }
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
