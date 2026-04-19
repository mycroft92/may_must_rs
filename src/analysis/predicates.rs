//! Solver-independent predicate vocabulary for the SMT-backed analyzer.
//!
//! The active toy analyzer still uses string predicates in `domain.rs`. This
//! module is the next representation: summaries and path states can store
//! cloneable Rust terms/formulas, then encode them into a fresh
//! `StateEncoding` when they need SMT checks. Keeping raw Z3 ASTs out of
//! summaries makes later caller/callee instantiation a substitution problem
//! instead of a solver-context lifetime problem.

#![allow(dead_code)]

use crate::analysis::state::{StateEncoding, SummaryPhase};
use std::fmt;
use z3::ast::{Bool, Int};
use z3::SatResult;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PredicateError {
    UnknownSmtResult,
}

impl fmt::Display for PredicateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PredicateError::UnknownSmtResult => write!(f, "SMT solver returned unknown"),
        }
    }
}

impl std::error::Error for PredicateError {}

pub type PredicateResult<T> = std::result::Result<T, PredicateError>;

/// Integer-valued symbolic term.
///
/// For now this is intentionally scalar-only. Memory terms will be added after
/// scalar transfer, branch feasibility, and function-boundary summaries are in
/// place.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum IntTerm {
    Const(i64),
    /// Path-local LLVM SSA integer symbol.
    Ssa(String),
    /// Function summary formal parameter at a pre/post boundary.
    SummaryParam {
        phase: SummaryPhase,
        index: usize,
    },
    /// Function summary return value at a pre/post boundary.
    SummaryReturn {
        phase: SummaryPhase,
    },
    Add(Box<IntTerm>, Box<IntTerm>),
    Sub(Box<IntTerm>, Box<IntTerm>),
    Mul(Box<IntTerm>, Box<IntTerm>),
}

impl IntTerm {
    pub fn int(value: i64) -> Self {
        Self::Const(value)
    }

    pub fn ssa(name: impl Into<String>) -> Self {
        Self::Ssa(normalize_name(name.into()))
    }

    pub fn summary_param(phase: SummaryPhase, index: usize) -> Self {
        Self::SummaryParam { phase, index }
    }

    pub fn summary_return(phase: SummaryPhase) -> Self {
        Self::SummaryReturn { phase }
    }

    pub fn add(left: IntTerm, right: IntTerm) -> Self {
        match (left, right) {
            (IntTerm::Const(0), right) => right,
            (left, IntTerm::Const(0)) => left,
            (IntTerm::Const(left), IntTerm::Const(right)) => IntTerm::Const(left + right),
            (left, right) => IntTerm::Add(Box::new(left), Box::new(right)),
        }
    }

    pub fn sub(left: IntTerm, right: IntTerm) -> Self {
        match (left, right) {
            (left, IntTerm::Const(0)) => left,
            (IntTerm::Const(left), IntTerm::Const(right)) => IntTerm::Const(left - right),
            (left, right) => IntTerm::Sub(Box::new(left), Box::new(right)),
        }
    }

    pub fn mul(left: IntTerm, right: IntTerm) -> Self {
        match (left, right) {
            (IntTerm::Const(0), _) | (_, IntTerm::Const(0)) => IntTerm::Const(0),
            (IntTerm::Const(1), right) => right,
            (left, IntTerm::Const(1)) => left,
            (IntTerm::Const(left), IntTerm::Const(right)) => IntTerm::Const(left * right),
            (left, right) => IntTerm::Mul(Box::new(left), Box::new(right)),
        }
    }

    pub fn encode(&self, state: &mut StateEncoding) -> Int {
        match self {
            IntTerm::Const(value) => state.int_const(*value),
            IntTerm::Ssa(name) => state.ssa_int(name),
            IntTerm::SummaryParam { phase, index } => state.summary_param_int(*phase, *index),
            IntTerm::SummaryReturn { phase } => state.summary_return_int(*phase),
            IntTerm::Add(left, right) => {
                let left = left.encode(state);
                let right = right.encode(state);
                Int::add(&[&left, &right])
            }
            IntTerm::Sub(left, right) => {
                let left = left.encode(state);
                let right = right.encode(state);
                Int::sub(&[&left, &right])
            }
            IntTerm::Mul(left, right) => {
                let left = left.encode(state);
                let right = right.encode(state);
                Int::mul(&[&left, &right])
            }
        }
    }
}

impl fmt::Display for IntTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntTerm::Const(value) => write!(f, "{value}"),
            IntTerm::Ssa(name) => write!(f, "{name}"),
            IntTerm::SummaryParam { phase, index } => write!(f, "{phase:?}.param_{index}"),
            IntTerm::SummaryReturn { phase } => write!(f, "{phase:?}.ret"),
            IntTerm::Add(left, right) => write!(f, "({left} + {right})"),
            IntTerm::Sub(left, right) => write!(f, "({left} - {right})"),
            IntTerm::Mul(left, right) => write!(f, "({left} * {right})"),
        }
    }
}

/// Boolean formula over integer terms and path-local Boolean SSA symbols.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Formula {
    True,
    False,
    BoolSsa(String),
    Eq(IntTerm, IntTerm),
    Ne(IntTerm, IntTerm),
    Gt(IntTerm, IntTerm),
    Ge(IntTerm, IntTerm),
    Lt(IntTerm, IntTerm),
    Le(IntTerm, IntTerm),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl Formula {
    pub fn bool_ssa(name: impl Into<String>) -> Self {
        Self::BoolSsa(normalize_name(name.into()))
    }

    pub fn eq(left: IntTerm, right: IntTerm) -> Self {
        if left == right {
            Self::True
        } else {
            Self::Eq(left, right)
        }
    }

    pub fn ne(left: IntTerm, right: IntTerm) -> Self {
        if left == right {
            Self::False
        } else {
            Self::Ne(left, right)
        }
    }

    pub fn gt(left: IntTerm, right: IntTerm) -> Self {
        Self::Gt(left, right)
    }

    pub fn ge(left: IntTerm, right: IntTerm) -> Self {
        Self::Ge(left, right)
    }

    pub fn lt(left: IntTerm, right: IntTerm) -> Self {
        Self::Lt(left, right)
    }

    pub fn le(left: IntTerm, right: IntTerm) -> Self {
        Self::Le(left, right)
    }

    pub fn negate(self) -> Self {
        match self {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            Formula::Not(inner) => *inner,
            other => Formula::Not(Box::new(other)),
        }
    }

    pub fn and(items: impl IntoIterator<Item = Formula>) -> Self {
        let mut flattened = Vec::new();
        for item in items {
            match item {
                Formula::True => {}
                Formula::False => return Formula::False,
                Formula::And(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }

        match flattened.len() {
            0 => Formula::True,
            1 => flattened.remove(0),
            _ => Formula::And(flattened),
        }
    }

    pub fn or(items: impl IntoIterator<Item = Formula>) -> Self {
        let mut flattened = Vec::new();
        for item in items {
            match item {
                Formula::True => return Formula::True,
                Formula::False => {}
                Formula::Or(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }

        match flattened.len() {
            0 => Formula::False,
            1 => flattened.remove(0),
            _ => Formula::Or(flattened),
        }
    }

    pub fn encode(&self, state: &mut StateEncoding) -> Bool {
        match self {
            Formula::True => state.bool_const(true),
            Formula::False => state.bool_const(false),
            Formula::BoolSsa(name) => state.ssa_bool(name),
            Formula::Eq(left, right) => left.encode(state).eq(&right.encode(state)),
            Formula::Ne(left, right) => left.encode(state).eq(&right.encode(state)).not(),
            Formula::Gt(left, right) => left.encode(state).gt(&right.encode(state)),
            Formula::Ge(left, right) => left.encode(state).ge(&right.encode(state)),
            Formula::Lt(left, right) => left.encode(state).lt(&right.encode(state)),
            Formula::Le(left, right) => left.encode(state).le(&right.encode(state)),
            Formula::Not(inner) => inner.encode(state).not(),
            Formula::And(items) => {
                let encoded = items
                    .iter()
                    .map(|item| item.encode(state))
                    .collect::<Vec<_>>();
                let refs = encoded.iter().collect::<Vec<_>>();
                Bool::and(&refs)
            }
            Formula::Or(items) => {
                let encoded = items
                    .iter()
                    .map(|item| item.encode(state))
                    .collect::<Vec<_>>();
                let refs = encoded.iter().collect::<Vec<_>>();
                Bool::or(&refs)
            }
        }
    }

    pub fn is_satisfiable_in(&self, function: &str) -> PredicateResult<bool> {
        let mut state = StateEncoding::new(function);
        let formula = self.encode(&mut state);
        state.assert(&formula);
        match state.check() {
            SatResult::Sat => Ok(true),
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err(PredicateError::UnknownSmtResult),
        }
    }

    pub fn entails_in(&self, other: &Formula, function: &str) -> PredicateResult<bool> {
        let mut state = StateEncoding::new(function);
        let left = self.encode(&mut state);
        let right = other.encode(&mut state);
        state.assert(&left);
        state.assert(&right.not());
        match state.check() {
            SatResult::Sat => Ok(false),
            SatResult::Unsat => Ok(true),
            SatResult::Unknown => Err(PredicateError::UnknownSmtResult),
        }
    }

    pub fn intersects_in(&self, other: &Formula, function: &str) -> PredicateResult<bool> {
        Formula::and([self.clone(), other.clone()]).is_satisfiable_in(function)
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::BoolSsa(name) => write!(f, "{name}"),
            Formula::Eq(left, right) => write!(f, "{left} == {right}"),
            Formula::Ne(left, right) => write!(f, "{left} != {right}"),
            Formula::Gt(left, right) => write!(f, "{left} > {right}"),
            Formula::Ge(left, right) => write!(f, "{left} >= {right}"),
            Formula::Lt(left, right) => write!(f, "{left} < {right}"),
            Formula::Le(left, right) => write!(f, "{left} <= {right}"),
            Formula::Not(inner) => write!(f, "!({inner})"),
            Formula::And(items) => write_joined(f, items, " & "),
            Formula::Or(items) => write_joined(f, items, " | "),
        }
    }
}

fn write_joined(f: &mut fmt::Formatter<'_>, items: &[Formula], sep: &str) -> fmt::Result {
    write!(f, "(")?;
    for (idx, item) in items.iter().enumerate() {
        if idx > 0 {
            write!(f, "{sep}")?;
        }
        write!(f, "{item}")?;
    }
    write!(f, ")")
}

fn normalize_name(name: impl AsRef<str>) -> String {
    let name = name.as_ref();
    if name.starts_with('%') {
        name.to_string()
    } else {
        format!("%{name}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_formula_encodes_to_z3() {
        let x = IntTerm::ssa("%x");
        let formula = Formula::and([
            Formula::eq(x.clone(), IntTerm::int(3)),
            Formula::eq(IntTerm::add(x, IntTerm::int(1)), IntTerm::int(4)),
        ]);

        assert_eq!(formula.is_satisfiable_in("main").unwrap(), true);
    }

    #[test]
    fn contradictory_formula_is_unsat() {
        let x = IntTerm::ssa("%x");
        let formula = Formula::and([
            Formula::gt(x.clone(), IntTerm::int(10)),
            Formula::le(x, IntTerm::int(10)),
        ]);

        assert_eq!(formula.is_satisfiable_in("main").unwrap(), false);
    }

    #[test]
    fn summary_boundary_terms_encode_pre_post_relation() {
        let param = IntTerm::summary_param(SummaryPhase::Pre, 0);
        let ret = IntTerm::summary_return(SummaryPhase::Post);
        let relation = Formula::eq(ret.clone(), IntTerm::add(param.clone(), IntTerm::int(1)));

        assert_eq!(
            relation
                .entails_in(&Formula::gt(ret, param), "increment")
                .unwrap(),
            true
        );
    }

    #[test]
    fn entailment_and_intersection_use_smt() {
        let x = IntTerm::ssa("%x");
        let positive = Formula::gt(x.clone(), IntTerm::int(0));
        let nonzero = Formula::ne(x.clone(), IntTerm::int(0));
        let negative = Formula::lt(x, IntTerm::int(0));

        assert_eq!(positive.entails_in(&nonzero, "main").unwrap(), true);
        assert_eq!(positive.intersects_in(&negative, "main").unwrap(), false);
    }
}
