#![allow(dead_code)]

//! Translation from the assertion frontend AST into the paper formula language.
//!
//! Parser-specific sort inference intentionally lives here instead of inside
//! `analysis::formula`. That keeps user-facing syntax recovery separate from
//! the paper vocabulary and lets tests exercise translation without any LLVM
//! dependency. The output is the same formula vocabulary later reused by the
//! rule driver, summaries, and oracle.

use crate::formula::{Formula, Rational, Sort, Term};
use crate::frontend::assertions::exp::{Assertion, Expr, Op, Statement};
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use thiserror::Error;

pub type SortSeeds = BTreeMap<String, Sort>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranslatedStatement {
    pub func: String,
    pub predicate: Formula,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranslatedAssertion {
    pub name: String,
    pub stmt: TranslatedStatement,
}

pub fn translate_expr(expr: &Expr, seeds: &SortSeeds) -> Result<Formula, TranslationError> {
    lower_formula(expr, seeds)
}

pub fn translate_statement(
    statement: &Statement,
    seeds: &SortSeeds,
) -> Result<TranslatedStatement, TranslationError> {
    Ok(TranslatedStatement {
        func: statement.func.clone(),
        predicate: translate_expr(&statement.exp, seeds)?,
    })
}

pub fn translate_assertion(
    assertion: &Assertion,
    seeds: &SortSeeds,
) -> Result<TranslatedAssertion, TranslationError> {
    Ok(TranslatedAssertion {
        name: assertion.name.clone(),
        stmt: translate_statement(&assertion.stmt, seeds)?,
    })
}

fn lower_formula(expr: &Expr, seeds: &SortSeeds) -> Result<Formula, TranslationError> {
    match expr {
        Expr::Ident(name) => {
            let sort = seeds.get(name).copied().unwrap_or(Sort::Bool);
            if sort != Sort::Bool {
                return Err(TranslationError::NonBooleanAtom { expr: name.clone() });
            }
            Ok(Formula::bool_var(name.clone()))
        }
        Expr::Const(value) => match value.as_str() {
            "true" => Ok(Formula::True),
            "false" => Ok(Formula::False),
            _ => Err(TranslationError::NonBooleanAtom {
                expr: value.clone(),
            }),
        },
        Expr::Unop(inner) => Ok(Formula::not(lower_formula(inner, seeds)?)),
        Expr::Binop(lhs, op, rhs) => match op {
            Op::LAnd => Ok(Formula::and(
                lower_formula(lhs, seeds)?,
                lower_formula(rhs, seeds)?,
            )),
            Op::LOr => Ok(Formula::or(
                lower_formula(lhs, seeds)?,
                lower_formula(rhs, seeds)?,
            )),
            Op::Eeq => {
                let sort = infer_numeric_sort(lhs, rhs, seeds)?;
                let lhs = lower_term(lhs, seeds, sort)?;
                let rhs = lower_term(rhs, seeds, sort)?;
                Ok(Formula::eq(lhs, rhs))
            }
            Op::Gt => lower_comparison(lhs, rhs, seeds, Formula::gt),
            Op::Ge => lower_comparison(lhs, rhs, seeds, Formula::ge),
            Op::Lt => lower_comparison(lhs, rhs, seeds, Formula::lt),
            Op::Le => lower_comparison(lhs, rhs, seeds, Formula::le),
            Op::Plus | Op::Minus | Op::Div | Op::Mult => Err(TranslationError::NonBooleanAtom {
                expr: format!("{lhs:?} {op} {rhs:?}"),
            }),
            Op::LNot | Op::Arrow | Op::Named => {
                Err(TranslationError::UnsupportedOperator { op: op.clone() })
            }
        },
    }
}

fn lower_comparison(
    lhs: &Expr,
    rhs: &Expr,
    seeds: &SortSeeds,
    build: fn(Term, Term) -> Formula,
) -> Result<Formula, TranslationError> {
    let sort = infer_numeric_sort(lhs, rhs, seeds)?;
    Ok(build(
        lower_term(lhs, seeds, sort)?,
        lower_term(rhs, seeds, sort)?,
    ))
}

fn lower_term(expr: &Expr, seeds: &SortSeeds, expected: Sort) -> Result<Term, TranslationError> {
    if expected == Sort::Bool {
        return Err(TranslationError::UnsupportedBooleanTerm);
    }
    match expr {
        Expr::Ident(name) => {
            if let Some(seed) = seeds.get(name) {
                if *seed != expected {
                    return Err(TranslationError::SeedConflict {
                        name: name.clone(),
                        expected,
                        actual: *seed,
                    });
                }
            }
            Ok(Term::var(name.clone(), expected))
        }
        Expr::Const(value) => lower_literal(value, expected),
        Expr::Unop(inner) => Ok(Term::neg(lower_term(inner, seeds, expected)?)),
        Expr::Binop(lhs, op, rhs) => {
            let lhs = lower_term(lhs, seeds, expected)?;
            let rhs = lower_term(rhs, seeds, expected)?;
            match op {
                Op::Plus => Ok(Term::add(lhs, rhs)),
                Op::Minus => Ok(Term::sub(lhs, rhs)),
                Op::Mult => Ok(Term::mul(lhs, rhs)),
                Op::Div => Ok(Term::div(lhs, rhs)),
                _ => Err(TranslationError::ExpectedArithmeticExpr),
            }
        }
    }
}

fn infer_numeric_sort(lhs: &Expr, rhs: &Expr, seeds: &SortSeeds) -> Result<Sort, TranslationError> {
    let lhs_sorts = candidate_numeric_sorts(lhs, seeds)?;
    let rhs_sorts = candidate_numeric_sorts(rhs, seeds)?;
    let intersection = lhs_sorts
        .intersection(&rhs_sorts)
        .copied()
        .collect::<BTreeSet<Sort>>();
    if intersection.is_empty() {
        return Err(TranslationError::NoSharedNumericSort);
    }
    if intersection.len() > 1 {
        if intersection.contains(&Sort::Int)
            && intersection.contains(&Sort::Real)
            && (contains_arithmetic(lhs) || contains_arithmetic(rhs))
        {
            return Ok(Sort::Int);
        }
        return Err(TranslationError::AmbiguousNumericSort);
    }
    Ok(*intersection.iter().next().unwrap())
}

fn candidate_numeric_sorts(
    expr: &Expr,
    seeds: &SortSeeds,
) -> Result<BTreeSet<Sort>, TranslationError> {
    let sorts = match expr {
        Expr::Ident(name) => match seeds.get(name).copied() {
            Some(Sort::Bool) => BTreeSet::new(),
            Some(sort) => BTreeSet::from([sort]),
            None => BTreeSet::from([Sort::Int, Sort::Real]),
        },
        Expr::Const(value) => {
            if value.contains('.') {
                BTreeSet::from([Sort::Real])
            } else {
                BTreeSet::from([Sort::Int, Sort::Real])
            }
        }
        Expr::Unop(inner) => candidate_numeric_sorts(inner, seeds)?,
        Expr::Binop(lhs, op, rhs) => match op {
            Op::Plus | Op::Minus | Op::Mult | Op::Div => {
                let lhs = candidate_numeric_sorts(lhs, seeds)?;
                let rhs = candidate_numeric_sorts(rhs, seeds)?;
                lhs.intersection(&rhs).copied().collect()
            }
            _ => BTreeSet::new(),
        },
    };
    if sorts.is_empty() {
        return Err(TranslationError::ExpectedArithmeticExpr);
    }
    Ok(sorts)
}

fn lower_literal(value: &str, expected: Sort) -> Result<Term, TranslationError> {
    match expected {
        Sort::Int => value.parse::<i64>().map(Term::int).map_err(|_| {
            TranslationError::InvalidIntegerLiteral {
                literal: value.to_string(),
            }
        }),
        Sort::Real => parse_real_literal(value).map(Term::Real),
        Sort::Bool => Err(TranslationError::UnsupportedBooleanTerm),
    }
}

fn contains_arithmetic(expr: &Expr) -> bool {
    match expr {
        Expr::Binop(lhs, op, rhs) => {
            matches!(op, Op::Plus | Op::Minus | Op::Mult | Op::Div)
                || contains_arithmetic(lhs)
                || contains_arithmetic(rhs)
        }
        Expr::Unop(inner) => contains_arithmetic(inner),
        _ => false,
    }
}

fn parse_real_literal(value: &str) -> Result<Rational, TranslationError> {
    if let Some((whole, frac)) = value.split_once('.') {
        let whole = whole
            .parse::<i64>()
            .map_err(|_| TranslationError::InvalidRealLiteral {
                literal: value.to_string(),
            })?;
        let frac_digits = frac.len() as u32;
        let frac_value = frac
            .parse::<i64>()
            .map_err(|_| TranslationError::InvalidRealLiteral {
                literal: value.to_string(),
            })?;
        let denom = 10_i64.pow(frac_digits);
        let sign = if whole < 0 { -1 } else { 1 };
        let whole_abs = whole.abs();
        let num = sign * (whole_abs * denom + frac_value);
        Ok(Rational::new(num, denom))
    } else {
        value.parse::<i64>().map(Rational::integer).map_err(|_| {
            TranslationError::InvalidRealLiteral {
                literal: value.to_string(),
            }
        })
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum TranslationError {
    #[error("non-Boolean atom in assertion context: {expr}")]
    NonBooleanAtom { expr: String },
    #[error("unsupported operator in translation: {op}")]
    UnsupportedOperator { op: Op },
    #[error("expected an arithmetic expression")]
    ExpectedArithmeticExpr,
    #[error("Boolean terms are not supported here")]
    UnsupportedBooleanTerm,
    #[error("no shared numeric sort could be inferred")]
    NoSharedNumericSort,
    #[error("numeric sort is ambiguous without seeds")]
    AmbiguousNumericSort,
    #[error("sort seed conflict for {name}: expected {expected}, got {actual}")]
    SeedConflict {
        name: String,
        expected: Sort,
        actual: Sort,
    },
    #[error("mixed numeric contexts are not allowed: {left} vs {right}")]
    MixedNumericContext { left: Sort, right: Sort },
    #[error("invalid integer literal: {literal}")]
    InvalidIntegerLiteral { literal: String },
    #[error("invalid real literal: {literal}")]
    InvalidRealLiteral { literal: String },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{Formula, Sort, Term};
    use crate::frontend::assertions::exp::parse_cmd_line;

    #[test]
    fn integer_assertion_translation() {
        let assertion = parse_cmd_line("main => %x + 1 == 4").unwrap();
        let translated = translate_assertion(&assertion, &SortSeeds::new()).unwrap();
        assert_eq!(
            translated.stmt.predicate,
            Formula::eq(
                Term::add(Term::var("%x", Sort::Int), Term::int(1)),
                Term::int(4)
            )
        );
    }

    #[test]
    fn real_context_promotes_integer_literals() {
        let assertion = parse_cmd_line("main => %x + 1 == 4.5").unwrap();
        let seeds = SortSeeds::from([("%x".to_string(), Sort::Real)]);
        let translated = translate_assertion(&assertion, &seeds).unwrap();
        assert_eq!(
            translated.stmt.predicate,
            Formula::eq(
                Term::add(Term::var("%x", Sort::Real), Term::real(Rational::new(1, 1))),
                Term::real(Rational::new(9, 2))
            )
        );
    }

    #[test]
    fn bare_boolean_variable_translation() {
        let assertion = parse_cmd_line("main => %flag").unwrap();
        let translated = translate_assertion(&assertion, &SortSeeds::new()).unwrap();
        assert_eq!(translated.stmt.predicate, Formula::bool_var("%flag"));
    }

    #[test]
    fn ambiguous_equality_is_rejected_without_seeds() {
        let assertion = parse_cmd_line("main => %x == 0").unwrap();
        let error = translate_assertion(&assertion, &SortSeeds::new()).unwrap_err();
        assert_eq!(error, TranslationError::AmbiguousNumericSort);
    }

    #[test]
    fn seeded_sort_resolves_ambiguous_equality() {
        let assertion = parse_cmd_line("main => %x == 0").unwrap();
        let seeds = SortSeeds::from([("%x".to_string(), Sort::Int)]);
        let translated = translate_assertion(&assertion, &seeds).unwrap();
        assert_eq!(
            translated.stmt.predicate,
            Formula::eq(Term::var("%x", Sort::Int), Term::int(0))
        );
    }
}
