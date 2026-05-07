//! Lightweight symbolic simplification for paper formulas and array-memory
//! terms.
//!
//! This module is intentionally syntax-directed and solver-free. It performs
//! only the local rewrites that the active summary and call machinery needs:
//!
//! - `select(store(M, i, v), i) -> v`
//! - Boolean cleanup around `and` / `or` / `not` / `implies`
//! - trivial equality/comparison cleanup after term simplification
//!
//! The goal is not complete normalization. It exists so projected summaries
//! and mapped call queries do not keep obviously local stack-memory terms
//! alive when they can be discharged syntactically.

use crate::analysis::formula::{Formula, Memory, Rational, Term};

pub fn simplify_formula(formula: &Formula) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => match simplify_formula(inner) {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            other => Formula::not(other),
        },
        Formula::And(items) => {
            let mut simplified = Vec::new();
            for item in items {
                match simplify_formula(item) {
                    Formula::False => return Formula::False,
                    Formula::True => {}
                    other => simplified.push(other),
                }
            }
            Formula::and_all(simplified)
        }
        Formula::Or(items) => {
            let mut simplified = Vec::new();
            for item in items {
                match simplify_formula(item) {
                    Formula::True => return Formula::True,
                    Formula::False => {}
                    other => simplified.push(other),
                }
            }
            Formula::or_all(simplified)
        }
        Formula::Implies(lhs, rhs) => {
            let lhs = simplify_formula(lhs);
            let rhs = simplify_formula(rhs);
            match (&lhs, &rhs) {
                (Formula::False, _) | (_, Formula::True) => Formula::True,
                (Formula::True, _) => rhs,
                (_, Formula::False) => Formula::not(lhs),
                _ => Formula::implies(lhs, rhs),
            }
        }
        Formula::Eq(lhs, rhs) => {
            let lhs = simplify_term(lhs);
            let rhs = simplify_term(rhs);
            if lhs == rhs {
                Formula::True
            } else {
                Formula::eq(lhs, rhs)
            }
        }
        Formula::MemoryEq(lhs, rhs) => {
            let lhs = simplify_memory(lhs);
            let rhs = simplify_memory(rhs);
            if lhs == rhs {
                Formula::True
            } else {
                Formula::memory_eq(lhs, rhs)
            }
        }
        Formula::Lt(lhs, rhs) => simplify_comparison(lhs, rhs, Formula::lt, false),
        Formula::Le(lhs, rhs) => simplify_comparison(lhs, rhs, Formula::le, true),
        Formula::Gt(lhs, rhs) => simplify_comparison(lhs, rhs, Formula::gt, false),
        Formula::Ge(lhs, rhs) => simplify_comparison(lhs, rhs, Formula::ge, true),
    }
}

pub fn simplify_term(term: &Term) -> Term {
    match term {
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(value.clone()),
        Term::Select(memory, index) => {
            let memory = simplify_memory(memory);
            let index = simplify_term(index);
            if let Memory::Store(inner, store_index, value) = &memory {
                if simplify_term(store_index) == index {
                    return simplify_term(value);
                }
                return Term::select(
                    Memory::Store(inner.clone(), store_index.clone(), value.clone()),
                    index,
                );
            }
            Term::select(memory, index)
        }
        Term::Add(lhs, rhs) => simplify_numeric_binary(lhs, rhs, Term::add, |lhs, rhs| lhs + rhs),
        Term::Sub(lhs, rhs) => simplify_numeric_binary(lhs, rhs, Term::sub, |lhs, rhs| lhs - rhs),
        Term::Mul(lhs, rhs) => simplify_numeric_binary(lhs, rhs, Term::mul, |lhs, rhs| lhs * rhs),
        Term::Div(lhs, rhs) => {
            let lhs = simplify_term(lhs);
            let rhs = simplify_term(rhs);
            match (&lhs, &rhs) {
                (_, Term::Int(1)) => lhs,
                (Term::Int(lhs), Term::Int(rhs)) if *rhs != 0 && lhs % rhs == 0 => {
                    Term::int(lhs / rhs)
                }
                _ => Term::div(lhs, rhs),
            }
        }
        Term::Neg(inner) => match simplify_term(inner) {
            Term::Int(value) => Term::int(-value),
            Term::Real(value) => Term::Real(Rational::new(-value.numerator(), value.denominator())),
            other => Term::neg(other),
        },
    }
}

pub fn simplify_memory(memory: &Memory) -> Memory {
    match memory {
        Memory::Var(name) => Memory::var(name.clone()),
        Memory::Store(inner, index, value) => Memory::store(
            simplify_memory(inner),
            simplify_term(index),
            simplify_term(value),
        ),
    }
}

fn simplify_numeric_binary(
    lhs: &Term,
    rhs: &Term,
    rebuild: fn(Term, Term) -> Term,
    fold: fn(i64, i64) -> i64,
) -> Term {
    let lhs = simplify_term(lhs);
    let rhs = simplify_term(rhs);
    match (&lhs, &rhs) {
        (Term::Int(lhs), Term::Int(rhs)) => Term::int(fold(*lhs, *rhs)),
        (Term::Int(0), _) if matches!(rebuild(Term::int(0), rhs.clone()), Term::Add(_, _)) => rhs,
        (_, Term::Int(0)) if matches!(rebuild(lhs.clone(), Term::int(0)), Term::Add(_, _)) => lhs,
        (_, Term::Int(0)) if matches!(rebuild(lhs.clone(), Term::int(0)), Term::Sub(_, _)) => lhs,
        (_, Term::Int(1)) if matches!(rebuild(lhs.clone(), Term::int(1)), Term::Mul(_, _)) => lhs,
        (Term::Int(1), _) if matches!(rebuild(Term::int(1), rhs.clone()), Term::Mul(_, _)) => rhs,
        (_, Term::Int(0)) if matches!(rebuild(lhs.clone(), Term::int(0)), Term::Mul(_, _)) => {
            Term::int(0)
        }
        (Term::Int(0), _) if matches!(rebuild(Term::int(0), rhs.clone()), Term::Mul(_, _)) => {
            Term::int(0)
        }
        _ => rebuild(lhs, rhs),
    }
}

fn simplify_comparison(
    lhs: &Term,
    rhs: &Term,
    rebuild: fn(Term, Term) -> Formula,
    equal_result: bool,
) -> Formula {
    let lhs = simplify_term(lhs);
    let rhs = simplify_term(rhs);
    if lhs == rhs {
        if equal_result {
            Formula::True
        } else {
            Formula::False
        }
    } else {
        rebuild(lhs, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Sort, Var};

    #[test]
    fn select_of_matching_store_collapse_to_the_stored_value() {
        let term = Term::select(
            Memory::store(Memory::var("m"), Term::int(0), Term::var("x", Sort::Int)),
            Term::int(0),
        );
        assert_eq!(simplify_term(&term), Term::var("x", Sort::Int));
    }

    #[test]
    fn simplifier_keeps_non_matching_store_selects() {
        let term = Term::select(
            Memory::store(Memory::var("m"), Term::int(1), Term::var("x", Sort::Int)),
            Term::int(0),
        );
        assert_eq!(
            simplify_term(&term),
            Term::select(
                Memory::store(Memory::var("m"), Term::int(1), Term::var("x", Sort::Int)),
                Term::int(0),
            )
        );
    }

    #[test]
    fn simplifier_reduces_trivial_formula_equalities() {
        let x = Var::int("x");
        let formula = Formula::eq(Term::Var(x.clone()), Term::Var(x));
        assert_eq!(simplify_formula(&formula), Formula::True);
    }
}
