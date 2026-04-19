//! Predicate and transition oracles for the paper-shaped rules.
//!
//! The paper rules are written in terms of set operations.  This module keeps
//! those decisions abstract so the same rules can later be backed by SMT,
//! predicate abstraction, or hand-authored tests.
//!
//! Paper correspondence:
//!
//! ```text
//! PredicateOracle::is_empty / intersects / subset
//!   -> set reasoning over predicates
//! TransitionOracle::post_under_approx
//!   -> choose theta subset Post(Gamma_e, source)
//! TransitionOracle::pre_over_approx
//!   -> choose beta with Pre(Gamma_e, target) subset beta
//! ```
//!
//! This file defines the interface the rules need. The future SMT-backed
//! implementation should plug in here rather than changing `rules.rs`.

use crate::analysis::cfg::PaperEdge;
use crate::analysis::formula::Predicate;
use std::fmt;
use z3::ast::Bool;
use z3::{SatResult, Solver};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleError {
    UnknownPredicate(String),
    UnknownTransition(String),
}

impl fmt::Display for OracleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OracleError::UnknownPredicate(reason) => write!(f, "unknown predicate check: {reason}"),
            OracleError::UnknownTransition(reason) => {
                write!(f, "unknown transition image: {reason}")
            }
        }
    }
}

pub type OracleResult<T> = Result<T, OracleError>;

pub trait PredicateOracle {
    fn is_empty(&self, predicate: &Predicate) -> OracleResult<bool>;

    fn intersects(&self, left: &Predicate, right: &Predicate) -> OracleResult<bool> {
        self.is_empty(&Predicate::and([left.clone(), right.clone()]))
            .map(|empty| !empty)
    }

    fn subset(&self, left: &Predicate, right: &Predicate) -> OracleResult<bool> {
        self.is_empty(&Predicate::and([
            left.clone(),
            Predicate::not(right.clone()),
        ]))
    }
}

pub trait TransitionOracle {
    /// Returns a `theta` for the paper's forward rule step.
    ///
    /// Contract:
    ///
    /// ```text
    /// theta subset Post(Gamma_e, source)
    /// ```
    ///
    /// Inputs:
    ///
    /// - `edge` identifies the concrete edge relation `Gamma_e`;
    /// - `source` is a predicate over source states, typically
    ///   `Omega_n1 ∩ phi1`.
    ///
    /// Role in the paper:
    ///
    /// - `MUST-POST` needs some definitely reachable successor set;
    /// - this method computes or chooses that under-approximate successor set.
    ///
    /// Allowed behavior:
    ///
    /// - it may return a smaller-than-ideal `theta`;
    /// - it must not claim impossible successor states.
    fn post_under_approx(&self, edge: &PaperEdge, source: &Predicate) -> OracleResult<Predicate>;

    /// Returns a `beta` for the paper's backward rule step.
    ///
    /// Contract:
    ///
    /// ```text
    /// Pre(Gamma_e, target) subset beta
    /// ```
    ///
    /// Inputs:
    ///
    /// - `edge` identifies the concrete edge relation `Gamma_e`;
    /// - `target` is a predicate over destination states, typically `phi2`.
    ///
    /// Role in the paper:
    ///
    /// - `NOTMAY-PRE` needs a safe predecessor over-approximation;
    /// - this method computes or chooses that predecessor set.
    ///
    /// Allowed behavior:
    ///
    /// - it may return a larger-than-ideal `beta`;
    /// - it must not exclude real predecessors that can reach `target`.
    fn pre_over_approx(&self, edge: &PaperEdge, target: &Predicate) -> OracleResult<Predicate>;
}

/// A tiny syntactic oracle for scaffold tests.
///
/// This is not the final reasoning engine.  It knows `false`, direct
/// contradictions such as `p && !p`, and simple structural subset facts.
#[derive(Clone, Copy, Debug, Default)]
pub struct SyntacticOracle;

impl PredicateOracle for SyntacticOracle {
    fn is_empty(&self, predicate: &Predicate) -> OracleResult<bool> {
        Ok(is_syntactically_empty(predicate))
    }

    fn subset(&self, left: &Predicate, right: &Predicate) -> OracleResult<bool> {
        if left == right || matches!(left, Predicate::False) || matches!(right, Predicate::True) {
            return Ok(true);
        }
        if let Predicate::And(parts) = left {
            if parts.iter().any(|part| part == right) {
                return Ok(true);
            }
        }
        PredicateOracle::is_empty(
            self,
            &Predicate::and([left.clone(), Predicate::not(right.clone())]),
        )
    }
}

impl TransitionOracle for SyntacticOracle {
    fn post_under_approx(&self, edge: &PaperEdge, _source: &Predicate) -> OracleResult<Predicate> {
        edge.transition
            .post_under_approx
            .clone()
            .ok_or_else(|| OracleError::UnknownTransition(format!("{} has no theta", edge.id)))
    }

    fn pre_over_approx(&self, edge: &PaperEdge, _target: &Predicate) -> OracleResult<Predicate> {
        edge.transition
            .pre_over_approx
            .clone()
            .ok_or_else(|| OracleError::UnknownTransition(format!("{} has no beta", edge.id)))
    }
}

/// SMT-backed predicate oracle over `analysis::formula::Predicate`.
///
/// Current encoding model:
///
/// - `true` / `false` map to SMT Boolean constants;
/// - predicate atoms map to SMT Boolean symbols;
/// - `not` / `and` / `or` map structurally.
#[derive(Clone, Copy, Debug, Default)]
pub struct SmtPredicateOracle;

impl SmtPredicateOracle {
    fn encode_predicate(predicate: &Predicate) -> Bool {
        match predicate {
            Predicate::True => Bool::from_bool(true),
            Predicate::False => Bool::from_bool(false),
            Predicate::Atom(name) => encode_atom(name),
            Predicate::Not(inner) => Self::encode_predicate(inner).not(),
            Predicate::And(parts) => {
                let encoded = parts.iter().map(Self::encode_predicate).collect::<Vec<_>>();
                let refs = encoded.iter().collect::<Vec<_>>();
                Bool::and(&refs)
            }
            Predicate::Or(parts) => {
                let encoded = parts.iter().map(Self::encode_predicate).collect::<Vec<_>>();
                let refs = encoded.iter().collect::<Vec<_>>();
                Bool::or(&refs)
            }
        }
    }

    fn satisfiable(&self, predicate: &Predicate) -> OracleResult<bool> {
        let solver = Solver::new();
        solver.assert(Self::encode_predicate(predicate));
        match solver.check() {
            SatResult::Sat => Ok(true),
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err(OracleError::UnknownPredicate(format!(
                "SMT returned unknown for {predicate}",
            ))),
        }
    }
}

impl PredicateOracle for SmtPredicateOracle {
    fn is_empty(&self, predicate: &Predicate) -> OracleResult<bool> {
        self.satisfiable(predicate).map(|sat| !sat)
    }
}

fn encode_atom(atom: &str) -> Bool {
    if atom.eq_ignore_ascii_case("true") {
        return Bool::from_bool(true);
    }
    if atom.eq_ignore_ascii_case("false") {
        return Bool::from_bool(false);
    }
    Bool::new_const(atom_symbol(atom))
}

fn atom_symbol(atom: &str) -> String {
    let mut symbol = String::from("pred_");
    for byte in atom.as_bytes() {
        let c = *byte as char;
        if c.is_ascii_alphanumeric() || c == '_' {
            symbol.push(c);
        } else {
            symbol.push('_');
            symbol.push_str(&format!("{byte:02x}"));
        }
    }
    if symbol == "pred_" {
        symbol.push_str("empty");
    }
    symbol
}

fn is_syntactically_empty(predicate: &Predicate) -> bool {
    match predicate {
        Predicate::False => true,
        Predicate::True | Predicate::Atom(_) => false,
        Predicate::Not(inner) => matches!(inner.as_ref(), Predicate::True),
        Predicate::Or(parts) => parts.iter().all(is_syntactically_empty),
        Predicate::And(parts) => {
            if parts.iter().any(is_syntactically_empty) {
                return true;
            }
            for part in parts {
                if parts
                    .iter()
                    .any(|other| other == &Predicate::not(part.clone()))
                {
                    return true;
                }
            }
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smt_predicate_oracle_detects_contradiction() {
        let oracle = SmtPredicateOracle;
        let p = Predicate::atom("p");
        let contradictory = Predicate::and([p.clone(), Predicate::not(p)]);
        assert!(oracle.is_empty(&contradictory).unwrap());
    }

    #[test]
    fn smt_predicate_oracle_subset_uses_solver() {
        let oracle = SmtPredicateOracle;
        let p = Predicate::atom("p");
        let p_or_q = Predicate::or([Predicate::atom("p"), Predicate::atom("q")]);
        assert!(oracle.subset(&p, &p_or_q).unwrap());
    }
}
