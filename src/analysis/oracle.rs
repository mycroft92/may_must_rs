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
use z3::ast::{Array, Bool, Int};
use z3::{SatResult, Solver, Sort};

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
/// - most predicate atoms map to SMT Boolean symbols;
/// - memory-shaped atoms such as `store/load` are mapped to
///   `Array[Int -> Int]` constraints;
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
    if let Some(encoded) = encode_semantic_atom(atom) {
        return encoded;
    }
    Bool::new_const(atom_symbol(atom))
}

fn atom_symbol(atom: &str) -> String {
    symbol_with_prefix("pred_", atom)
}

fn int_symbol(name: &str) -> String {
    symbol_with_prefix("int_", name)
}

fn array_symbol(name: &str) -> String {
    symbol_with_prefix("arr_", name)
}

fn symbol_with_prefix(prefix: &str, raw: &str) -> String {
    let mut symbol = String::from(prefix);
    for byte in raw.as_bytes() {
        let c = *byte as char;
        if c.is_ascii_alphanumeric() || c == '_' {
            symbol.push(c);
        } else {
            symbol.push('_');
            symbol.push_str(&format!("{byte:02x}"));
        }
    }
    if symbol == prefix {
        symbol.push_str("empty");
    }
    symbol
}

fn encode_semantic_atom(atom: &str) -> Option<Bool> {
    let core = strip_edge_suffix(atom);
    let (lhs, rhs) = parse_assignment(core)?;
    if let Some((func, args)) = parse_call(rhs) {
        return match func {
            "store" => encode_store_assignment(lhs, &args),
            "load" => encode_load_assignment(lhs, &args),
            _ => None,
        };
    }

    if looks_like_memory_name(lhs) && looks_like_memory_name(rhs) {
        return Some(array_var(lhs).eq(&array_var(rhs)));
    }

    Some(int_var(lhs).eq(&int_term(rhs)))
}

fn strip_edge_suffix(atom: &str) -> &str {
    atom.rsplit_once(" @")
        .map(|(core, _)| core)
        .unwrap_or(atom)
        .trim()
}

fn parse_assignment(atom: &str) -> Option<(&str, &str)> {
    let (lhs, rhs) = atom.split_once('=')?;
    Some((lhs.trim(), rhs.trim()))
}

fn parse_call(rhs: &str) -> Option<(&str, Vec<&str>)> {
    let open = rhs.find('(')?;
    if !rhs.ends_with(')') || open + 1 > rhs.len() {
        return None;
    }
    let func = rhs[..open].trim();
    let args = rhs[open + 1..rhs.len() - 1]
        .split(',')
        .map(str::trim)
        .filter(|arg| !arg.is_empty())
        .collect::<Vec<_>>();
    Some((func, args))
}

fn encode_store_assignment(lhs: &str, args: &[&str]) -> Option<Bool> {
    if args.len() != 2 {
        return None;
    }
    let post_mem = array_var(lhs);
    let pre_mem_name = unprimed_name(lhs).unwrap_or(lhs);
    let pre_mem = array_var(pre_mem_name);
    let ptr = int_term(args[0]);
    let value = int_term(args[1]);
    Some(post_mem.eq(&pre_mem.store(&ptr, &value)))
}

fn encode_load_assignment(lhs: &str, args: &[&str]) -> Option<Bool> {
    let (mem_name, ptr_name) = match args {
        [ptr] => ("mem", *ptr),
        [mem, ptr] => (*mem, *ptr),
        _ => return None,
    };
    let mem = array_var(mem_name);
    let ptr = int_term(ptr_name);
    let lhs_val = int_var(lhs);
    Some(mem.select(&ptr).eq(&lhs_val))
}

fn unprimed_name(name: &str) -> Option<&str> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return None;
    }
    trimmed.strip_suffix('\'').or(Some(trimmed))
}

fn looks_like_memory_name(name: &str) -> bool {
    let trimmed = name.trim();
    trimmed == "mem" || trimmed.starts_with("mem")
}

fn int_term(token: &str) -> Int {
    let trimmed = token.trim();
    if let Ok(value) = trimmed.parse::<i64>() {
        return Int::from_i64(value);
    }
    Int::new_const(int_symbol(trimmed))
}

fn int_var(name: &str) -> Int {
    Int::new_const(int_symbol(name.trim()))
}

fn array_var(name: &str) -> Array {
    let int_sort = Sort::int();
    Array::new_const(array_symbol(name.trim()), &int_sort, &int_sort)
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

    #[test]
    fn smt_predicate_oracle_uses_array_store_load_semantics() {
        let oracle = SmtPredicateOracle;
        let memory_step = Predicate::atom("mem' = store(%p, 7) @e0");
        let load_step = Predicate::atom("%x = load(mem', %p) @e1");
        let not_expected_value = Predicate::not(Predicate::atom("%x = 7"));
        let contradictory = Predicate::and([memory_step, load_step, not_expected_value]);
        assert!(oracle.is_empty(&contradictory).unwrap());
    }

    #[test]
    fn smt_predicate_oracle_subset_with_array_reasoning() {
        let oracle = SmtPredicateOracle;
        let left = Predicate::and([
            Predicate::atom("mem' = store(%p, 7) @e0"),
            Predicate::atom("%x = load(mem', %p) @e1"),
        ]);
        let right = Predicate::atom("%x = 7");
        assert!(oracle.subset(&left, &right).unwrap());
    }
}
