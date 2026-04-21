//! Solver-independent predicates used by the paper-shaped scaffold.
//!
//! These predicates are deliberately small.  They are set descriptions over
//! program states, not raw SMT ASTs.  Rule code asks an oracle about emptiness,
//! subset, and intersection instead of embedding a solver here.
//!
//! Paper correspondence:
//!
//! ```text
//! Predicate -> phi, beta, theta, query pre/post, summary pre/post
//! ```
//!
//! This file intentionally stays above SMT. Encoding these predicates into Z3
//! belongs in a future analysis-level encoding/oracle layer, not here.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Predicate {
    True,
    False,
    Atom(String),
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
}

impl Predicate {
    pub fn atom(name: impl Into<String>) -> Self {
        Self::Atom(name.into())
    }

    pub fn not(predicate: Predicate) -> Self {
        match predicate {
            Predicate::True => Predicate::False,
            Predicate::False => Predicate::True,
            Predicate::Not(inner) => *inner,
            other => Predicate::Not(Box::new(other)),
        }
    }

    pub fn and(parts: impl IntoIterator<Item = Predicate>) -> Self {
        let mut flattened = Vec::new();
        for part in parts {
            match part {
                Predicate::False => return Predicate::False,
                Predicate::True => {}
                Predicate::And(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }
        match flattened.len() {
            0 => Predicate::True,
            1 => flattened.pop().expect("one element"),
            _ => {
                flattened.sort();
                flattened.dedup();
                Predicate::And(flattened)
            }
        }
    }

    pub fn or(parts: impl IntoIterator<Item = Predicate>) -> Self {
        let mut flattened = Vec::new();
        for part in parts {
            match part {
                Predicate::True => return Predicate::True,
                Predicate::False => {}
                Predicate::Or(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }
        match flattened.len() {
            0 => Predicate::False,
            1 => flattened.pop().expect("one element"),
            _ => {
                flattened.sort();
                flattened.dedup();
                Predicate::Or(flattened)
            }
        }
    }

    pub fn intersection(self, other: Predicate) -> Predicate {
        Predicate::and([self, other])
    }

    pub fn union(self, other: Predicate) -> Predicate {
        Predicate::or([self, other])
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Predicate::True => write!(f, "true"),
            Predicate::False => write!(f, "false"),
            Predicate::Atom(name) => write!(f, "{name}"),
            Predicate::Not(inner) => write!(f, "!({inner})"),
            Predicate::And(parts) => {
                write!(f, "(")?;
                for (idx, part) in parts.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " && ")?;
                    }
                    write!(f, "{part}")?;
                }
                write!(f, ")")
            }
            Predicate::Or(parts) => {
                write!(f, "(")?;
                for (idx, part) in parts.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " || ")?;
                    }
                    write!(f, "{part}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Rewrites symbol occurrences in a predicate using exact token boundaries.
///
/// This lives in `analysis::formula` (instead of `main`) because it is a
/// predicate-vocabulary transformation used by interprocedural query plumbing
/// and should be reusable by analysis modules independent of CLI wiring.
pub fn substitute_predicate_symbols(
    predicate: Predicate,
    replacements: &BTreeMap<String, String>,
) -> Predicate {
    if replacements.is_empty() {
        return predicate;
    }
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Atom(atom) => Predicate::atom(substitute_atom_symbols(&atom, replacements)),
        Predicate::Not(inner) => Predicate::not(substitute_predicate_symbols(*inner, replacements)),
        Predicate::And(parts) => Predicate::and(
            parts
                .into_iter()
                .map(|part| substitute_predicate_symbols(part, replacements)),
        ),
        Predicate::Or(parts) => Predicate::or(
            parts
                .into_iter()
                .map(|part| substitute_predicate_symbols(part, replacements)),
        ),
    }
}

/// Collects symbolic tokens used by predicate atoms (`%x`, `@g`, `retval_f`,
/// memory-shaped symbols).
pub fn collect_predicate_symbols(predicate: &Predicate) -> BTreeSet<String> {
    let mut symbols = BTreeSet::new();
    collect_predicate_symbols_into(predicate, &mut symbols);
    symbols
}

pub fn looks_like_memory_symbol(token: &str) -> bool {
    token == "mem" || token == "mem'" || token.starts_with("mem_")
}

fn substitute_atom_symbols(atom: &str, replacements: &BTreeMap<String, String>) -> String {
    let mut rewritten = atom.to_string();
    let mut ordered = replacements.iter().collect::<Vec<_>>();
    ordered.sort_by(|(left, _), (right, _)| right.len().cmp(&left.len()));
    for (from, to) in ordered {
        rewritten = replace_symbol_exact(&rewritten, from, to);
    }
    rewritten
}

fn replace_symbol_exact(input: &str, from: &str, to: &str) -> String {
    if from.is_empty() || from == to {
        return input.to_string();
    }
    let mut out = String::new();
    let mut index = 0usize;
    while index < input.len() {
        let Some(relative) = input[index..].find(from) else {
            out.push_str(&input[index..]);
            break;
        };
        let found = index + relative;
        let end = found + from.len();
        let left_boundary = if found == 0 {
            true
        } else {
            !is_symbol_body_char(input[..found].chars().next_back().unwrap_or(' '))
        };
        let right_boundary = if end >= input.len() {
            true
        } else {
            !is_symbol_body_char(input[end..].chars().next().unwrap_or(' '))
        };
        if left_boundary && right_boundary {
            out.push_str(&input[index..found]);
            out.push_str(to);
            index = end;
        } else {
            out.push_str(&input[index..end]);
            index = end;
        }
    }
    out
}

fn collect_predicate_symbols_into(predicate: &Predicate, symbols: &mut BTreeSet<String>) {
    match predicate {
        Predicate::True | Predicate::False => {}
        Predicate::Atom(atom) => collect_atom_symbols(atom, symbols),
        Predicate::Not(inner) => collect_predicate_symbols_into(inner, symbols),
        Predicate::And(parts) | Predicate::Or(parts) => {
            for part in parts {
                collect_predicate_symbols_into(part, symbols);
            }
        }
    }
}

fn collect_atom_symbols(atom: &str, symbols: &mut BTreeSet<String>) {
    let chars = atom.chars().collect::<Vec<_>>();
    let mut index = 0usize;
    while index < chars.len() {
        let c = chars[index];
        if c == '%' || c == '@' {
            let start = index;
            index += 1;
            while index < chars.len() && is_symbol_body_char(chars[index]) {
                index += 1;
            }
            symbols.insert(chars[start..index].iter().collect());
            continue;
        }
        if c.is_ascii_alphabetic() {
            let start = index;
            index += 1;
            while index < chars.len() && is_symbol_body_char(chars[index]) {
                index += 1;
            }
            let token = chars[start..index].iter().collect::<String>();
            if token.starts_with("retval_") || looks_like_memory_symbol(&token) {
                symbols.insert(token);
            }
            continue;
        }
        index += 1;
    }
}

fn is_symbol_body_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '\'' | '.')
}
