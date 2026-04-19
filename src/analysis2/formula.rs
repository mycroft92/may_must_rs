//! Solver-independent predicates used by the paper-shaped scaffold.
//!
//! These predicates are deliberately small.  They are set descriptions over
//! program states, not raw SMT ASTs.  Rule code asks an oracle about emptiness,
//! subset, and intersection instead of embedding a solver here.

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
