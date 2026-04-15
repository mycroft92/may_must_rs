//! Paper mapping:
//!
//! - Section 2 defines the reachability query shape
//!   `<phi1 ?=> P phi2>` and introduces may, not-may, and must summaries.
//! - Section 4 formalizes those summaries in the compositional rules.
//!
//! This module contains only the shared data model for those ideas. It does not
//! decide queries by itself; `analysis::may_must` owns the current algorithm.

use std::fmt;

/// A lightweight placeholder for the paper's state predicates `phi`.
///
/// Today this is intentionally syntactic. `entails` and `intersects` implement
/// only cheap checks so the prototype can run before Z3-backed predicate
/// reasoning is wired into summary lookup.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Predicate {
    True,
    False,
    Atom(String),
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
}

impl Predicate {
    pub fn atom(value: impl Into<String>) -> Self {
        let value = value.into();
        match value.as_str() {
            "true" | "1" => Predicate::True,
            "false" | "0" => Predicate::False,
            _ => Predicate::Atom(value),
        }
    }

    pub fn and(items: impl IntoIterator<Item = Predicate>) -> Self {
        let mut flattened = Vec::new();
        for item in items {
            match item {
                Predicate::True => {}
                Predicate::False => return Predicate::False,
                Predicate::And(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }

        match flattened.len() {
            0 => Predicate::True,
            1 => flattened.remove(0),
            _ => Predicate::And(flattened),
        }
    }

    pub fn or(items: impl IntoIterator<Item = Predicate>) -> Self {
        let mut flattened = Vec::new();
        for item in items {
            match item {
                Predicate::True => return Predicate::True,
                Predicate::False => {}
                Predicate::Or(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }

        match flattened.len() {
            0 => Predicate::False,
            1 => flattened.remove(0),
            _ => Predicate::Or(flattened),
        }
    }

    pub fn negate(self) -> Self {
        match self {
            Predicate::True => Predicate::False,
            Predicate::False => Predicate::True,
            Predicate::Not(inner) => *inner,
            other => Predicate::Not(Box::new(other)),
        }
    }

    pub fn intersects(&self, other: &Predicate) -> bool {
        !matches!(
            Predicate::and([self.clone(), other.clone()]),
            Predicate::False
        )
    }

    pub fn entails(&self, other: &Predicate) -> bool {
        self == other || matches!(other, Predicate::True) || matches!(self, Predicate::False)
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Predicate::True => write!(f, "true"),
            Predicate::False => write!(f, "false"),
            Predicate::Atom(value) => write!(f, "{value}"),
            Predicate::Not(inner) => write!(f, "!({inner})"),
            Predicate::And(items) => {
                let joined = items
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" & ");
                write!(f, "({joined})")
            }
            Predicate::Or(items) => {
                let joined = items
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" | ");
                write!(f, "({joined})")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Query {
    pub function: String,
    pub pre: Predicate,
    pub post: Predicate,
}

impl Query {
    pub fn new(function: impl Into<String>, pre: Predicate, post: Predicate) -> Self {
        Self {
            function: function.into(),
            pre,
            post,
        }
    }
}

/// The two procedure-summary kinds used by SMASH.
///
/// Paper connection:
/// - `Must` corresponds to `<phi1 must=> P phi2>` and is evidence that some
///   execution reaches the postcondition.
/// - `NotMay` corresponds to `<phi1 not-may=> P phi2>` and is evidence that no
///   execution from the precondition reaches the postcondition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryKind {
    Must,
    NotMay,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Summary {
    pub function: String,
    pub pre: Predicate,
    pub post: Predicate,
    pub kind: SummaryKind,
    pub trace: Vec<String>,
}

impl Summary {
    pub fn must(
        function: impl Into<String>,
        pre: Predicate,
        post: Predicate,
        trace: Vec<String>,
    ) -> Self {
        Self {
            function: function.into(),
            pre,
            post,
            kind: SummaryKind::Must,
            trace,
        }
    }

    pub fn not_may(function: impl Into<String>, pre: Predicate, post: Predicate) -> Self {
        Self {
            function: function.into(),
            pre,
            post,
            kind: SummaryKind::NotMay,
            trace: Vec::new(),
        }
    }
}
