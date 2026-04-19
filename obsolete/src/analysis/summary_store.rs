//! SMT-backed procedure-summary storage.
//!
//! This is deliberately separate from both transfer functions and the raw Z3
//! wrapper. Transfer functions should produce path states and boundary
//! relations. The store decides which cached `Must`/`NotMay` summaries are
//! applicable to a new query.

#![allow(dead_code)]

use crate::analysis::domain::SummaryKind;
use crate::analysis::may_must_rules::{applicable_must_summary, applicable_not_may_summary};
use crate::analysis::predicates::{Formula, PredicateResult};
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SummaryTarget {
    Return,
    AssertionViolation(String),
}

impl SummaryTarget {
    pub fn assertion(name: impl Into<String>) -> Self {
        Self::AssertionViolation(name.into())
    }
}

impl fmt::Display for SummaryTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SummaryTarget::Return => write!(f, "return"),
            SummaryTarget::AssertionViolation(name) => write!(f, "violate:{name}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryEvidence {
    WitnessTrace(Vec<String>),
    NotMayProof { reason: String },
    Pending,
}

/// A typed, function-boundary summary.
///
/// `pre`, `post`, and `relation` are all expressed with solver-independent
/// formulas. They can reference summary boundary symbols such as
/// `SummaryPhase::Pre` parameters and `SummaryPhase::Post` return values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSummary {
    pub function: String,
    pub kind: SummaryKind,
    pub target: SummaryTarget,
    pub pre: Formula,
    pub post: Formula,
    pub relation: Formula,
    pub evidence: SummaryEvidence,
}

impl FunctionSummary {
    pub fn must(
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        relation: Formula,
        trace: Vec<String>,
    ) -> Self {
        Self {
            function: function.into(),
            kind: SummaryKind::Must,
            target,
            pre,
            post,
            relation,
            evidence: SummaryEvidence::WitnessTrace(trace),
        }
    }

    pub fn not_may(
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            function: function.into(),
            kind: SummaryKind::NotMay,
            target,
            pre,
            post,
            relation: Formula::True,
            evidence: SummaryEvidence::NotMayProof {
                reason: reason.into(),
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtQuery {
    pub function: String,
    pub target: SummaryTarget,
    pub pre: Formula,
    pub post: Formula,
}

impl SmtQuery {
    pub fn new(
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
    ) -> Self {
        Self {
            function: function.into(),
            target,
            pre,
            post,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct FunctionSummarySet {
    must: Vec<FunctionSummary>,
    not_may: Vec<FunctionSummary>,
}

impl FunctionSummarySet {
    pub fn must(&self) -> &[FunctionSummary] {
        &self.must
    }

    pub fn not_may(&self) -> &[FunctionSummary] {
        &self.not_may
    }
}

#[derive(Clone, Debug, Default)]
pub struct SummaryStore {
    by_function: HashMap<String, FunctionSummarySet>,
}

impl SummaryStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, summary: FunctionSummary) -> bool {
        let summaries = self
            .by_function
            .entry(summary.function.clone())
            .or_default();
        let target = match summary.kind {
            SummaryKind::Must => &mut summaries.must,
            SummaryKind::NotMay => &mut summaries.not_may,
        };

        if target.iter().any(|existing| existing == &summary) {
            false
        } else {
            target.push(summary);
            true
        }
    }

    pub fn add_must(
        &mut self,
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        relation: Formula,
        trace: Vec<String>,
    ) -> bool {
        self.add(FunctionSummary::must(
            function, target, pre, post, relation, trace,
        ))
    }

    pub fn add_not_may(
        &mut self,
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        reason: impl Into<String>,
    ) -> bool {
        self.add(FunctionSummary::not_may(
            function, target, pre, post, reason,
        ))
    }

    pub fn get(&self, function: &str) -> Option<&FunctionSummarySet> {
        self.by_function.get(function)
    }

    pub fn must_count(&self) -> usize {
        self.by_function
            .values()
            .map(|summaries| summaries.must.len())
            .sum()
    }

    pub fn not_may_count(&self) -> usize {
        self.by_function
            .values()
            .map(|summaries| summaries.not_may.len())
            .sum()
    }

    pub fn find_applicable_must(
        &self,
        query: &SmtQuery,
    ) -> PredicateResult<Option<&FunctionSummary>> {
        let Some(summaries) = self.by_function.get(&query.function) else {
            return Ok(None);
        };

        for summary in &summaries.must {
            if applicable_must_summary(summary, query)?.holds {
                return Ok(Some(summary));
            }
        }

        Ok(None)
    }

    pub fn find_applicable_not_may(
        &self,
        query: &SmtQuery,
    ) -> PredicateResult<Option<&FunctionSummary>> {
        let Some(summaries) = self.by_function.get(&query.function) else {
            return Ok(None);
        };

        for summary in &summaries.not_may {
            if applicable_not_may_summary(summary, query)?.holds {
                return Ok(Some(summary));
            }
        }

        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::predicates::IntTerm;
    use crate::analysis::state::SummaryPhase;

    #[test]
    fn store_deduplicates_identical_summaries() {
        let mut store = SummaryStore::new();
        let target = SummaryTarget::assertion("a0");

        assert!(store.add_must(
            "main",
            target.clone(),
            Formula::True,
            Formula::True,
            Formula::True,
            vec!["may_assert(0)".to_string()],
        ));
        assert!(!store.add_must(
            "main",
            target,
            Formula::True,
            Formula::True,
            Formula::True,
            vec!["may_assert(0)".to_string()],
        ));

        assert_eq!(store.must_count(), 1);
        assert_eq!(store.not_may_count(), 0);
    }

    #[test]
    fn not_may_lookup_uses_smt_entailment() {
        let mut store = SummaryStore::new();
        let target = SummaryTarget::assertion("a0");
        let param = IntTerm::summary_param(SummaryPhase::Pre, 0);

        store.add_not_may(
            "checked",
            target.clone(),
            Formula::gt(param.clone(), IntTerm::int(0)),
            Formula::True,
            "positive inputs cannot violate a0",
        );

        let query = SmtQuery::new(
            "checked",
            target,
            Formula::gt(param, IntTerm::int(10)),
            Formula::True,
        );

        assert!(store.find_applicable_not_may(&query).unwrap().is_some());
    }

    #[test]
    fn must_lookup_requires_matching_target() {
        let mut store = SummaryStore::new();

        store.add_must(
            "main",
            SummaryTarget::assertion("a0"),
            Formula::True,
            Formula::True,
            Formula::True,
            vec!["a0".to_string()],
        );

        let query = SmtQuery::new(
            "main",
            SummaryTarget::assertion("a1"),
            Formula::True,
            Formula::True,
        );

        assert!(store.find_applicable_must(&query).unwrap().is_none());
    }
}
