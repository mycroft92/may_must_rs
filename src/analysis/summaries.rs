//! Procedure summaries and top-level queries in paper vocabulary.
//!
//! Paper correspondence:
//!
//! ```text
//! ProcedureSummary     -> boundary summary for a procedure
//! SummaryKind::Must    -> must summary
//! SummaryKind::NotMay  -> not-may summary
//! ReachabilityQuery    -> query Q
//! query.pre / query.post -> boundary predicates for the query
//! ```

use crate::analysis::formula::Predicate;
use crate::analysis::vocabulary::EdgeId;
use crate::analysis::vocabulary::ProcedureName;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SummaryKind {
    Must,
    NotMay,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProcedureSummary {
    pub procedure: ProcedureName,
    pub kind: SummaryKind,
    pub pre: Predicate,
    pub post: Predicate,
    pub evidence: SummaryEvidence,
}

impl ProcedureSummary {
    pub fn must(
        procedure: impl Into<ProcedureName>,
        pre: Predicate,
        post: Predicate,
        witness: impl Into<String>,
    ) -> Self {
        Self {
            procedure: procedure.into(),
            kind: SummaryKind::Must,
            pre,
            post,
            evidence: SummaryEvidence::Witness(witness.into()),
        }
    }

    pub fn not_may(
        procedure: impl Into<ProcedureName>,
        pre: Predicate,
        post: Predicate,
        proof: impl Into<String>,
    ) -> Self {
        Self {
            procedure: procedure.into(),
            kind: SummaryKind::NotMay,
            pre,
            post,
            evidence: SummaryEvidence::Proof(proof.into()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryEvidence {
    Witness(String),
    Proof(String),
    Pending,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReachabilityQuery {
    pub procedure: ProcedureName,
    pub pre: Predicate,
    pub post: Predicate,
    pub target_assertion: Option<EdgeId>,
}

impl ReachabilityQuery {
    pub fn new(procedure: impl Into<ProcedureName>, pre: Predicate, post: Predicate) -> Self {
        Self {
            procedure: procedure.into(),
            pre,
            post,
            target_assertion: None,
        }
    }

    pub fn with_target_assertion(mut self, target_assertion: EdgeId) -> Self {
        self.target_assertion = Some(target_assertion);
        self
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SummaryTable {
    by_procedure: BTreeMap<ProcedureName, Vec<ProcedureSummary>>,
}

impl SummaryTable {
    pub fn add(&mut self, summary: ProcedureSummary) {
        let summaries = self
            .by_procedure
            .entry(summary.procedure.clone())
            .or_default();
        if summaries.iter().any(|existing| existing == &summary) {
            return;
        }
        summaries.push(summary);
    }

    pub fn for_procedure(&self, procedure: &ProcedureName) -> &[ProcedureSummary] {
        self.by_procedure
            .get(procedure)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}
