//! Procedure-summary carriers for the paper's `¬may ⇒ P` and `must ⇒ P`
//! relations.
//!
//! This module stores summary facts but does not decide when they are created
//! or consumed. Those decisions belong in `rules.rs`.

use crate::analysis::formula::Formula;
use std::collections::BTreeMap;

pub type ProcedureName = String;

/// One `¬may ⇒ P` summary fact for a procedure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NotMaySummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

/// One `must ⇒ P` summary fact for a procedure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MustSummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

/// Repository of summary facts keyed by procedure name.
///
/// Both summary relations are stored as small deduplicated vectors because the
/// current milestone needs only the paper-facing facts, not a specialized
/// indexing strategy.
#[derive(Clone, Debug, Default)]
pub struct SummaryTables {
    notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    must: BTreeMap<ProcedureName, Vec<MustSummary>>,
}

impl SummaryTables {
    /// Creates empty summary tables for both summary relations.
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensures storage exists for one procedure's `¬may ⇒ P` summaries.
    pub fn init_notmay(&mut self, procedure: impl Into<ProcedureName>) {
        self.notmay.entry(procedure.into()).or_default();
    }

    /// Ensures storage exists for one procedure's `must ⇒ P` summaries.
    pub fn init_must(&mut self, procedure: impl Into<ProcedureName>) {
        self.must.entry(procedure.into()).or_default();
    }

    /// Returns all recorded `¬may ⇒ P` summaries for one procedure.
    pub fn notmay(&self, procedure: &str) -> &[NotMaySummary] {
        self.notmay.get(procedure).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Returns all recorded `must ⇒ P` summaries for one procedure.
    pub fn must(&self, procedure: &str) -> &[MustSummary] {
        self.must.get(procedure).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Adds one `¬may ⇒ P` summary if it is not already present.
    pub fn add_notmay(&mut self, procedure: impl Into<ProcedureName>, summary: NotMaySummary) {
        let entries = self.notmay.entry(procedure.into()).or_default();
        if !entries.contains(&summary) {
            entries.push(summary);
        }
    }

    /// Adds one `must ⇒ P` summary if it is not already present.
    pub fn add_must(&mut self, procedure: impl Into<ProcedureName>, summary: MustSummary) {
        let entries = self.must.entry(procedure.into()).or_default();
        if !entries.contains(&summary) {
            entries.push(summary);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Formula, Term};

    #[test]
    fn summary_tables_store_unique_entries_per_procedure() {
        let mut tables = SummaryTables::new();
        tables.init_notmay("callee");
        tables.init_must("callee");

        let notmay = NotMaySummary {
            precondition: Formula::True,
            postcondition: Formula::bool_var("bad"),
        };
        let must = MustSummary {
            precondition: Formula::True,
            postcondition: Formula::eq(
                Term::var("x", crate::analysis::formula::Sort::Int),
                Term::int(1),
            ),
        };

        tables.add_notmay("callee", notmay.clone());
        tables.add_notmay("callee", notmay);
        tables.add_must("callee", must.clone());
        tables.add_must("callee", must);

        assert_eq!(tables.notmay("callee").len(), 1);
        assert_eq!(tables.must("callee").len(), 1);
    }
}
