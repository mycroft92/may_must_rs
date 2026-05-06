//! Procedure-summary carriers for the paper's `¬may ⇒ P` and `must ⇒ P`
//! relations.
//!
//! This module stores summary facts but does not decide when they are created
//! or consumed. Those decisions belong in `rules.rs` and `driver.rs`.
//!
//! The current file now has two layers:
//!
//! - `SummaryTables`, the paper-facing raw relations used directly by the
//!   named summary rules
//! - `SummaryRepository` plus `SummaryProvider`, the driver-facing boundary for
//!   discovered summaries and future external candidate sources
//!
//! The important design point is that the driver consumes a provider, not a
//! concrete table implementation. That keeps later imported or generated
//! candidates separate from the paper-facing summary relations themselves.

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

/// Provenance of one summary made visible to the driver.
///
/// The current implementation only produces discovered summaries, but the
/// provider boundary is intentionally separate from summary creation so later
/// sessions can inject file-backed or LLM-backed candidates without changing
/// the rule scheduler.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryProvenance {
    Discovered,
}

/// `¬may ⇒ P` summary candidate paired with its provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvidedNotMaySummary {
    pub summary: NotMaySummary,
    pub provenance: SummaryProvenance,
}

/// `must ⇒ P` summary candidate paired with its provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvidedMustSummary {
    pub summary: MustSummary,
    pub provenance: SummaryProvenance,
}

/// Read-only summary source used by the interprocedural driver.
pub trait SummaryProvider {
    fn notmay_candidates(&self, procedure: &str) -> Vec<ProvidedNotMaySummary>;
    fn must_candidates(&self, procedure: &str) -> Vec<ProvidedMustSummary>;
}

/// Mutable discovered-summary repository used by the current non-LLM route.
///
/// The repository owns the raw paper summary relations and also exposes them
/// through `SummaryProvider`, which gives the driver a stable boundary between
/// "where summaries come from" and "how rules use them".
/// Current non-LLM discovered-summary store plus provider façade.
#[derive(Clone, Debug, Default)]
pub struct SummaryRepository {
    tables: SummaryTables,
}

impl SummaryRepository {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn tables(&self) -> &SummaryTables {
        &self.tables
    }

    pub fn tables_mut(&mut self) -> &mut SummaryTables {
        &mut self.tables
    }

    pub fn init_procedure(&mut self, procedure: impl Into<ProcedureName> + Clone) {
        let procedure = procedure.into();
        self.tables.init_notmay(procedure.clone());
        self.tables.init_must(procedure);
    }

    pub fn record_notmay_discovered(
        &mut self,
        procedure: impl Into<ProcedureName>,
        summary: NotMaySummary,
    ) {
        self.tables.add_notmay(procedure, summary);
    }

    pub fn record_must_discovered(
        &mut self,
        procedure: impl Into<ProcedureName>,
        summary: MustSummary,
    ) {
        self.tables.add_must(procedure, summary);
    }
}

impl SummaryProvider for SummaryRepository {
    fn notmay_candidates(&self, procedure: &str) -> Vec<ProvidedNotMaySummary> {
        self.tables
            .notmay(procedure)
            .iter()
            .cloned()
            .map(|summary| ProvidedNotMaySummary {
                summary,
                provenance: SummaryProvenance::Discovered,
            })
            .collect()
    }

    fn must_candidates(&self, procedure: &str) -> Vec<ProvidedMustSummary> {
        self.tables
            .must(procedure)
            .iter()
            .cloned()
            .map(|summary| ProvidedMustSummary {
                summary,
                provenance: SummaryProvenance::Discovered,
            })
            .collect()
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

    #[test]
    fn summary_repository_exposes_discovered_entries_through_the_provider_boundary() {
        let mut repository = SummaryRepository::new();
        repository.init_procedure("callee");
        repository.record_notmay_discovered(
            "callee",
            NotMaySummary {
                precondition: Formula::True,
                postcondition: Formula::bool_var("bad"),
            },
        );
        repository.record_must_discovered(
            "callee",
            MustSummary {
                precondition: Formula::True,
                postcondition: Formula::eq(
                    Term::var("x", crate::analysis::formula::Sort::Int),
                    Term::int(1),
                ),
            },
        );

        let notmay = repository.notmay_candidates("callee");
        let must = repository.must_candidates("callee");

        assert_eq!(notmay.len(), 1);
        assert_eq!(must.len(), 1);
        assert_eq!(notmay[0].provenance, SummaryProvenance::Discovered);
        assert_eq!(must[0].provenance, SummaryProvenance::Discovered);
    }
}
