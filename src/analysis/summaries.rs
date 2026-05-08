use crate::analysis::formula::Formula;
use std::collections::BTreeMap;

pub type ProcedureName = String;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct NotMaySummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MustSummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

#[derive(Clone, Debug, Default)]
pub struct SummaryTables {
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    pub must: BTreeMap<ProcedureName, Vec<MustSummary>>,
}

impl SummaryTables {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn init_notmay(&mut self, name: impl Into<String>) {
        self.notmay.entry(name.into()).or_default();
    }

    pub fn init_must(&mut self, name: impl Into<String>) {
        self.must.entry(name.into()).or_default();
    }

    pub fn notmay(&self, name: &str) -> &[NotMaySummary] {
        self.notmay.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    pub fn must(&self, name: &str) -> &[MustSummary] {
        self.must.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    pub fn add_notmay(&mut self, name: impl Into<String>, summary: NotMaySummary) -> bool {
        let entries = self.notmay.entry(name.into()).or_default();
        if entries.contains(&summary) {
            false
        } else {
            entries.push(summary);
            true
        }
    }

    pub fn add_must(&mut self, name: impl Into<String>, summary: MustSummary) -> bool {
        let entries = self.must.entry(name.into()).or_default();
        if entries.contains(&summary) {
            false
        } else {
            entries.push(summary);
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn notmay_deduplicates() {
        let mut tables = SummaryTables::new();
        let summary = NotMaySummary {
            precondition: Formula::bool_var("p"),
            postcondition: Formula::bool_var("q"),
        };
        assert!(tables.add_notmay("f", summary.clone()));
        assert!(!tables.add_notmay("f", summary));
    }

    #[test]
    fn must_deduplicates() {
        let mut tables = SummaryTables::new();
        let summary = MustSummary {
            precondition: Formula::True,
            postcondition: Formula::False,
        };
        assert!(tables.add_must("f", summary.clone()));
        assert!(!tables.add_must("f", summary));
    }

    #[test]
    fn missing_tables_return_empty_slices() {
        let tables = SummaryTables::new();
        assert!(tables.notmay("missing").is_empty());
        assert!(tables.must("missing").is_empty());
    }
}
