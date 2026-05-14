#![allow(dead_code)]

use crate::common::adapter::ReturnSummary;
use crate::common::formula::Formula;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopContext {
    pub function: String,
    pub loop_id: usize,
}

pub trait CandidateProvider {
    fn function_summary(&self, _callee: &str) -> Option<ReturnSummary> {
        None
    }

    fn loop_invariant(&self, _ctx: &LoopContext) -> Vec<Formula> {
        Vec::new()
    }
}

#[derive(Clone, Debug, Default)]
pub struct NoProvider;

impl CandidateProvider for NoProvider {}

#[derive(Clone, Debug, Default)]
pub struct ManualProvider {
    function_summaries: BTreeMap<String, ReturnSummary>,
}

impl ManualProvider {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function_summary(mut self, summary: ReturnSummary) -> Self {
        self.add_function_summary(summary);
        self
    }

    pub fn add_function_summary(&mut self, summary: ReturnSummary) {
        self.function_summaries
            .insert(summary.function.clone(), summary);
    }

    pub fn function_summaries(&self) -> &BTreeMap<String, ReturnSummary> {
        &self.function_summaries
    }
}

impl CandidateProvider for ManualProvider {
    fn function_summary(&self, callee: &str) -> Option<ReturnSummary> {
        self.function_summaries.get(callee).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fake_summary(name: &str) -> ReturnSummary {
        ReturnSummary {
            function: name.to_string(),
            formal_parameters: vec![],
            retval_name: format!("{name}$__retval"),
            relation: Formula::True,
            write_effects: Vec::new(),
        }
    }

    #[test]
    fn no_provider_returns_none() {
        let provider = NoProvider;
        assert!(provider.function_summary("foo").is_none());
    }

    #[test]
    fn manual_provider_returns_inserted_summary() {
        let summary = fake_summary("callee");
        let provider = ManualProvider::new().with_function_summary(summary.clone());
        assert_eq!(provider.function_summary("callee"), Some(summary));
    }

    #[test]
    fn manual_provider_misses_unknown_callee() {
        let provider = ManualProvider::new();
        assert!(provider.function_summary("missing").is_none());
    }
}
