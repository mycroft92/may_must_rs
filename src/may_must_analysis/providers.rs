//! External and manual summary provider seam.
//!
//! The driver can analyse a callee automatically, but sometimes a summary must
//! come from outside the analysis — for example, a hand-written stub for a
//! library function or a summary injected by a test harness.
//!
//! This module defines the [`CandidateProvider`] trait as the injection point.
//! The driver queries a provider before attempting to synthesise a summary
//! automatically.  Two implementations are shipped:
//!
//! - [`NoProvider`] — the null object; always returns nothing.
//! - [`ManualProvider`] — a map of function names to hand-supplied
//!   [`ReturnSummary`] values, populated programmatically before analysis.

#![allow(dead_code)]

use crate::common::adapter::ReturnSummary;
use crate::common::formula::Formula;
use std::collections::BTreeMap;

/// Identifies a specific loop instance within a function, used when querying
/// for loop invariant candidates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopContext {
    /// The name of the function that contains the loop.
    pub function: String,
    /// A stable numeric identifier for the loop within that function (assigned
    /// by the loop-detection pass).
    pub loop_id: usize,
}

/// Seam through which external or manually constructed summaries are supplied
/// to the analysis driver.
///
/// Implementors may return pre-computed [`ReturnSummary`] values for callees
/// the analysis cannot or should not re-analyse (e.g. external library
/// functions), and/or loop invariant candidates to seed invariant synthesis.
///
/// The default implementations return no information, so partial
/// implementations need only override the methods they care about.
pub trait CandidateProvider {
    /// Returns a pre-computed return summary for `callee`, if available.
    ///
    /// Returning `Some(summary)` causes the driver to skip automatic analysis
    /// of that callee and use the provided summary directly.  Returning `None`
    /// leaves the decision to the driver.
    fn function_summary(&self, _callee: &str) -> Option<ReturnSummary> {
        None
    }

    /// Returns a list of loop invariant candidate formulas for the loop
    /// identified by `ctx`.
    ///
    /// An empty list signals that the provider has no suggestions; the driver
    /// will fall back to its own invariant synthesis strategy.
    fn loop_invariant(&self, _ctx: &LoopContext) -> Vec<Formula> {
        Vec::new()
    }
}

/// A no-op provider that never supplies any summary or invariant candidate.
///
/// Use this as the default when no external summaries are needed.
#[derive(Clone, Debug, Default)]
pub struct NoProvider;

impl CandidateProvider for NoProvider {}

/// A provider backed by a map of manually registered [`ReturnSummary`] values.
///
/// Build one with [`new`] / [`with_function_summary`] (builder style) or
/// [`add_function_summary`] (mutation style), then pass it to the driver.
///
/// [`new`]: ManualProvider::new
/// [`with_function_summary`]: ManualProvider::with_function_summary
/// [`add_function_summary`]: ManualProvider::add_function_summary
#[derive(Clone, Debug, Default)]
pub struct ManualProvider {
    function_summaries: BTreeMap<String, ReturnSummary>,
}

impl ManualProvider {
    /// Creates an empty provider.
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers `summary` and returns `self`, enabling builder-style
    /// construction.  If a summary for the same function was already
    /// registered, it is overwritten.
    pub fn with_function_summary(mut self, summary: ReturnSummary) -> Self {
        self.add_function_summary(summary);
        self
    }

    /// Registers `summary`, overwriting any previous entry for the same
    /// function name.
    pub fn add_function_summary(&mut self, summary: ReturnSummary) {
        self.function_summaries
            .insert(summary.function.clone(), summary);
    }

    /// Returns the full map of registered summaries, keyed by function name.
    pub fn function_summaries(&self) -> &BTreeMap<String, ReturnSummary> {
        &self.function_summaries
    }
}

impl CandidateProvider for ManualProvider {
    /// Returns the pre-registered summary for `callee`, or `None` if no
    /// summary was registered for that name.
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
