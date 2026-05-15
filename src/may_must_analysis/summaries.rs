//! Interprocedural summary tables for the bidirectional may/must analysis.
//!
//! After analysing a callee, its results are distilled into two kinds of
//! summary that can be reused when analysing callers:
//!
//! - [`NotMaySummary`] — captures a proven *safety* result: given that the
//!   callee's precondition holds, the violation postcondition also holds (i.e.
//!   the assertion cannot be violated through this call under those conditions).
//! - [`MustSummary`] — captures a *reachability* result: given that the
//!   callee's precondition holds, the postcondition is guaranteed to hold at
//!   the return site, allowing the forward reach component to grow.
//!
//! [`SummaryTables`] is the central store that maps procedure names to their
//! accumulated summaries.  It is populated incrementally by the driver and
//! consulted by the [`RuleEngine`] during fixpoint iteration.
//!
//! Loop invariants for recursive/looping procedures are also stored here,
//! keyed by function name, so that `analyze_with_tables` can seed the forward
//! reach at loop header nodes without re-running invariant synthesis.
//!
//! [`RuleEngine`]: crate::may_must_analysis::rules::RuleEngine

#![allow(dead_code)]

use crate::common::abstract_cfg::CfgNodeId;
use crate::common::formula::Formula;
use std::collections::BTreeMap;

/// A procedure name string; used as the key in [`SummaryTables`].
pub type ProcedureName = String;

/// A safety summary derived from the backward (not-may) analysis of a callee.
///
/// Semantics: if `precondition` holds at the call site *and* the callee
/// analysis reaches a state consistent with `postcondition`, then no assertion
/// violation can propagate back through this call under those conditions.
///
/// Both fields are formulas over the symbolic call-site state (caller frame).
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct NotMaySummary {
    /// The call-site condition under which this safety result was derived.
    pub precondition: Formula,
    /// The violation postcondition that is proven unreachable when
    /// `precondition` holds.
    pub postcondition: Formula,
}

/// A reachability summary derived from the forward (must) analysis of a callee.
///
/// Semantics: if `precondition` holds at the call site, then `postcondition`
/// is guaranteed to hold at the return site.  This widens the caller's
/// `reach` component across the call boundary.
///
/// Both fields are formulas over the symbolic call-site / return-site state.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MustSummary {
    /// The call-site condition under which this reachability result holds.
    pub precondition: Formula,
    /// The state that is guaranteed to hold at the return site.
    pub postcondition: Formula,
}

/// Global summary store shared across all procedures in a module.
///
/// Populated by the driver ([`driver.rs`]) as callees are analysed before
/// their callers.  All three tables grow monotonically; entries are never
/// removed.
///
/// [`driver.rs`]: crate::may_must_analysis::driver
#[derive(Clone, Debug, Default)]
pub struct SummaryTables {
    /// Not-may (safety) summaries, keyed by procedure name.
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    /// Must (reachability) summaries, keyed by procedure name.
    pub must: BTreeMap<ProcedureName, Vec<MustSummary>>,
    /// Loop invariants, keyed by procedure name.  Each entry is a list of
    /// `(header_node, invariant_formula)` pairs.
    pub loop_invariants: BTreeMap<ProcedureName, Vec<(CfgNodeId, Formula)>>,
}

impl SummaryTables {
    /// Creates an empty summary store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensures a not-may entry exists for `name`, initialising it to an empty
    /// list if absent.  Useful when a procedure has been analysed but produced
    /// no summaries (e.g. all paths were infeasible).
    pub fn init_notmay(&mut self, name: impl Into<String>) {
        self.notmay.entry(name.into()).or_default();
    }

    /// Ensures a must entry exists for `name`, initialising it to an empty
    /// list if absent.
    pub fn init_must(&mut self, name: impl Into<String>) {
        self.must.entry(name.into()).or_default();
    }

    /// Returns all not-may summaries for `name`, or an empty slice if none
    /// exist.
    pub fn notmay(&self, name: &str) -> &[NotMaySummary] {
        self.notmay.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Returns all must summaries for `name`, or an empty slice if none exist.
    pub fn must(&self, name: &str) -> &[MustSummary] {
        self.must.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Inserts a not-may summary for `name`.
    ///
    /// Returns `true` if the summary was new, `false` if an identical summary
    /// was already present (deduplication by structural equality).
    pub fn add_notmay(&mut self, name: impl Into<String>, summary: NotMaySummary) -> bool {
        let entries = self.notmay.entry(name.into()).or_default();
        if entries.contains(&summary) {
            false
        } else {
            entries.push(summary);
            true
        }
    }

    /// Inserts a must summary for `name`.
    ///
    /// Returns `true` if the summary was new, `false` if an identical summary
    /// was already present (deduplication by structural equality).
    pub fn add_must(&mut self, name: impl Into<String>, summary: MustSummary) -> bool {
        let entries = self.must.entry(name.into()).or_default();
        if entries.contains(&summary) {
            false
        } else {
            entries.push(summary);
            true
        }
    }

    /// Replaces the loop invariants for `function` with `invariants`.
    ///
    /// Each element is `(header_node_id, invariant_formula)`.  A subsequent
    /// call for the same function overwrites the previous invariants.
    pub fn set_loop_invariants(
        &mut self,
        function: impl Into<String>,
        invariants: Vec<(CfgNodeId, Formula)>,
    ) {
        self.loop_invariants.insert(function.into(), invariants);
    }

    /// Returns the loop invariants stored for `function`, or an empty slice if
    /// none have been set.
    pub fn get_loop_invariants(&self, function: &str) -> &[(CfgNodeId, Formula)] {
        self.loop_invariants
            .get(function)
            .map(|items| items.as_slice())
            .unwrap_or(&[])
    }

    /// Returns a sorted, deduplicated list of all procedure names that appear
    /// in any of the three tables.
    pub fn all_procedure_names(&self) -> Vec<String> {
        let mut names = self
            .notmay
            .keys()
            .chain(self.must.keys())
            .chain(self.loop_invariants.keys())
            .cloned()
            .collect::<Vec<_>>();
        names.sort();
        names.dedup();
        names
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::CfgNodeId;

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

    #[test]
    fn loop_invariants_round_trip() {
        let mut tables = SummaryTables::new();
        tables.set_loop_invariants("loop_fn", vec![(CfgNodeId(3), Formula::bool_var("inv"))]);
        assert_eq!(
            tables.get_loop_invariants("loop_fn"),
            &[(CfgNodeId(3), Formula::bool_var("inv"))]
        );
    }
}
