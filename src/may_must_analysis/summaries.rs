//! Interprocedural summary tables for the bidirectional may / not-may analysis.
//!
//! # Naming and SMASH paper alignment (v0.15.0+)
//!
//! Both summary kinds in this module are **over-approximations**.  Per the
//! *Compositional May-Must Program Analysis* paper, over-approximations are
//! the **MAY family**:
//!
//! - [`NotMaySummary`] — captures a proven *safety* result over an
//!   over-approximate violation precondition.  Used to discharge backward
//!   not-may propagation at a callee call site.
//! - [`MaySummary`] (formerly `MustSummary`) — captures a *forward reach*
//!   result derived from SP propagation.  The callee, starting with caller
//!   states satisfying `precondition`, *may* leave the caller's `reach`
//!   component containing the cells described by `postcondition`.
//!
//! The historical name `MustSummary` was misleading — the post-state widening
//! it performs (`join_reach`, a disjunction) is over-approximate, not
//! under-approximate.  A true MUST summary (concrete bug witness) lives in
//! [`crate::may_must_analysis::smash::MustPathSummary`].
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

/// A *forward MAY* summary — an over-approximation of the callee's forward
/// reach contribution at the return site.
///
/// Despite its historical name (`MustSummary`), the consumer
/// ([`crate::may_must_analysis::rules::RuleEngine::forward_may_usesummary`])
/// performs a `join_reach` (a disjunction), which widens the caller's
/// `reach` — over-approximation, not under-approximation.  In SMASH-paper
/// terminology this is a **MAY** summary, not a MUST summary.
///
/// Semantics: if `precondition` holds at the call site, then it is *possible*
/// for `postcondition` to hold at the return site — i.e. `postcondition` is a
/// constraint we may safely add to the caller's `reach` after the call.
///
/// Both fields are formulas over the symbolic call-site / return-site state.
///
/// True under-approximate MUST summaries (concrete bug witnesses) are
/// represented separately by [`crate::may_must_analysis::smash::MustPathSummary`].
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MaySummary {
    /// The call-site condition under which this reach contribution is added.
    pub precondition: Formula,
    /// The reach-side constraint that may be conjoined into the caller's
    /// `reach` at the return site.
    pub postcondition: Formula,
}

/// Deprecated alias retained so external callers do not break during the
/// rename.  Prefer [`MaySummary`].
#[deprecated(
    note = "use MaySummary; this name was misleading (it's over-approximate, hence MAY in the SMASH paper sense, not MUST)"
)]
pub type MustSummary = MaySummary;

/// Global summary store shared across all procedures in a module.
///
/// Populated by the driver ([`driver.rs`]) as callees are analysed before
/// their callers.  All three tables grow monotonically; entries are never
/// removed.
///
/// [`driver.rs`]: crate::may_must_analysis::driver
#[derive(Clone, Debug, Default)]
pub struct SummaryTables {
    /// Not-may (safety) summaries, keyed by procedure name.  Used to discharge
    /// backward not-may propagation at callee call sites.
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    /// Forward-may (reach) summaries, keyed by procedure name.  Used to widen
    /// the caller's `reach` over-approximation at the return site of a call.
    /// Renamed from `must` in v0.15.0 to align with SMASH-paper semantics —
    /// these are over-approximations, hence MAY, not MUST.
    pub forward_may: BTreeMap<ProcedureName, Vec<MaySummary>>,
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

    /// Ensures a forward-may entry exists for `name`, initialising it to an
    /// empty list if absent.
    pub fn init_forward_may(&mut self, name: impl Into<String>) {
        self.forward_may.entry(name.into()).or_default();
    }

    /// Returns all not-may summaries for `name`, or an empty slice if none
    /// exist.
    pub fn notmay(&self, name: &str) -> &[NotMaySummary] {
        self.notmay.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Returns all forward-may summaries for `name`, or an empty slice if none
    /// exist.
    pub fn forward_may(&self, name: &str) -> &[MaySummary] {
        self.forward_may
            .get(name)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
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

    /// Inserts a forward-may summary for `name`.
    ///
    /// Returns `true` if the summary was new, `false` if an identical summary
    /// was already present (deduplication by structural equality).
    pub fn add_forward_may(&mut self, name: impl Into<String>, summary: MaySummary) -> bool {
        let entries = self.forward_may.entry(name.into()).or_default();
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
            .chain(self.forward_may.keys())
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
    fn forward_may_deduplicates() {
        let mut tables = SummaryTables::new();
        let summary = MaySummary {
            precondition: Formula::True,
            postcondition: Formula::False,
        };
        assert!(tables.add_forward_may("f", summary.clone()));
        assert!(!tables.add_forward_may("f", summary));
    }

    #[test]
    fn missing_tables_return_empty_slices() {
        let tables = SummaryTables::new();
        assert!(tables.notmay("missing").is_empty());
        assert!(tables.forward_may("missing").is_empty());
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
