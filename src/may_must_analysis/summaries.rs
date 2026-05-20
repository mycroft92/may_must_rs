//! Summary types for the SMASH-paper interprocedural analysis.
//!
//! After v0.20 (query refactor step 6B) this module no longer owns a
//! `SummaryTables` struct.  The single source of truth is
//! [`crate::may_must_analysis::query::ContextualSummaryTable`], which is
//! re-exported here as `SummaryTables` for any caller still importing the
//! historical name.  The summary record types `NotMaySummary`,
//! `MaySummary`, `MustSummary` (alias for `MaySummary`) remain here.
//!
//! # Naming and SMASH-paper alignment
//!
//! Both `NotMaySummary` and `MaySummary` are over-approximations
//! (SMASH-paper MAY family):
//!
//! - [`NotMaySummary`] — captures a proven *safety* result.
//! - [`MaySummary`] (formerly `MustSummary`) — captures a *forward reach*
//!   result over-approximately.  The historical name `MustSummary` was
//!   misleading; the consumer (`join_reach`, a disjunction) is
//!   over-approximate.
//!
//! True under-approximate MUST summaries (concrete bug witnesses) live in
//! [`crate::may_must_analysis::query::ContextualMustSummary`].

#![allow(dead_code)]

use crate::common::formula::Formula;

/// A procedure name string; used as the key in
/// [`crate::may_must_analysis::query::ContextualSummaryTable`].
pub type ProcedureName = String;

/// A safety summary derived from the backward (not-may) analysis of a callee.
///
/// Semantics: if `precondition` holds at the call site *and* the callee
/// analysis reaches a state consistent with `postcondition`, then no assertion
/// violation can propagate back through this call under those conditions.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct NotMaySummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

/// A *forward MAY* summary — an over-approximation of the callee's forward
/// reach contribution at the return site.  See module docs for why this is
/// MAY, not MUST.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MaySummary {
    pub precondition: Formula,
    pub postcondition: Formula,
}

/// Deprecated alias retained so external callers do not break during the
/// rename.  Prefer [`MaySummary`].
#[deprecated(
    note = "use MaySummary; this name was misleading (it's over-approximate, hence MAY in the SMASH paper sense, not MUST)"
)]
pub type MustSummary = MaySummary;

/// **Re-export of [`crate::may_must_analysis::query::ContextualSummaryTable`].**
///
/// The historical `SummaryTables` struct that lived in this module is
/// gone (deleted in step 6B of the query refactor).  Its replacement is
/// the paper-equivalent `ContextualSummaryTable`, which carries multiple
/// contextual `(pre, post)` entries per procedure with subsumption-aware
/// merging.
pub use crate::may_must_analysis::query::ContextualSummaryTable as SummaryTables;
