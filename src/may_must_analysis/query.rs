//! Query types for the demand-driven SMASH refactor.
//!
//! Per `design_notes/QUERY_REFACTOR.md`, the unit of work is no longer an
//! `AssertionSite` analysed in isolation, but a Hoare-style query
//! `⟨pre ⇒ proc post⟩`.  Top-level assertions become initial queries with
//! `post = ¬obligation`; call sites generate sub-queries with caller-derived
//! pre and post.  Multiple contextual summaries per procedure are produced
//! from completed query results and reused via subsumption.
//!
//! This module defines the data shapes — no scheduler logic yet (that lives
//! in `scheduler.rs`).  Subsumption helpers operate purely on formulas via
//! the [`Oracle`], so they are unit-testable without any CFG.
//!
//! # Subsumption asymmetry (must read)
//!
//! The direction of implications differs between NotMay and Must:
//!
//! - **NotMaySummary covers query** iff `q.pre ⇒ s.pre  ∧  q.post ⇒ s.post`.
//!   The summary proves "from `s.pre`, `s.post` is unreachable"; the query
//!   asks "from `q.pre`, can `q.post` reach?".  If `q.pre` is in `s.pre`'s
//!   range and `q.post` is in `s.post`'s range, the answer is no.
//!
//! - **MustSummary covers query** iff `s.pre ⇒ q.pre  ∧  s.post ⇒ q.post`.
//!   The summary witnesses "from `s.pre` we can reach `s.post`"; if the
//!   summary's pre is contained in the query's pre, and the summary's post
//!   is contained in the query's post, the same witness applies.

#![allow(dead_code)]

use crate::common::formula::{Formula, SmtModel};
use crate::common::oracle::{Oracle, OracleError, Validity};
use crate::may_must_analysis::summaries::{MaySummary, NotMaySummary, ProcedureName};
use std::collections::BTreeMap;

/// A demand-driven query asking one Hoare-style question of one procedure.
///
/// Semantics: "Assuming `pre` holds at the entry of `procedure`, is some
/// state in `post` reachable at its exit (or violation site)?"
///
/// Both analysis directions (backward NOT-MAY, forward MUST) race to
/// discharge a single query.  The first decisive result wins; the other
/// direction may still contribute to summaries.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Query {
    /// Procedure being analysed.
    pub procedure: ProcedureName,
    /// Caller-derived precondition at the procedure entry, expressed over
    /// procedure-interface variables (formals, externally-visible regions,
    /// globals).
    pub pre: Formula,
    /// Caller-derived "bad" postcondition.  For top-level assertion
    /// queries this is `¬obligation`.  For call-site queries it is the
    /// caller's projected post-state.
    pub post: Formula,
}

impl Query {
    pub fn new(procedure: impl Into<ProcedureName>, pre: Formula, post: Formula) -> Self {
        Self {
            procedure: procedure.into(),
            pre,
            post,
        }
    }
}

/// Stable identifier for a query within a single `Scheduler` run.
///
/// Assigned at enqueue time.  Two queries that are textually identical but
/// enqueued separately receive different ids; the scheduler's subsumption
/// check decides whether to share a result.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct QueryId(pub usize);

/// The decisive result a query produces, plus the summary it contributes
/// to the contextual table.
#[derive(Clone, Debug)]
pub enum QueryResult {
    /// `post` is provably NOT reachable from `pre` in this procedure.
    NotReachable { summary: NotMaySummary },

    /// A concrete execution from a state satisfying `pre` reaches a state
    /// satisfying `post`.  Sound only when produced by the forward-MUST
    /// direction (backward-on-acyclic, native or BMC-unrolled).
    Reachable {
        /// Projected MUST summary (concrete witness in procedure-interface
        /// variables).  Distinct from `MaySummary` — see the type
        /// documentation in `summaries.rs`.
        summary: ContextualMustSummary,
        witness: Option<SmtModel>,
    },

    /// Neither direction reached a decisive verdict.
    Unknown,
}

/// True under-approximate MUST summary derived from a forward-MUST query
/// result.  Distinct from `MaySummary` (which is over-approximate and
/// historically misnamed `MustSummary`).  See
/// `design_notes/QUERY_REFACTOR.md` §3 for the rationale.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ContextualMustSummary {
    /// Concrete pre-state from which the witness was derived, projected
    /// to procedure-interface variables.
    pub precondition: Formula,
    /// Concrete post-state the witness reaches, also projected.
    pub postcondition: Formula,
}

/// An in-progress query and its dependents.
///
/// Recursion is detected via subsumption against active queries: if a new
/// query is subsumed by an in-progress one, we register a dependency
/// rather than re-entering the same analysis.
#[derive(Clone, Debug)]
pub struct InProgressQuery {
    pub id: QueryId,
    pub query: Query,
    /// Queries currently blocked on this one finishing.
    pub dependents: Vec<QueryId>,
    pub placeholder: PlaceholderKind,
}

/// What an in-progress query contributes to its own dependents while it
/// has no result yet.
///
/// The choice is direction-specific:
///
/// - `NotMayOptimistic`: assume the query will succeed (call edge is
///   safe).  Sound only if the eventual result is `NotReachable`; if
///   `Reachable` is produced instead, dependents must be re-checked.
///
/// - `MustOptimistic`: assume the query will not produce a witness (no
///   contribution to forward must_reach).  Sound only if the eventual
///   result is `NotReachable` or `Unknown`; a `Reachable` outcome forces
///   re-check of dependents.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PlaceholderKind {
    NotMayOptimistic,
    MustOptimistic,
}

// ── Subsumption ──────────────────────────────────────────────────────────

/// Result of a subsumption check.  Cheaper than a full oracle implication —
/// the helpers below short-circuit on structural equality and on trivial
/// `True` / `False` cases before invoking the SMT solver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Subsumption {
    /// Definitely covers.
    Covers,
    /// Definitely does not cover.
    DoesNotCover,
    /// Oracle returned Unknown; safe default: treat as not covering.
    OracleUnknown,
}

impl Subsumption {
    pub fn is_covering(self) -> bool {
        matches!(self, Subsumption::Covers)
    }
}

/// Does `NotMaySummary { pre_s, post_s }` cover `query`?
///
/// Returns `Covers` iff `q.pre ⇒ pre_s ∧ q.post ⇒ post_s`.  See the
/// module-level documentation for the direction asymmetry.
pub fn notmay_covers(
    summary: &NotMaySummary,
    query: &Query,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    let pre_ok = implies_with_shortcuts(&query.pre, &summary.precondition, oracle)?;
    if !matches!(pre_ok, Subsumption::Covers) {
        return Ok(pre_ok);
    }
    implies_with_shortcuts(&query.post, &summary.postcondition, oracle)
}

/// Does `MustSummary { pre_s, post_s }` cover `query`?
///
/// Returns `Covers` iff `pre_s ⇒ q.pre ∧ post_s ⇒ q.post`.
pub fn must_covers(
    summary: &ContextualMustSummary,
    query: &Query,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    let pre_ok = implies_with_shortcuts(&summary.precondition, &query.pre, oracle)?;
    if !matches!(pre_ok, Subsumption::Covers) {
        return Ok(pre_ok);
    }
    implies_with_shortcuts(&summary.postcondition, &query.post, oracle)
}

/// Implication check with cheap shortcuts before invoking the oracle.
///
/// Order: structural equality, `lhs == False`, `rhs == True`, then SMT.
fn implies_with_shortcuts(
    lhs: &Formula,
    rhs: &Formula,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    if lhs == rhs {
        return Ok(Subsumption::Covers);
    }
    if matches!(lhs, Formula::False) {
        return Ok(Subsumption::Covers); // ex falso quodlibet
    }
    if matches!(rhs, Formula::True) {
        return Ok(Subsumption::Covers); // anything implies True
    }
    match oracle.implies(lhs, rhs)? {
        Validity::Valid => Ok(Subsumption::Covers),
        Validity::Invalid => Ok(Subsumption::DoesNotCover),
        Validity::Unknown => Ok(Subsumption::OracleUnknown),
    }
}

// ── Contextual summary table ────────────────────────────────────────────

/// Per-(procedure, query-post) loop invariant cache key.  See
/// `design_notes/LOOPS.md` §2 for why invariants are keyed by query post.
///
/// `None` indicates a post-independent invariant (produced by the pre-pass
/// before any assertion context is known).
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum QueryPostFingerprint {
    /// Post-independent invariant — applies to every query on this procedure.
    None,
    /// Canonical fingerprint of `Query.post` for cache keying.  The first
    /// cut uses `Debug` formatting; a richer canonicalisation can replace
    /// it later without changing semantics.
    Hash(String),
}

impl QueryPostFingerprint {
    pub fn of_post(post: &Formula) -> Self {
        QueryPostFingerprint::Hash(format!("{post:?}"))
    }
}

/// Contextual summary table: multiple `NotMaySummary` and contextual
/// `MustSummary` entries per procedure, plus loop invariants keyed by
/// `(procedure, fingerprint)`.
///
/// Coexists with the current `SummaryTables` during the refactor.  The
/// existing types (`MaySummary` for forward MAY summaries, `NotMaySummary`)
/// stay as the over-approximate side; the new `ContextualMustSummary` is
/// the under-approximate side.
#[derive(Clone, Debug, Default)]
pub struct ContextualSummaryTable {
    /// Contextual not-may summaries (over-approximate; safety).
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    /// Contextual must summaries (under-approximate; concrete witness).
    pub must: BTreeMap<ProcedureName, Vec<ContextualMustSummary>>,
    /// Over-approximate forward-may summaries (renamed from the old
    /// MustSummary in v0.15.0).  Consumed by `forward_may_usesummary` to
    /// widen `reach` at call sites.
    pub may: BTreeMap<ProcedureName, Vec<MaySummary>>,
    /// Loop invariants keyed by `(procedure, query-post fingerprint)`.
    pub loop_invariants: BTreeMap<
        (ProcedureName, QueryPostFingerprint),
        Vec<(crate::common::abstract_cfg::CfgNodeId, Formula)>,
    >,
}

impl ContextualSummaryTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn notmay(&self, procedure: &str) -> &[NotMaySummary] {
        self.notmay
            .get(procedure)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    pub fn must(&self, procedure: &str) -> &[ContextualMustSummary] {
        self.must
            .get(procedure)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    pub fn may(&self, procedure: &str) -> &[MaySummary] {
        self.may.get(procedure).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Adds a `NotMaySummary` with merge-with-subsumption semantics
    /// (`MERGE_MAY_SUMMARY` from the paper).  Returns `true` if the new
    /// summary was kept; `false` if an existing summary already covered it
    /// (in which case the new one is discarded).
    pub fn merge_notmay(
        &mut self,
        procedure: impl Into<ProcedureName>,
        new_summary: NotMaySummary,
        oracle: &Oracle,
    ) -> Result<bool, OracleError> {
        let name = procedure.into();
        let entries = self.notmay.entry(name).or_default();
        // Is there an existing summary that already covers `new_summary`?
        // i.e. is there `s_old` such that `s_old` covers the query
        // `{pre: new.pre, post: new.post}`?
        let new_as_query = Query {
            procedure: String::new(), // procedure name unused in subsumption
            pre: new_summary.precondition.clone(),
            post: new_summary.postcondition.clone(),
        };
        for existing in entries.iter() {
            if matches!(
                notmay_covers(existing, &new_as_query, oracle)?,
                Subsumption::Covers
            ) {
                return Ok(false);
            }
        }
        // Remove any entries that the new summary subsumes.
        let mut kept = Vec::with_capacity(entries.len() + 1);
        for existing in entries.drain(..) {
            let existing_as_query = Query {
                procedure: String::new(),
                pre: existing.precondition.clone(),
                post: existing.postcondition.clone(),
            };
            if !matches!(
                notmay_covers(&new_summary, &existing_as_query, oracle)?,
                Subsumption::Covers
            ) {
                kept.push(existing);
            }
        }
        kept.push(new_summary);
        *entries = kept;
        Ok(true)
    }

    /// Analogous merge for `ContextualMustSummary` (`MERGE_MUST_SUMMARY`).
    pub fn merge_must(
        &mut self,
        procedure: impl Into<ProcedureName>,
        new_summary: ContextualMustSummary,
        oracle: &Oracle,
    ) -> Result<bool, OracleError> {
        let name = procedure.into();
        let entries = self.must.entry(name).or_default();
        let new_as_query = Query {
            procedure: String::new(),
            pre: new_summary.precondition.clone(),
            post: new_summary.postcondition.clone(),
        };
        for existing in entries.iter() {
            if matches!(
                must_covers(existing, &new_as_query, oracle)?,
                Subsumption::Covers
            ) {
                return Ok(false);
            }
        }
        let mut kept = Vec::with_capacity(entries.len() + 1);
        for existing in entries.drain(..) {
            let existing_as_query = Query {
                procedure: String::new(),
                pre: existing.precondition.clone(),
                post: existing.postcondition.clone(),
            };
            if !matches!(
                must_covers(&new_summary, &existing_as_query, oracle)?,
                Subsumption::Covers
            ) {
                kept.push(existing);
            }
        }
        kept.push(new_summary);
        *entries = kept;
        Ok(true)
    }

    /// Find a `NotMaySummary` covering `query`.  Returns the first match;
    /// callers may want to prefer "tightest" matches but for correctness
    /// any covering summary is sound.
    pub fn lookup_notmay_covering(
        &self,
        query: &Query,
        oracle: &Oracle,
    ) -> Result<Option<&NotMaySummary>, OracleError> {
        for summary in self.notmay(&query.procedure) {
            if matches!(notmay_covers(summary, query, oracle)?, Subsumption::Covers) {
                return Ok(Some(summary));
            }
        }
        Ok(None)
    }

    /// Find a `ContextualMustSummary` covering `query`.
    pub fn lookup_must_covering(
        &self,
        query: &Query,
        oracle: &Oracle,
    ) -> Result<Option<&ContextualMustSummary>, OracleError> {
        for summary in self.must(&query.procedure) {
            if matches!(must_covers(summary, query, oracle)?, Subsumption::Covers) {
                return Ok(Some(summary));
            }
        }
        Ok(None)
    }
}

// ── Unit tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::formula::{Sort, Term, Var};

    fn bool_var(name: &str) -> Formula {
        Formula::Var(Var::new(name, Sort::Bool))
    }

    fn int_le(a: &str, b: i64) -> Formula {
        Formula::le(Term::Var(Var::new(a, Sort::Int)), Term::int(b))
    }

    #[test]
    fn structural_equality_is_covering() {
        let oracle = Oracle::new();
        let f = bool_var("p");
        assert!(matches!(
            implies_with_shortcuts(&f, &f, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn anything_implies_true() {
        let oracle = Oracle::new();
        let f = int_le("x", 5);
        assert!(matches!(
            implies_with_shortcuts(&f, &Formula::True, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn false_implies_anything() {
        let oracle = Oracle::new();
        let f = int_le("x", 5);
        assert!(matches!(
            implies_with_shortcuts(&Formula::False, &f, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn notmay_covers_uses_query_implies_summary() {
        // Summary: from `x <= 10`, post `x <= 20` is unreachable.
        // Query: from `x <= 5`, is `x <= 15` reachable?
        // Subsumption check: x<=5 ⇒ x<=10  AND  x<=15 ⇒ x<=20  → Covers.
        let oracle = Oracle::new();
        let summary = NotMaySummary {
            precondition: int_le("x", 10),
            postcondition: int_le("x", 20),
        };
        let query = Query::new("p", int_le("x", 5), int_le("x", 15));
        assert!(matches!(
            notmay_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn notmay_covers_rejects_when_query_pre_too_weak() {
        // Summary needs x <= 10 at pre; query offers x <= 20 — too weak.
        let oracle = Oracle::new();
        let summary = NotMaySummary {
            precondition: int_le("x", 10),
            postcondition: int_le("x", 20),
        };
        let query = Query::new("p", int_le("x", 20), int_le("x", 15));
        assert!(!matches!(
            notmay_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn must_covers_uses_summary_implies_query() {
        // MustSummary: witness from `x <= 5` reaches `x <= 15`.
        // Query: from `x <= 10`, can `x <= 20` reach?
        // Subsumption: x<=5 ⇒ x<=10  AND  x<=15 ⇒ x<=20  → Covers.
        let oracle = Oracle::new();
        let summary = ContextualMustSummary {
            precondition: int_le("x", 5),
            postcondition: int_le("x", 15),
        };
        let query = Query::new("p", int_le("x", 10), int_le("x", 20));
        assert!(matches!(
            must_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn must_covers_rejects_when_summary_pre_too_loose() {
        // MustSummary witnesses from `x <= 20`; query restricts to `x <= 5`.
        let oracle = Oracle::new();
        let summary = ContextualMustSummary {
            precondition: int_le("x", 20),
            postcondition: int_le("x", 15),
        };
        let query = Query::new("p", int_le("x", 5), int_le("x", 30));
        assert!(!matches!(
            must_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn merge_notmay_discards_subsumed_addition() {
        // A NotMay summary `{pre_s, post_s}` is **stronger / more general**
        // when `pre_s` is weaker (broader pre-range) AND `post_s` is weaker
        // (broader bad-post coverage).  Existing `{x<=10, x<=20}` subsumes
        // a stricter new `{x<=5, x<=15}`:
        //   new.pre  (x<=5)  ⇒ existing.pre  (x<=10)   ✓
        //   new.post (x<=15) ⇒ existing.post (x<=20)   ✓
        // → covered, discard the new one.
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        let kept = tbl
            .merge_notmay(
                "p",
                NotMaySummary {
                    precondition: int_le("x", 5),
                    postcondition: int_le("x", 15),
                },
                &oracle,
            )
            .unwrap();
        assert!(!kept, "subsumed summary should be discarded");
        assert_eq!(tbl.notmay("p").len(), 1);
    }

    #[test]
    fn merge_notmay_removes_subsumed_existing() {
        // Inverse: insert the stricter summary first, then a broader one.
        // The broader subsumes the stricter, so the stricter is removed.
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 5),
                postcondition: int_le("x", 15),
            },
            &oracle,
        )
        .unwrap();
        let kept = tbl
            .merge_notmay(
                "p",
                NotMaySummary {
                    precondition: int_le("x", 10),
                    postcondition: int_le("x", 20),
                },
                &oracle,
            )
            .unwrap();
        assert!(kept, "broader summary should be kept");
        assert_eq!(
            tbl.notmay("p").len(),
            1,
            "broader summary should replace stricter one"
        );
    }

    #[test]
    fn lookup_notmay_finds_covering_summary() {
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        let query = Query::new("p", int_le("x", 5), int_le("x", 15));
        let found = tbl.lookup_notmay_covering(&query, &oracle).unwrap();
        assert!(found.is_some());
    }

    #[test]
    fn lookup_notmay_misses_when_no_summary_covers() {
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        // Query precondition is weaker than summary's — not covered.
        let query = Query::new("p", int_le("x", 100), int_le("x", 15));
        let found = tbl.lookup_notmay_covering(&query, &oracle).unwrap();
        assert!(found.is_none());
    }

    #[test]
    fn query_post_fingerprint_is_stable() {
        let f1 = int_le("x", 10);
        let f2 = int_le("x", 10);
        assert_eq!(
            QueryPostFingerprint::of_post(&f1),
            QueryPostFingerprint::of_post(&f2)
        );
        let f3 = int_le("x", 20);
        assert_ne!(
            QueryPostFingerprint::of_post(&f1),
            QueryPostFingerprint::of_post(&f3)
        );
    }
}
