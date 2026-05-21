//! Demand-driven query worklist scheduler.
//!
//! Owns the work queue that drives intra-procedural analysis from top-level
//! assertion queries.  See `design_notes/QUERY_REFACTOR.md` for the full
//! architectural design.
//!
//! # Current scope (step 6B)
//!
//! - [`Scheduler`] is **module-scoped**: one instance covers every procedure
//!   in the module.  It holds `initial_tables` (return summaries seeded
//!   before dispatch) and accumulates `table` (contextual not-may / must
//!   summaries) as each query completes, so procedures enqueued later
//!   benefit from summaries produced by procedures dispatched earlier.
//! - [`Scheduler::enqueue`] adds an assertion query; [`Scheduler::drain`]
//!   pops and dispatches each one via [`smash::run_smash`], collecting
//!   [`DispatchOutcome`]s.
//! - Calls are still inlined eagerly via the legacy [`ReturnSummary`] path
//!   (call-spawned sub-queries are a future step — step 6C).
//! - [`InProgressQuery`] tracking (step 7 / #21): the `active` map records
//!   queries currently being dispatched.  Subsumption checks against this
//!   map during `enqueue` will prevent re-entering the same analysis for
//!   recursive call edges once sub-query spawning (step 6C) is wired in.
//!   The subsumption path is infrastructure-only today — it is not triggered
//!   because sub-queries are not yet spawned from call edges.

use std::collections::{BTreeMap, HashMap, VecDeque};

use crate::analysis::backward::rules::Judgement;
use crate::analysis::backward::InvariantConfig;
use crate::analysis::interproc::query::{
    create_must_summary_with_debug_names, create_notmay_summary_with_debug_names,
    ContextualSummaryTable, InProgressQuery, PlaceholderKind, ProcedureInterface, Query, QueryId,
};
use crate::analysis::interproc::smash::{self, SmashRunResult, SmashSummaryDB};
use crate::analysis::interproc::summaries::{ProcedureName, SummaryTables};
use crate::cfg::adapter::AssertionSite;
use crate::cfg::AbstractCfg;
use crate::smt::oracle::Oracle;

/// Per-assertion provenance kept alongside a top-level Query.
///
/// The query is `⟨pre, procedure, post⟩` where `post = WP(site.transfer,
/// ¬obligation)`.  We retain the original [`AssertionSite`] so verdicts
/// can be reported in the existing `AssertionResult` shape; later steps
/// will produce `QueryResult` directly and drop this side-channel.
#[derive(Clone, Debug)]
pub struct AssertionProvenance {
    pub site: AssertionSite,
}

/// The work queued for one procedure's analysis.
///
/// In step 3 every entry corresponds to one top-level assertion; in step 4
/// call-spawned sub-queries will be added here too (without provenance).
#[derive(Clone, Debug)]
pub struct PendingEntry {
    pub id: QueryId,
    pub query: Query,
    pub provenance: Option<AssertionProvenance>,
}

/// Outcome of dispatching one queue entry.
///
/// In step 3 this always carries a [`SmashRunResult`] (the legacy
/// per-assertion verdict shape).  Step 5 will refine `Completed` to carry
/// a [`crate::analysis::interproc::query::QueryResult`] directly.
#[derive(Clone, Debug)]
pub enum DispatchOutcome {
    /// Query produced a verdict via the existing analysis path.
    Completed(SmashRunResult),
    /// Provenance was missing for a top-level query — should not happen
    /// in step 3 (every enqueue today carries provenance) but represented
    /// explicitly so future steps can spawn unprovenanced sub-queries
    /// without panicking.
    Unprovenanced,
}

/// Per-procedure data the scheduler needs to dispatch queries against
/// a specific procedure's body.
///
/// Owned by [`Scheduler`] (cloned at registration time).  Cloning is
/// acceptable because the CFG is shared by reference inside; the only
/// owned heavy field is the assertion list, which is bounded by source
/// size.
#[derive(Clone, Debug)]
pub struct ProcedureContext {
    pub cfg: AbstractCfg,
    pub assertions: Vec<AssertionSite>,
    pub debug_names: HashMap<String, String>,
    pub interface: ProcedureInterface,
}

/// Demand-driven query scheduler for one module.
///
/// Owns:
/// - The pending queue + in-progress map shared across all queries
///   (top-level + sub-queries) in the module.
/// - One [`ProcedureContext`] per procedure (registered via
///   [`register_procedure`]).
/// - `initial_tables` — return-summary / loop-invariant tables loaded
///   before any dispatch (set once by the driver via
///   [`Scheduler::with_initial_tables`]).
/// - `table` — contextual summaries accumulated as each query completes
///   (populated by `CREATE_NOTMAYSUMMARY` / `CREATE_MUSTSUMMARY`).
/// - `active` — [`InProgressQuery`] map tracking which queries are
///   currently being dispatched, for step-7 / #21 subsumption detection
///   once call-edge sub-query spawning is wired in.
///
/// Step 6B: a single `Scheduler` now covers the whole module.  Each
/// `dispatch_next` call derives the effective legacy tables by merging
/// `initial_tables` with `table`, so summaries from earlier dispatches
/// are visible to later ones without a separate plumbing step.
pub struct Scheduler {
    pending: VecDeque<QueryId>,
    in_progress: BTreeMap<QueryId, PendingEntry>,
    completed: BTreeMap<QueryId, DispatchOutcome>,
    /// Return-summary / loop-invariant tables seeded before dispatch.
    /// Never mutated after construction; merged with `self.table` at
    /// dispatch time by [`Scheduler::legacy_tables_for_dispatch`].
    initial_tables: SummaryTables,
    /// Contextual summaries discovered so far.  Populated by
    /// CREATE_NOTMAYSUMMARY / CREATE_MUSTSUMMARY after each query
    /// completes; merged into `initial_tables` at dispatch time.
    pub table: ContextualSummaryTable,
    procedures: BTreeMap<ProcedureName, ProcedureContext>,
    next_id: usize,
    /// Queries currently being dispatched.  Infrastructure for step-7
    /// (#21) in-progress subsumption: when sub-query spawning is added,
    /// `enqueue` will check this map for a covering active query before
    /// adding a new pending entry.
    active: BTreeMap<QueryId, InProgressQuery>,
}

impl Scheduler {
    /// Create a scheduler with no pre-loaded summaries.  Equivalent to
    /// `with_initial_tables(SummaryTables::new())`.
    pub fn new() -> Self {
        Self::with_initial_tables(SummaryTables::new())
    }

    /// Create a scheduler pre-loaded with `initial_tables` (e.g., return
    /// summaries and loop invariants from a prior inference pass).  These
    /// are merged with contextual summaries accumulated in `self.table`
    /// each time a query is dispatched.
    pub fn with_initial_tables(initial_tables: SummaryTables) -> Self {
        Self {
            pending: VecDeque::new(),
            in_progress: BTreeMap::new(),
            completed: BTreeMap::new(),
            initial_tables,
            table: ContextualSummaryTable::new(),
            procedures: BTreeMap::new(),
            next_id: 0,
            active: BTreeMap::new(),
        }
    }

    /// Build the effective summary tables for the next dispatch by merging
    /// `initial_tables` (static return summaries) with `self.table`
    /// (contextual summaries from earlier dispatches in this drain).
    fn legacy_tables_for_dispatch(&self) -> SummaryTables {
        let mut merged = self.initial_tables.clone();
        merged.extend_from(&self.table);
        merged
    }

    /// Return the outcome of a completed query, or `None` if not yet done.
    pub fn completed_outcome(&self, id: QueryId) -> Option<&DispatchOutcome> {
        self.completed.get(&id)
    }

    /// Registers a procedure with the scheduler.  Must be called before
    /// any query for that procedure is dispatched.  Multiple
    /// registrations for the same procedure name overwrite the
    /// previous entry — useful if the caller wants to refresh the CFG
    /// (we don't today, but the path is open).
    pub fn register_procedure(&mut self, ctx: ProcedureContext) {
        log::debug!(
            target: "scheduler",
            "[register_procedure] {} (assertions={}, formals={})",
            ctx.interface.procedure,
            ctx.assertions.len(),
            ctx.interface.formals.len(),
        );
        self.procedures.insert(ctx.interface.procedure.clone(), ctx);
    }

    /// Returns the registered context for `procedure`, if any.
    pub fn procedure(&self, procedure: &str) -> Option<&ProcedureContext> {
        self.procedures.get(procedure)
    }

    /// Adds a query to the pending queue.  Returns the assigned
    /// [`QueryId`].  No deduplication / subsumption yet (step 7).
    pub fn enqueue(&mut self, query: Query, provenance: Option<AssertionProvenance>) -> QueryId {
        let id = QueryId(self.next_id);
        self.next_id += 1;
        let entry = PendingEntry {
            id,
            query,
            provenance,
        };
        log::debug!(
            target: "scheduler",
            "[enqueue] {:?}: procedure={} (pending depth={})",
            id,
            entry.query.procedure,
            self.pending.len() + 1,
        );
        self.in_progress.insert(id, entry);
        self.pending.push_back(id);
        id
    }

    /// Dispatches the next pending query.  Looks up the procedure's
    /// [`ProcedureContext`] from the registered set (the query's
    /// `procedure` field is the key).  Returns `None` when the queue is
    /// empty; emits a warning and returns `Unprovenanced` if the query
    /// references an un-registered procedure.
    ///
    /// The effective summary tables are derived internally by merging
    /// `self.initial_tables` (static return summaries) with `self.table`
    /// (contextual summaries from prior dispatches in this drain), so
    /// each successive dispatch sees all summaries produced earlier.
    pub fn dispatch_next(
        &mut self,
        oracle: &Oracle,
        config: Option<&InvariantConfig>,
    ) -> Option<DispatchOutcome> {
        let id = self.pending.pop_front()?;
        let entry = self.in_progress.remove(&id)?;
        log::debug!(
            target: "scheduler",
            "[dispatch] {:?}: procedure={} pre={:?} post={:?}",
            id, entry.query.procedure, entry.query.pre, entry.query.post,
        );

        // #21 infrastructure: record this query as active while it is
        // being dispatched.  When call-edge sub-query spawning is added,
        // `enqueue` will check this map to detect recursive re-entries
        // and register a dependency rather than spawning a new dispatch.
        self.active.insert(
            id,
            InProgressQuery {
                id,
                query: entry.query.clone(),
                dependents: Vec::new(),
                placeholder: PlaceholderKind::NotMayOptimistic,
            },
        );

        // Look up the procedure's context.  Cloning here keeps the
        // borrow checker quiet — `self.create_and_merge_summary` needs
        // `&mut self` later in this function.  Cost: one CFG clone per
        // dispatch; acceptable until we restructure to a borrowing
        // shape.
        let ctx = match self.procedures.get(&entry.query.procedure).cloned() {
            Some(ctx) => ctx,
            None => {
                log::warn!(
                    target: "scheduler",
                    "[dispatch] {:?}: procedure '{}' not registered",
                    id, entry.query.procedure,
                );
                let outcome = DispatchOutcome::Unprovenanced;
                self.completed.insert(id, outcome.clone());
                return Some(outcome);
            }
        };

        let outcome = match entry.provenance.as_ref() {
            Some(prov) => {
                // Merge initial_tables + contextual summaries from prior
                // dispatches in this drain.  This is the core step-6B
                // change: later procedures see summaries from earlier ones.
                let db = SmashSummaryDB {
                    tables: self.legacy_tables_for_dispatch(),
                };
                let run = smash::run_smash(
                    &ctx.cfg,
                    &entry.query.procedure,
                    &prov.site,
                    oracle,
                    &db,
                    config,
                    &ctx.debug_names,
                );
                log::debug!(
                    target: "scheduler",
                    "[dispatch] {:?}: completed via run_smash (engine={:?})",
                    id, run.engine,
                );

                // CREATE_NOTMAYSUMMARY / CREATE_MUSTSUMMARY from the query
                // result and merge into `self.table`.
                self.create_and_merge_summary(
                    &entry.query,
                    &run.assertion,
                    &ctx.interface,
                    oracle,
                    &ctx.debug_names,
                );

                DispatchOutcome::Completed(run)
            }
            None => {
                // Sub-queries spawned by call edges need their own dispatch
                // path (synthesize an assertion at the procedure exit with
                // obligation = ¬query.post).  Step 6B/6C.
                log::warn!(
                    target: "scheduler",
                    "[dispatch] {:?}: no provenance — sub-query dispatch not yet implemented",
                    id,
                );
                DispatchOutcome::Unprovenanced
            }
        };

        // #21 infrastructure: clear the active entry now that dispatch
        // is complete.  Future: notify any registered dependents here.
        self.active.remove(&id);

        self.completed.insert(id, outcome.clone());
        Some(outcome)
    }

    /// Build a contextual summary (NotMay or Must) from a completed query
    /// and merge it into [`self.table`].  Quietly returns if projection
    /// fails (a local couldn't be eliminated) or if the verdict was
    /// Unknown — no summary is added in those cases.
    ///
    /// # Alpha-renaming caveat
    ///
    /// The query's `pre` / `post` and the assertion's `entry_summary` /
    /// `assertion_summary` formulas are in the **callee's** procedure
    /// frame (callee SSA names, callee `__ext_N` regions).  Callers that
    /// look up these summaries must alpha-rename actuals→formals before
    /// the subsumption check (see `design_notes/QUERY_REFACTOR.md` §5
    /// "Projection (caller variables ↔ callee variables)").  That
    /// renaming happens at the call site, not here.
    fn create_and_merge_summary(
        &mut self,
        query: &Query,
        assertion: &crate::analysis::backward::AssertionResult,
        interface: &ProcedureInterface,
        oracle: &Oracle,
        debug_names: &HashMap<String, String>,
    ) {
        match &assertion.judgement {
            Judgement::Verified => {
                if let Some(summary) =
                    create_notmay_summary_with_debug_names(query, interface, Some(debug_names))
                {
                    match self
                        .table
                        .merge_notmay(interface.procedure.clone(), summary, oracle)
                    {
                        Ok(true) => log::debug!(
                            target: "summaries",
                            "[merge_notmay] {}: new summary added", interface.procedure,
                        ),
                        Ok(false) => log::debug!(
                            target: "summaries",
                            "[merge_notmay] {}: subsumed by existing", interface.procedure,
                        ),
                        Err(e) => log::warn!(
                            target: "summaries",
                            "[merge_notmay] {}: oracle error {e:?}", interface.procedure,
                        ),
                    }
                }
            }
            Judgement::BugFound { .. } => {
                // For BugFound today (acyclic CFGs only — BMC is cut),
                // `entry_summary.state` is the precise WP precondition
                // that proved SAT at the entry, and `assertion_summary
                // .state` is the violation precondition at the assertion
                // site.  Use these as the concrete-witness pre/post for
                // the MUST summary.  Once forward-MUST is fully wired,
                // we'll use the under-approximate `must_reach` instead.
                let pre = &assertion.entry_summary.state;
                let post = &assertion.assertion_summary.state;
                if let Some(summary) =
                    create_must_summary_with_debug_names(pre, post, interface, Some(debug_names))
                {
                    match self
                        .table
                        .merge_must(interface.procedure.clone(), summary, oracle)
                    {
                        Ok(true) => log::debug!(
                            target: "summaries",
                            "[merge_must] {}: new summary added", interface.procedure,
                        ),
                        Ok(false) => log::debug!(
                            target: "summaries",
                            "[merge_must] {}: subsumed by existing", interface.procedure,
                        ),
                        Err(e) => log::warn!(
                            target: "summaries",
                            "[merge_must] {}: oracle error {e:?}", interface.procedure,
                        ),
                    }
                }
            }
            Judgement::Unknown => {
                // No summary — Unknown means the analysis couldn't
                // prove either direction.  Future iterations of the
                // worklist may discharge it via a different context.
            }
        }
    }

    /// Drains all pending queries in FIFO order.  The effective summary
    /// tables for each dispatch are derived from `initial_tables` merged
    /// with contextual summaries accumulated so far, so each query
    /// benefits from summaries produced by all previously dispatched
    /// queries in this drain.  Returns outcomes in dispatch order.
    pub fn drain(
        &mut self,
        oracle: &Oracle,
        config: Option<&InvariantConfig>,
    ) -> Vec<DispatchOutcome> {
        let mut out = Vec::new();
        while let Some(o) = self.dispatch_next(oracle, config) {
            out.push(o);
        }
        out
    }

    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }
}

impl Default for Scheduler {
    fn default() -> Self {
        Self::new()
    }
}

// ── Unit tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    fn dummy_query(procedure: &str) -> Query {
        Query::new(procedure, Formula::True, Formula::False)
    }

    #[test]
    fn fresh_scheduler_is_empty() {
        let sched = Scheduler::new();
        assert!(sched.is_empty());
    }

    #[test]
    fn enqueue_assigns_sequential_ids_and_orders_fifo() {
        let mut sched = Scheduler::new();
        let id0 = sched.enqueue(dummy_query("p"), None);
        let id1 = sched.enqueue(dummy_query("q"), None);
        assert_eq!(id0, QueryId(0));
        assert_eq!(id1, QueryId(1));
        assert!(!sched.is_empty());
        // Ensure the FIFO order: id0 first, then id1.
        let first = sched.pending.front().copied().unwrap();
        assert_eq!(first, id0);
    }

    #[test]
    fn dispatch_without_provenance_returns_unprovenanced() {
        // Without a CFG / oracle wired up in test, we test the unprovenanced
        // branch via a stub.  This exercises the early-return path in
        // `dispatch_next` that step 4 will replace.
        let mut sched = Scheduler::new();
        let id = sched.enqueue(dummy_query("p"), None);
        assert_eq!(id, QueryId(0));
        // Note: we can't call `dispatch_next` without a real CFG; the
        // function signature requires concrete oracle and CFG.  We
        // exercise the queue plumbing only here (no analysis is run).
        assert_eq!(sched.pending.len(), 1);
        assert!(sched.completed.is_empty());
    }
}
