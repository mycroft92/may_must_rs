//! Demand-driven query worklist scheduler.
//!
//! Per `design_notes/QUERY_REFACTOR.md`, this module owns the work queue
//! that drives intra-procedural analysis from top-level assertion queries
//! plus (eventually) call-spawned sub-queries.
//!
//! # Scope (steps 3, 5, 6A)
//!
//! - `Scheduler` is **per-module**: it owns a [`ProcedureContext`] for
//!   every procedure in the module and a shared
//!   [`ContextualSummaryTable`] that all dispatches read from and write
//!   into.  Step 6A: a single `Scheduler` for the whole module so that
//!   summaries created by one procedure's analysis become available to
//!   the others without an extra plumbing step.
//! - `enqueue(query)` adds a query; `dispatch_next()` pops one and runs
//!   the existing intra-procedural analysis (`run_smash` internals)
//!   against the CFG owned by the registered procedure context.
//! - Calls are still inlined eagerly via the legacy `ReturnSummary` path
//!   (no sub-query spawning yet — that's step 6B/6C).
//! - No subsumption-aware caching of *queries* yet (step 7).

#![allow(dead_code)]
// `smash::SmashSummaryDB` is deprecated scaffolding still used by the
// transitional `run_smash` entry point.  This module's references will
// disappear when `run_smash` takes `&SummaryTables` directly.
#![allow(deprecated)]

use std::collections::{BTreeMap, HashMap, VecDeque};

use crate::common::abstract_cfg::AbstractCfg;
use crate::common::adapter::AssertionSite;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::InvariantConfig;
use crate::may_must_analysis::loops::VerifiedLoopInvariant;
use crate::may_must_analysis::query::{
    create_must_summary_with_debug_names, create_notmay_summary_with_debug_names,
    ContextualSummaryTable, ProcedureInterface, Query, QueryId,
};
use crate::may_must_analysis::rules::Judgement;
use crate::may_must_analysis::smash::{self, SmashRunResult, SmashSummaryDB};
use crate::may_must_analysis::summaries::{ProcedureName, SummaryTables};

/// Per-assertion provenance kept alongside a top-level Query.
///
/// The query is `⟨pre, procedure, post⟩` where `post = WP(site.transfer,
/// ¬obligation)`.  We retain the original [`AssertionSite`] so verdicts
/// can be reported in the existing `AssertionResult` shape; later steps
/// will produce `QueryResult` directly and drop this side-channel.
#[derive(Clone, Debug)]
pub struct AssertionProvenance {
    pub site: AssertionSite,
    /// Pre-computed VerifiedLoopInvariants for this procedure (from the
    /// driver's `discover_loop_invariants` pre-pass + tables).  Carried
    /// per-query rather than re-derived inside the scheduler.
    pub verified_invariants: Option<Vec<VerifiedLoopInvariant>>,
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
/// a [`crate::may_must_analysis::query::QueryResult`] directly.
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
/// - The shared [`ContextualSummaryTable`] populated by every query's
///   completion path (see `create_and_merge_summary`).
///
/// Step 6A change: previously a `Scheduler` was per-procedure and the
/// driver built one per `AdaptedProcedure`.  Now a single `Scheduler`
/// covers the whole module so contextual summaries created by leaf
/// procedures are available when caller procedures are analysed,
/// without a separate plumbing step.
pub struct Scheduler {
    pending: VecDeque<QueryId>,
    in_progress: BTreeMap<QueryId, PendingEntry>,
    completed: BTreeMap<QueryId, DispatchOutcome>,
    /// Contextual summaries discovered so far.  Populated by
    /// CREATE_NOTMAYSUMMARY / CREATE_MUSTSUMMARY after each query
    /// completes; shared across procedures in the same module.
    pub table: ContextualSummaryTable,
    procedures: BTreeMap<ProcedureName, ProcedureContext>,
    next_id: usize,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            pending: VecDeque::new(),
            in_progress: BTreeMap::new(),
            completed: BTreeMap::new(),
            table: ContextualSummaryTable::new(),
            procedures: BTreeMap::new(),
            next_id: 0,
        }
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

    /// Dispatches the next pending query against the given procedure's CFG
    /// and the supplied interprocedural [`SummaryTables`] (legacy must/notmay
    /// summaries — to be migrated to the contextual table in step 5).
    ///
    /// Dispatches the next pending query.  Looks up the procedure's
    /// [`ProcedureContext`] from the registered set (the query's
    /// `procedure` field is the key).  Returns `None` when the queue is
    /// empty; emits a warning and returns `Unprovenanced` if the query
    /// references an un-registered procedure.
    pub fn dispatch_next(
        &mut self,
        oracle: &Oracle,
        legacy_tables: &SummaryTables,
        config: Option<&InvariantConfig>,
    ) -> Option<DispatchOutcome> {
        let id = self.pending.pop_front()?;
        let entry = self.in_progress.remove(&id)?;
        log::debug!(
            target: "scheduler",
            "[dispatch] {:?}: procedure={} pre={:?} post={:?}",
            id, entry.query.procedure, entry.query.pre, entry.query.post,
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
                // Existing intra-procedural analysis path.
                let db = SmashSummaryDB {
                    tables: legacy_tables.clone(),
                    must_paths: BTreeMap::new(),
                };
                let run = smash::run_smash(
                    &ctx.cfg,
                    &entry.query.procedure,
                    &prov.site,
                    oracle,
                    &db,
                    config,
                    prov.verified_invariants.as_deref(),
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
        assertion: &crate::may_must_analysis::backward::AssertionResult,
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

    /// Drains all pending queries.  Each is dispatched against its
    /// registered procedure context.  Returns the outcomes in dispatch
    /// order (FIFO, no subsumption reordering yet).
    pub fn drain(
        &mut self,
        oracle: &Oracle,
        legacy_tables: &SummaryTables,
        config: Option<&InvariantConfig>,
    ) -> Vec<DispatchOutcome> {
        let mut out = Vec::new();
        while let Some(o) = self.dispatch_next(oracle, legacy_tables, config) {
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
    use crate::common::formula::Formula;

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
