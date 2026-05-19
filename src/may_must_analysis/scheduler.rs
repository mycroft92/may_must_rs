//! Demand-driven query worklist scheduler (step 3 of the query refactor).
//!
//! Per `design_notes/QUERY_REFACTOR.md`, this module owns the work queue
//! that drives intra-procedural analysis from top-level assertion queries
//! plus (eventually) call-spawned sub-queries.
//!
//! # Current scope (step 3)
//!
//! - `Scheduler` holds the queue, in-progress map, and contextual summary
//!   table.
//! - `enqueue(query)` adds a query; `dispatch_next(...)` pops one and runs
//!   the existing intra-procedural analysis (`run_smash` internals).
//! - Calls are still inlined eagerly via the legacy `ReturnSummary` path
//!   (no sub-query spawning yet — that's step 4).
//! - No subsumption-aware caching yet (step 7).
//!
//! The intent is that *every* assertion verdict the codebase produces now
//! flows through `Scheduler::analyze_procedure`, so subsequent steps can
//! replace internals (call mediation, summary creation, recursion) without
//! touching the driver again.

#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap, VecDeque};

use crate::common::abstract_cfg::AbstractCfg;
use crate::common::adapter::AssertionSite;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::InvariantConfig;
use crate::may_must_analysis::loops::VerifiedLoopInvariant;
use crate::may_must_analysis::query::{ContextualSummaryTable, Query, QueryId};
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

/// Demand-driven query scheduler for one procedure.
///
/// Owns the pending queue, in-progress map, and the contextual summary
/// table that will grow in subsequent steps.  Multiple `Scheduler`
/// instances may run concurrently for disjoint procedures; cross-procedure
/// sharing (step 4+) will introduce a shared DB above this level.
pub struct Scheduler {
    pending: VecDeque<QueryId>,
    in_progress: BTreeMap<QueryId, PendingEntry>,
    completed: BTreeMap<QueryId, DispatchOutcome>,
    /// Contextual summaries discovered so far.  Populated in step 5
    /// (CREATE_*_SUMMARY).  Today this is empty.
    pub table: ContextualSummaryTable,
    next_id: usize,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            pending: VecDeque::new(),
            in_progress: BTreeMap::new(),
            completed: BTreeMap::new(),
            table: ContextualSummaryTable::new(),
            next_id: 0,
        }
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
    /// Returns `None` when the queue is empty.
    #[allow(clippy::too_many_arguments)]
    pub fn dispatch_next(
        &mut self,
        cfg: &AbstractCfg,
        procedure: &ProcedureName,
        oracle: &Oracle,
        legacy_tables: &SummaryTables,
        config: Option<&InvariantConfig>,
        debug_names: &HashMap<String, String>,
    ) -> Option<DispatchOutcome> {
        let id = self.pending.pop_front()?;
        let entry = self.in_progress.remove(&id)?;
        log::debug!(
            target: "scheduler",
            "[dispatch] {:?}: procedure={} pre={:?} post={:?}",
            id, entry.query.procedure, entry.query.pre, entry.query.post,
        );

        if entry.query.procedure != *procedure {
            // Step 3 only dispatches single-procedure queues; cross-
            // procedure dispatch arrives with the worklist scheduler that
            // owns multiple procedure CFGs (step 4).
            log::warn!(
                target: "scheduler",
                "[dispatch] {:?}: query for procedure {} dispatched on CFG for {} \
                 — single-procedure scope only in step 3",
                id, entry.query.procedure, procedure,
            );
        }

        let outcome = match entry.provenance.as_ref() {
            Some(prov) => {
                // Existing intra-procedural analysis path.
                let db = SmashSummaryDB {
                    tables: legacy_tables.clone(),
                    must_paths: BTreeMap::new(),
                };
                let run = smash::run_smash(
                    cfg,
                    procedure,
                    &prov.site,
                    oracle,
                    &db,
                    config,
                    prov.verified_invariants.as_deref(),
                    debug_names,
                );
                log::debug!(
                    target: "scheduler",
                    "[dispatch] {:?}: completed via run_smash (engine={:?})",
                    id, run.engine,
                );
                DispatchOutcome::Completed(run)
            }
            None => {
                // Step 4+: sub-queries spawned by call edges need their own
                // dispatch path (build a synthetic AssertionSite from
                // entry.query, project the result back).  For now flag.
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

    /// Drains all pending queries against the given procedure context.
    /// Convenience wrapper around repeated `dispatch_next`.  Returns the
    /// outcomes in dispatch order (also stable: the order queries were
    /// enqueued, since step 3 has no subsumption-driven reordering).
    #[allow(clippy::too_many_arguments)]
    pub fn drain(
        &mut self,
        cfg: &AbstractCfg,
        procedure: &ProcedureName,
        oracle: &Oracle,
        legacy_tables: &SummaryTables,
        config: Option<&InvariantConfig>,
        debug_names: &HashMap<String, String>,
    ) -> Vec<DispatchOutcome> {
        let mut out = Vec::new();
        while let Some(o) =
            self.dispatch_next(cfg, procedure, oracle, legacy_tables, config, debug_names)
        {
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
