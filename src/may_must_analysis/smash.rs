//! SMASH-style bidirectional may/must orchestrator.
//!
//! Adapts the original *Compositional May-Must Analysis* (SMASH) paper:
//! for each assertion, run the **may** direction (proves safety via
//! [`analyze_with_tables`]'s combined `reach ∧ state` check) and the **must**
//! direction (finds bugs via [`bmc::bmc_check`]'s bounded unrolling) as
//! cooperating peers, sharing a [`SmashSummaryDB`].
//!
//! This module is the *top layer* over the existing passes — it does not
//! re-implement may/must, it composes them.  See the SMASH section at the top
//! of `TODO.md` for the design rationale.
//!
//! # Current scope (v0.14.0)
//!
//! - Orchestrator runs may → must in sequence per assertion.
//! - BMC's BugFound results are recorded as [`MustPathSummary`] entries in
//!   the DB (consumed by the next step in this milestone).
//! - Engine attribution: every verdict is labelled with the engine that
//!   produced it via the `engine_verdict` log target.
//!
//! # Deferred (next steps)
//!
//! - ACHAR consults [`MustPathSummary`] entries to prune candidates that any
//!   known must-path violates.
//! - Inter-procedural cross-feed: callee must-paths surface as caller-visible
//!   bug witnesses.
//! - Iterating may/must to fixpoint over DB updates within a single procedure
//!   (today the orchestrator runs each direction once).

use std::collections::{BTreeMap, HashMap};

use crate::common::abstract_cfg::AbstractCfg;
use crate::common::adapter::AssertionSite;
use crate::common::formula::Formula;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::{
    analyze_with_tables, AssertionResult, BackwardError, InvariantConfig,
};
use crate::may_must_analysis::bmc;
use crate::may_must_analysis::loops::VerifiedLoopInvariant;
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::rules::Judgement;
use crate::may_must_analysis::summaries::{ProcedureName, SummaryTables};

/// A concrete bug-witness path discovered by the **must** direction.
///
/// Produced by [`bmc::bmc_check`] when it finds a BugFound at some unrolling
/// depth.  The fields describe the concrete pre-state at the procedure entry
/// and post-state at the assertion site, both extracted from the SMT model.
///
/// Future consumers (cross-procedure propagation, ACHAR pruning) read these
/// entries from the [`SmashSummaryDB`].
#[derive(Clone, Debug)]
pub struct MustPathSummary {
    /// Procedure where the must-path was found.
    pub procedure: ProcedureName,
    /// Assertion site this path reaches.
    pub site_id: usize,
    /// Concrete pre-state at procedure entry (from the SMT model of the
    /// satisfiable `reach ∧ state` formula on the unrolled CFG).
    pub entry_state: Formula,
    /// BMC bound that exposed this must-path.
    pub bmc_bound: usize,
}

/// Shared summary database for the SMASH orchestrator.
///
/// Extends the may-side [`SummaryTables`] (invariants + not-may/must summaries)
/// with the must-side [`MustPathSummary`] entries.  The orchestrator reads
/// invariant entries from `tables` and writes must-path entries to
/// `must_paths` when BMC finds a bug.
#[derive(Clone, Debug, Default)]
pub struct SmashSummaryDB {
    /// May-side summaries (existing structure).  Re-used as-is so this layer
    /// is purely additive.
    pub tables: SummaryTables,
    /// Must-side bug witnesses, keyed by procedure name.
    pub must_paths: BTreeMap<ProcedureName, Vec<MustPathSummary>>,
}

impl SmashSummaryDB {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the must-paths recorded for `procedure`, or an empty slice.
    pub fn must_paths(&self, procedure: &str) -> &[MustPathSummary] {
        self.must_paths
            .get(procedure)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Inserts a must-path summary.  Deduplicates by structural equality of
    /// `(site_id, entry_state, bmc_bound)`.  Returns `true` if newly added.
    pub fn add_must_path(&mut self, summary: MustPathSummary) -> bool {
        let entries = self
            .must_paths
            .entry(summary.procedure.clone())
            .or_default();
        let dup = entries.iter().any(|e| {
            e.site_id == summary.site_id
                && e.bmc_bound == summary.bmc_bound
                && format!("{:?}", e.entry_state) == format!("{:?}", summary.entry_state)
        });
        if dup {
            false
        } else {
            entries.push(summary);
            true
        }
    }
}

/// Output of one orchestrator run for a single assertion.
///
/// Returned by [`run_smash`] so the caller can merge any newly discovered
/// must-paths into the shared DB after a parallel batch completes.  Bundling
/// them this way keeps the per-assertion call cleanly read-only on `tables`
/// and the DB, which lets the driver `par_iter` over assertions without
/// locking.
#[derive(Clone, Debug)]
pub struct SmashRunResult {
    /// Final assertion verdict.  Always populated — never an Err.
    pub assertion: AssertionResult,
    /// Engine that produced the verdict, for telemetry / debugging.
    pub engine: VerdictEngine,
    /// Must-paths newly discovered by this run, to be merged into the DB.
    pub new_must_paths: Vec<MustPathSummary>,
}

/// Which engine produced the final verdict for an assertion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerdictEngine {
    /// Verdict came from the may direction (combined `reach ∧ state` check).
    MayInvariantAnalysis,
    /// Verdict came from the must direction (BMC at a specific bound).
    MustBmc { bound: usize },
    /// Both engines failed to produce a decisive verdict; final = Unknown.
    Inconclusive,
}

impl VerdictEngine {
    pub fn label(self) -> String {
        match self {
            VerdictEngine::MayInvariantAnalysis => "may/invariant-analysis".into(),
            VerdictEngine::MustBmc { bound } => format!("must/bmc bound={bound}"),
            VerdictEngine::Inconclusive => "inconclusive".into(),
        }
    }
}

/// Run the SMASH orchestrator for one assertion.
///
/// Sequence (current iteration of the design):
///
/// 1. **May direction** — call [`analyze_with_tables`].
///    - If `Verified` → return `Verified` immediately.
///    - If `BugFound` → return `BugFound` immediately (the may path can find
///      bugs in acyclic functions through `reach ∧ state` already being SAT
///      at entry; no need to call BMC).
///    - If `Unknown` or `CyclicCfgUnsupported` → fall through to must.
///
/// 2. **Must direction** — if `config.bmc_bound = Some(k)`, call
///    [`bmc::bmc_check`] up to bound `k`.
///    - If BMC finds a bug → return `BugFound`, record a `MustPathSummary`
///      for cross-procedure use.
///    - If BMC exhausts → return the may direction's `Unknown` verdict.
///
/// The orchestrator always returns a valid [`AssertionResult`], never an
/// `Err`.  The current may/BMC fallback in `driver.rs` is structurally
/// equivalent; this function exists so future enhancements (ACHAR pruning
/// via must-paths, cross-procedure propagation, fixpoint iteration over the
/// DB) compose without changing the driver's call site.
#[allow(clippy::too_many_arguments)]
pub fn run_smash(
    cfg: &AbstractCfg,
    procedure_name: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    db: &SmashSummaryDB,
    config: Option<&InvariantConfig>,
    verified_invariants: Option<&[VerifiedLoopInvariant]>,
    debug_names: &HashMap<String, String>,
) -> SmashRunResult {
    // ── May direction ────────────────────────────────────────────────────
    let may_result = analyze_with_tables(
        cfg,
        procedure_name,
        site,
        oracle,
        &db.tables,
        config,
        verified_invariants,
        debug_names,
    );

    let may_unknown_or_error = match may_result {
        Ok(result) => {
            // Verified or BugFound from may → decisive, return.  Unknown
            // from may → fall through to must.
            if matches!(
                result.judgement,
                Judgement::Verified | Judgement::BugFound { .. }
            ) {
                log::info!(
                    target: "engine_verdict",
                    "function {procedure_name} assertion #{} ({}): {:?} [engine=may/invariant-analysis]",
                    site.id, site.location, result.judgement
                );
                return SmashRunResult {
                    assertion: result,
                    engine: VerdictEngine::MayInvariantAnalysis,
                    new_must_paths: Vec::new(),
                };
            }
            Some(result)
        }
        Err(BackwardError::CyclicCfgUnsupported) => None,
        Err(other) => {
            // Genuine analysis error (Rule/Oracle).  Return Unknown without
            // attempting BMC — these errors indicate the inputs are
            // malformed, not that BMC could rescue us.
            log::warn!(
                target: "engine_verdict",
                "function {procedure_name} assertion #{} ({}): error {other:?} \
                 — returning Unknown without BMC attempt",
                site.id, site.location
            );
            return SmashRunResult {
                assertion: empty_unknown_result(site, debug_names),
                engine: VerdictEngine::Inconclusive,
                new_must_paths: Vec::new(),
            };
        }
    };

    // ── Must direction ───────────────────────────────────────────────────
    let bmc_bound = config.and_then(|c| c.bmc_bound);
    if let Some(bound) = bmc_bound {
        if let Some(bmc_result) = bmc::bmc_check(cfg, site, oracle, bound) {
            // BMC found a concrete bug.  Record a must-path summary so that
            // future steps (cross-procedure propagation, ACHAR pruning) can
            // consume it.
            let entry_state = match &bmc_result.judgement {
                Judgement::BugFound { .. } => bmc_result.entry_summary.state.clone(),
                _ => Formula::True,
            };
            let must_path = MustPathSummary {
                procedure: procedure_name.to_string(),
                site_id: site.id,
                entry_state,
                bmc_bound: bound,
            };
            log::info!(
                target: "engine_verdict",
                "function {procedure_name} assertion #{} ({}): {:?} [engine=must/bmc bound={bound}]",
                site.id, site.location, bmc_result.judgement
            );
            return SmashRunResult {
                assertion: bmc_result,
                engine: VerdictEngine::MustBmc { bound },
                new_must_paths: vec![must_path],
            };
        }
        log::info!(
            target: "engine_verdict",
            "function {procedure_name} assertion #{} ({}): Unknown [engine=must/bmc bound={bound} exhausted]",
            site.id, site.location
        );
    }

    // ── Final: may's Unknown (or an empty Unknown if may also errored) ──
    let assertion = may_unknown_or_error.unwrap_or_else(|| empty_unknown_result(site, debug_names));
    SmashRunResult {
        assertion,
        engine: VerdictEngine::Inconclusive,
        new_must_paths: Vec::new(),
    }
}

/// Builds a placeholder [`AssertionResult`] with `Judgement::Unknown` when
/// neither engine produced a usable result.  Used to keep the orchestrator's
/// return type uniform (never `Err`).
fn empty_unknown_result(
    site: &AssertionSite,
    debug_names: &HashMap<String, String>,
) -> AssertionResult {
    let empty = NodeSummary {
        node: site.node,
        reach: Formula::True,
        state: Formula::True,
        must_reach: Formula::False,
    };
    AssertionResult {
        site_id: site.id,
        site_label: site.location.clone(),
        source_location: site.source_location.clone().into(),
        judgement: Judgement::Unknown,
        entry_summary: empty.clone(),
        assertion_summary: empty,
        debug_names: debug_names.clone(),
    }
}
