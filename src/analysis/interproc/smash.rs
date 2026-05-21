//! SMASH-style bidirectional may/must orchestrator.
//!
//! For each assertion, runs the **may** direction
//! ([`analyze_with_tables`] — combined `reach ∧ state` backward check) and,
//! when that returns `Unknown`, the **forward MUST** direction
//! ([`dart_explore`] — depth-first concrete path enumeration).
//!
//! This module is the *top layer* over the existing passes — it does not
//! re-implement may/must; it composes them.  See
//! paper concepts and our types.
//!
//! # Key types
//!
//! - [`SmashSummaryDB`] — carries the [`SummaryTables`] consumed by both
//! - [`SmashRunResult`] — pairs the final [`AssertionResult`] with a
//!   [`VerdictEngine`] label identifying which direction produced it.

use std::collections::HashMap;

use crate::analysis::backward::node_summary::NodeSummary;
use crate::analysis::backward::rules::Judgement;
use crate::analysis::backward::{
    analyze_with_tables, AssertionResult, BackwardError, InvariantConfig,
};
use crate::analysis::dart::{dart_explore, DartConfig};
use crate::analysis::interproc::summaries::SummaryTables;
use crate::cfg::adapter::AssertionSite;
use crate::cfg::AbstractCfg;
use crate::formula::Formula;
use crate::smt::oracle::Oracle;

/// Shared summary database for one orchestrator run.
pub struct SmashSummaryDB {
    pub tables: SummaryTables,
}

/// Output of one orchestrator run for a single assertion.
#[derive(Clone, Debug)]
pub struct SmashRunResult {
    pub assertion: AssertionResult,
    pub engine: VerdictEngine,
}

/// Which engine produced the final verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerdictEngine {
    MayInvariantAnalysis,
    MustDart,
    Inconclusive,
}

/// Run the bidirectional SMASH orchestrator for one assertion.
///
/// 1. **May direction** (`analyze_with_tables`): if Verified or BugFound, return immediately.
/// 2. **Forward MUST direction** (DART path enumeration): if `bmc_bound > 0`, enumerate
///    concrete paths up to `bmc_bound` loop re-visits and return BugFound on first SAT model.
/// 3. Return the may direction's Unknown verdict if both directions are inconclusive.
pub fn run_smash(
    cfg: &AbstractCfg,
    procedure_name: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    db: &SmashSummaryDB,
    config: Option<&InvariantConfig>,
    debug_names: &HashMap<String, String>,
) -> SmashRunResult {
    let may_result = analyze_with_tables(
        cfg,
        procedure_name,
        site,
        oracle,
        &db.tables,
        config,
        debug_names,
    );

    let may_unknown_or_error = match may_result {
        Ok(result) => {
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
                };
            }
            Some(result)
        }
        Err(BackwardError::CyclicCfgUnsupported) => None,
        Err(other) => {
            log::warn!(
                target: "engine_verdict",
                "function {procedure_name} assertion #{} ({}): error {other:?} — returning Unknown",
                site.id, site.location
            );
            return SmashRunResult {
                assertion: empty_unknown_result(site, debug_names),
                engine: VerdictEngine::Inconclusive,
            };
        }
    };

    // Forward MUST via DART: depth-first concrete path enumeration.
    let dart_config = DartConfig::default();
    if let Some(dart_result) = dart_explore(cfg, site, oracle, dart_config, debug_names) {
        log::info!(
            target: "engine_verdict",
            "function {procedure_name} assertion #{} ({}): {:?} [engine=forward-must/dart]",
            site.id, site.location, dart_result.judgement
        );
        return SmashRunResult {
            assertion: dart_result,
            engine: VerdictEngine::MustDart,
        };
    }
    log::info!(
        target: "engine_verdict",
        "function {procedure_name} assertion #{} ({}): Unknown [engine=forward-must/dart exhausted]",
        site.id, site.location
    );

    let assertion = may_unknown_or_error.unwrap_or_else(|| empty_unknown_result(site, debug_names));
    SmashRunResult {
        assertion,
        engine: VerdictEngine::Inconclusive,
    }
}

fn empty_unknown_result(
    site: &AssertionSite,
    debug_names: &HashMap<String, String>,
) -> AssertionResult {
    let empty = NodeSummary {
        node: site.node,
        reach: Formula::True,
        state: Formula::True,
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
