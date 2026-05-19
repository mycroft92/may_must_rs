//! Assertion checker — the top-level entry for the bidirectional may/must analysis.
//!
//! # Algorithm overview
//!
//! Given an [`AbstractCfg`] and an [`AssertionSite`] this module proves (or
//! refutes) that the assertion condition always holds on every reachable
//! execution.  The check is *bidirectional*:
//!
//! * **Forward (reach / must)** — loop invariants are injected into the `reach`
//!   component at loop headers, overapproximating the set of reachable states.
//! * **Backward (state / may)** — the weakest precondition of `NOT obligation`
//!   is propagated backward through `state`, encoding the conditions under which
//!   a violation could occur.
//! * **Combined decision** — at the function entry, if `reach AND state` is
//!   unsatisfiable, no reachable execution can violate the assertion →
//!   [`Judgement::Verified`].  If `reach AND state` is satisfiable, a
//!   concrete counterexample is extracted → [`Judgement::BugFound`].
//!
//! # Acyclic vs. cyclic CFGs
//!
//! For acyclic (loop-free) CFGs [`run_backward`] is called directly.  For
//! cyclic CFGs a set of loop invariants must be obtained first.  The entry
//! point [`analyze_with_tables`] accepts *precomputed* invariants (from a
//! previous interprocedural pass) and falls back to [`synthesize_loop_invariants`]
//! when none are available.  [`discover_loop_invariants`] is a lighter
//! invariant-only path used by the interprocedural driver.
//!
//! # Invariant synthesis pipeline
//!
//! The active generators and their order are controlled by [`SynthesisMode`]:
//!
//! * **Default** (no flag): entry-safety → ACHAR.
//! * **`--inv-observer`**: only the observer-disjunction phase.
//! * **`--inv-grammar`**: only the ACHAR grammar phase.
//!
//! Each candidate is checked with [`check_loop_invariant_verbose`] from [`loops`].

#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId};
use crate::common::adapter::AssertionSite;
use crate::common::formula::{Formula, ModelValue, SmtModel};
use crate::common::oracle::{Oracle, OracleError};
use crate::common::source::SourceLocation;
use crate::may_must_analysis::achar;
use crate::may_must_analysis::loops::{
    check_loop_invariant_verbose, detect_loops, entry_safety_candidates, normalize_candidate,
    observer_disjunction_candidates, sort_innermost_first, InvariantCheckResult,
    VerifiedLoopInvariant,
};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::rules::{Judgement, RuleEngine, RuleError};
use crate::may_must_analysis::summaries::SummaryTables;
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Final outcome of one assertion check together with supporting witness data.
///
/// The `entry_summary` and `assertion_summary` fields capture the [`NodeSummary`]
/// computed at the function entry and at the assertion site respectively, which
/// is useful for diagnostics and for building caller-facing summaries.
///
/// # Fields
///
/// * `site_id` — unique identifier of this assertion.
/// * `site_label` — human-readable description of the assertion location.
/// * `source_location` — file, line, and column information.
/// * `judgement` — the verification result: [`Judgement::Verified`],
///   [`Judgement::BugFound`], or [`Judgement::Unknown`].
/// * `entry_summary` — the combined reach and state at function entry,
///   useful for understanding why Unknown verdicts occur.
/// * `assertion_summary` — the combined reach and state at the assertion site.
#[derive(Clone, Debug)]
pub struct AssertionResult {
    pub site_id: usize,
    pub site_label: String,
    pub source_location: SourceLocation,
    pub judgement: Judgement,
    pub entry_summary: NodeSummary,
    pub assertion_summary: NodeSummary,
    /// Debug name map from the adapted procedure (region/IR-var → source var name).
    pub debug_names: HashMap<String, String>,
}

/// Errors that can occur during the backward (or combined) analysis pass.
///
/// `CyclicCfgUnsupported` is returned when the CFG contains a back edge but no
/// loop invariant candidate was accepted by the three-part check (initiation,
/// inductiveness, exit closure).  Callers should treat this as `UNKNOWN` rather
/// than `Verified`.
///
/// # Variants
///
/// * `CyclicCfgUnsupported` — no accepted loop invariant was found for a cyclic CFG.
/// * `Rule` — a [`RuleError`] occurred during forward reach or backward state propagation.
/// * `Oracle` — an [`OracleError`] occurred during SMT feasibility or validity checking.
#[derive(Debug, thiserror::Error)]
pub enum BackwardError {
    #[error("CFG has a cycle and no loop invariant was accepted")]
    CyclicCfgUnsupported,
    #[error(transparent)]
    Rule(#[from] RuleError),
    #[error(transparent)]
    Oracle(#[from] OracleError),
}

/// Selects which invariant synthesis generators are active.
///
/// - `Default`: full pipeline — entry-safety → ACHAR.
/// - `ObserverOnly`: only the observer-disjunction phase.
/// - `GrammarOnly`: only the ACHAR grammar phase.
///
/// Each exclusive mode is triggered by a dedicated CLI flag (`--inv-observer`,
/// `--inv-grammar`).  When no flag is given, `Default` runs all phases in
/// order, stopping at the first accepted invariant.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum SynthesisMode {
    /// Full pipeline: entry-safety → ACHAR.
    #[default]
    Default,
    /// Only the observer-disjunction phase.
    ObserverOnly,
    /// Only the ACHAR grammar phase.
    GrammarOnly,
}

impl SynthesisMode {
    pub fn name(&self) -> &'static str {
        match self {
            SynthesisMode::Default => "default",
            SynthesisMode::ObserverOnly => "observer-only",
            SynthesisMode::GrammarOnly => "achar-only",
        }
    }
}

/// Runtime configuration for the loop-invariant synthesis pass.
pub struct InvariantConfig {
    /// Which generators are active and in what order.
    pub mode: SynthesisMode,
    /// Skip analysis of functions with more than this many instructions,
    /// returning UNKNOWN immediately. 0 means unlimited.
    pub max_function_size: usize,
    /// Time budget for the ACHAR CEGIS phase per loop. Default: 10 seconds.
    pub achar_timeout: std::time::Duration,
    /// When Some(k), run BMC with bound k as a fallback after invariant
    /// synthesis fails (CyclicCfgUnsupported). BMC can find bugs that require
    /// reasoning through k loop iterations but cannot prove safety.
    pub bmc_bound: Option<usize>,
}

impl Default for InvariantConfig {
    fn default() -> Self {
        Self {
            mode: SynthesisMode::Default,
            max_function_size: 500,
            achar_timeout: std::time::Duration::from_secs(10),
            bmc_bound: None,
        }
    }
}

pub fn analyze(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
) -> Result<AssertionResult, BackwardError> {
    analyze_with_tables(
        cfg,
        "",
        site,
        oracle,
        &SummaryTables::new(),
        None,
        None,
        &HashMap::new(),
    )
}

/// Top-level entry point for checking one assertion inside a (possibly cyclic) CFG.
///
/// # Acyclic path
///
/// When the CFG has a topological order (no back edges) this calls
/// [`run_backward`] directly — no invariant synthesis is required.
///
/// # Cyclic path
///
/// 1. If `precomputed` [`VerifiedLoopInvariant`]s are supplied, they are used
///    directly — they have already passed initiation, inductiveness, and exit
///    closure.  No re-check is performed.
/// 2. Otherwise [`synthesize_loop_invariants`] is called with the active
///    candidate generators (entry-safety, ACHAR), which produces
///    [`VerifiedLoopInvariant`]s that pass all three checks including exit
///    closure.
/// 3. Accepted invariants are injected into `reach` at loop headers before the
///    final [`run_backward`] call.
///
/// # Parameters
///
/// * `tables` — interprocedural must/not-may summaries from a prior pass.
/// * `config` — controls which synthesis generators are enabled.
/// * `precomputed` — already-verified loop invariants produced by
///   [`verify_precomputed`] (from the pre-pass) or by the observer synthesis in
///   `driver.rs`.  Hints (`(CfgNodeId, Formula)` pairs) must be upgraded via
///   [`verify_precomputed`] before being passed here.
pub fn analyze_with_tables(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    tables: &SummaryTables,
    config: Option<&InvariantConfig>,
    precomputed: Option<&[VerifiedLoopInvariant]>,
    debug_names: &HashMap<String, String>,
) -> Result<AssertionResult, BackwardError> {
    if cfg.topological_order().is_some() {
        return run_backward(
            cfg,
            site,
            oracle,
            &BTreeSet::new(),
            &[],
            tables,
            debug_names,
        );
    }

    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();

    // Pre-verified invariants: use directly, no exit closure re-check needed.
    if let Some(invariants) = precomputed {
        if !invariants.is_empty() {
            return run_backward(
                cfg,
                site,
                oracle,
                &excluded,
                invariants,
                tables,
                debug_names,
            );
        }
    }

    // No precomputed invariants: synthesize with full exit closure.
    let assertion_postconditions = compute_preliminary_backward_states(cfg, site, &excluded)?;
    let invariants = synthesize_loop_invariants(
        cfg,
        function,
        &assertion_postconditions,
        oracle,
        config,
        debug_names,
    )?;
    if invariants.is_empty() {
        return Err(BackwardError::CyclicCfgUnsupported);
    }
    run_backward(
        cfg,
        site,
        oracle,
        &excluded,
        &invariants,
        tables,
        debug_names,
    )
}

/// Upgrade InductiveHint invariants to [`VerifiedLoopInvariant`] for a specific assertion.
///
/// Runs the full three-part check (initiation, inductiveness, exit closure) on
/// each hint against the given assertion site.  Returns `Ok(Some(verified))` if
/// all pass, `Ok(None)` if any fail (caller should fall through to synthesis).
///
/// This is the only sound path from InductiveHints to invariants suitable for
/// [`analyze_with_tables`].  Never pass raw hints directly to `run_backward`.
pub fn verify_precomputed(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    hints: &[(CfgNodeId, Formula)],
    oracle: &Oracle,
) -> Result<Option<Vec<VerifiedLoopInvariant>>, BackwardError> {
    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();
    let assertion_postconditions = compute_preliminary_backward_states(cfg, site, &excluded)?;
    precomputed_satisfy_exit_closure(cfg, &assertion_postconditions, hints, oracle)
}

/// Core bidirectional analysis pass.
///
/// Implements the combined may/must check:
///
/// 1. **Forward reach injection** — loop invariants are conjuncted into `reach`
///    at loop headers; back edges are blocked so the engine runs in topological order.
/// 2. **Backward state seeding** — WP of `NOT obligation` is set at the assertion node.
/// 3. **Fixpoint** — [`RuleEngine::run_to_fixpoint`] propagates both directions.
/// 4. **Decision** at the function entry:
///    - `reach AND state` satisfiable → [`Judgement::BugFound`].
///    - `reach AND state` unsatisfiable → [`Judgement::Verified`].
///    - Neither → [`Judgement::Unknown`].
fn run_backward(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    excluded_edges: &BTreeSet<crate::common::abstract_cfg::CfgEdgeId>,
    loop_invariants: &[VerifiedLoopInvariant],
    tables: &SummaryTables,
    debug_names: &HashMap<String, String>,
) -> Result<AssertionResult, BackwardError> {
    let order = cfg
        .topological_order_excluding(excluded_edges)
        .ok_or(BackwardError::CyclicCfgUnsupported)?;

    let mut engine = RuleEngine::new(&cfg);
    engine.init();

    for edge in excluded_edges {
        engine.block_edge(*edge);
    }

    for (header, invariant) in conjunct_loop_invariants(loop_invariants) {
        let summary = engine.summary_mut(header)?;
        summary.reach = if summary.reach == Formula::False {
            invariant
        } else {
            Formula::and(summary.reach.clone(), invariant)
        };
    }

    let neg_obligation = Formula::not(site.obligation.clone());
    let pre_at_assertion = cfg
        .node(site.node)
        .map_err(|_| crate::may_must_analysis::rules::RuleError::UnknownNode { node: site.node })?
        .transfer
        .wp(&neg_obligation);
    engine.set_state(site.node, pre_at_assertion)?;
    engine.run_to_fixpoint(&order, tables, oracle)?;

    let bug = engine.bugfound(cfg.entry(), oracle)?;
    let judgement = if let Some(model) = bug {
        Judgement::BugFound { model }
    } else if engine.verified(cfg.entry(), oracle)? {
        Judgement::Verified
    } else {
        Judgement::Unknown
    };

    Ok(AssertionResult {
        site_id: site.id,
        site_label: site.location.clone(),
        source_location: site.source_location.clone().into(),
        judgement,
        entry_summary: engine.summary(cfg.entry())?.clone(),
        assertion_summary: engine.summary(site.node)?.clone(),
        debug_names: debug_names.clone(),
    })
}

/// Pre-pass that discovers **InductiveHint** invariants before assertion analysis.
///
/// Calls [`synthesize_loop_invariants`] with empty `assertion_postconditions`,
/// so exit closure is not checked — no assertion site is available yet.
/// Returns raw `(CfgNodeId, Formula)` pairs (InductiveHints), NOT
/// [`VerifiedLoopInvariant`]s.
///
/// Callers must upgrade hints to [`VerifiedLoopInvariant`] via
/// [`verify_precomputed`] before passing them to [`analyze_with_tables`].  If
/// exit closure fails for a given assertion site, synthesis is re-run
/// automatically with the real postconditions.
///
/// Returns `None` if synthesis fails for any loop (the function may still be
/// verifiable via per-site synthesis in [`analyze_with_tables`]).
pub fn discover_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    oracle: &Oracle,
    config: Option<&InvariantConfig>,
    debug_names: &HashMap<String, String>,
) -> Option<Vec<(CfgNodeId, Formula)>> {
    synthesize_loop_invariants(cfg, function, &BTreeMap::new(), oracle, config, debug_names)
        .ok()
        .map(|v| v.into_iter().map(|inv| inv.as_pair()).collect())
}

/// Invariant synthesis pipeline for a cyclic CFG.
///
/// Accepts `assertion_postconditions` (WP of `NOT obligation` propagated
/// backward with back edges blocked).
///
/// - When called with `&BTreeMap::new()` (from [`discover_loop_invariants`]):
///   exit closure is skipped and the result is an **InductiveHint** — suitable
///   for interprocedural summary caching but not for direct verdicts.
///
/// - When called with real postconditions (from [`analyze_with_tables`]):
///   all three checks (initiation, inductiveness, exit closure) are required and
///   the result is a **VerifiedLoopInvariant** — safe to pass to `run_backward`.
///
/// Tiers that explicitly use `&empty_pc` (Phase-B disjunctions in ACHAR tiers 3
/// and 7) are disabled when `assertion_postconditions` is non-empty, preventing
/// inductive-but-not-exit-closed candidates from slipping through.
///
/// Returns [`Err(BackwardError::CyclicCfgUnsupported)`] if no invariant is
/// found for any loop, or `Ok(vec![])` if the CFG has no loops.
fn synthesize_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    oracle: &Oracle,
    config: Option<&InvariantConfig>,
    debug_names: &HashMap<String, String>,
) -> Result<Vec<VerifiedLoopInvariant>, BackwardError> {
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let mode = config.map(|c| &c.mode).unwrap_or(&SynthesisMode::Default);
    let mut accepted = Vec::<VerifiedLoopInvariant>::new();

    for (index, loop_info) in loops.into_iter().enumerate() {
        let loop_loc = crate::may_must_analysis::loops::fmt_loop_loc(&loop_info);
        log::info!(
            target: "loop_invariant",
            "function {function} loop {} [{}]: synthesizing invariant [mode={}]",
            index + 1, loop_loc, mode.name()
        );
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} header {:?} body {:?}",
            index + 1, loop_info.header, loop_info.body
        );
        let mut accepted_candidate = None;

        // inner invariants as (header, formula) pairs, needed by check_loop_invariant_verbose
        let inner: Vec<(CfgNodeId, Formula)> = accepted.iter().map(|v| v.as_pair()).collect();

        // Entry-safety phase: `counter_init || safety` candidates.
        // Runs in Default mode (phase 1 of the default pipeline).
        // Exit closure is required: run_backward is not a sound substitute because
        // it blocks back edges and only injects invariants into reach at headers,
        // so it cannot reason about state after one or more iterations.
        if accepted_candidate.is_none()
            && !assertion_postconditions.is_empty()
            && *mode == SynthesisMode::Default
        {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {}: trying entry-safety generator",
                index + 1
            );
            let candidates =
                entry_safety_candidates(&loop_info, cfg, assertion_postconditions, &inner);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} entry-safety: {} candidates",
                index + 1, candidates.len()
            );
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} entry-safety candidates: {}",
                index + 1, format_candidates(&candidates, debug_names)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "entry-safety",
                &loop_info,
                cfg,
                &candidates,
                oracle,
                assertion_postconditions,
                &inner,
                debug_names,
            );
        }

        // Observer phase: only runs in ObserverOnly mode (for diagnostic comparison).
        // In Default mode, ACHAR subsumes observer by generating the same disjunction
        // candidates as part of its output.
        let run_observer = accepted_candidate.is_none()
            && !assertion_postconditions.is_empty()
            && *mode == SynthesisMode::ObserverOnly;
        if run_observer {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {}: trying observer generator",
                index + 1
            );
            let candidates =
                observer_disjunction_candidates(&loop_info, cfg, assertion_postconditions);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} observer: {} candidates",
                index + 1, candidates.len()
            );
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} observer candidates: {}",
                index + 1, format_candidates(&candidates, debug_names)
            );
            if !candidates.is_empty() {
                accepted_candidate = first_accepted_candidate(
                    function,
                    index + 1,
                    "observer",
                    &loop_info,
                    cfg,
                    &candidates,
                    oracle,
                    assertion_postconditions,
                    &inner,
                    debug_names,
                );
            }
        }

        // ACHAR phase: grammar-guided ICE CEGIS loop over the loop vocabulary.
        // Runs in Default (phase 2) and GrammarOnly modes.
        let run_achar = accepted_candidate.is_none()
            && matches!(mode, SynthesisMode::Default | SynthesisMode::GrammarOnly);
        if run_achar {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {}: trying achar cegis",
                index + 1
            );
            let achar_timeout = config
                .map(|c| c.achar_timeout)
                .unwrap_or(std::time::Duration::from_secs(10));
            accepted_candidate = achar::synthesize_with_cegis(
                &loop_info,
                cfg,
                assertion_postconditions,
                &inner,
                oracle,
                function,
                index + 1,
                achar_timeout,
            );
        }

        if accepted_candidate.is_none() {
            log::info!(
                target: "loop_invariant",
                "function {function} loop {}: no invariant accepted — synthesis failed",
                index + 1
            );
            return Err(BackwardError::CyclicCfgUnsupported);
        }

        let candidate = accepted_candidate.expect("checked above");
        accepted.push(VerifiedLoopInvariant::new(loop_info.header, candidate));
    }

    Ok(accepted)
}

fn compute_preliminary_backward_states(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    excluded_back_edges: &BTreeSet<CfgEdgeId>,
) -> Result<BTreeMap<CfgNodeId, Formula>, BackwardError> {
    let order = cfg
        .topological_order_excluding(excluded_back_edges)
        .ok_or(BackwardError::CyclicCfgUnsupported)?;
    let mut engine = RuleEngine::new(cfg);
    engine.init();
    for edge in excluded_back_edges {
        engine.block_edge(*edge);
    }

    let neg_obligation = Formula::not(site.obligation.clone());
    let pre_at_assertion = cfg
        .node(site.node)
        .map_err(|_| crate::may_must_analysis::rules::RuleError::UnknownNode { node: site.node })?
        .transfer
        .wp(&neg_obligation);
    engine.set_state(site.node, pre_at_assertion)?;

    for node in order.iter().rev() {
        for edge in cfg.incoming_edges(*node) {
            engine.notmay_pre(edge)?;
        }
    }

    Ok(engine
        .summaries()
        .iter()
        .map(|(id, summary)| (*id, summary.state.clone()))
        .collect())
}

/// Check that InductiveHint invariants satisfy exit closure for a specific assertion.
///
/// Runs the full three-part check on each hint (initiation, inductiveness, exit
/// closure) against the given `assertion_postconditions`.
///
/// Returns `Ok(Some(verified))` if all invariants pass all three checks;
/// `Ok(None)` if any fail — the caller should fall through to synthesis.
/// Only loops that have a matching hint are checked; others are silently skipped.
fn precomputed_satisfy_exit_closure(
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    hints: &[(CfgNodeId, Formula)],
    oracle: &Oracle,
) -> Result<Option<Vec<VerifiedLoopInvariant>>, BackwardError> {
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let mut accepted: Vec<VerifiedLoopInvariant> = Vec::new();
    for loop_info in &loops {
        if let Some((_, invariant)) = hints.iter().find(|(h, _)| *h == loop_info.header) {
            let inner: Vec<(CfgNodeId, Formula)> = accepted.iter().map(|v| v.as_pair()).collect();
            let result = check_loop_invariant_verbose(
                loop_info,
                cfg,
                invariant,
                oracle,
                assertion_postconditions,
                &inner,
            );
            log::debug!(
                target: "loop_invariant",
                "precomputed exit-closure check for invariant {} => {}",
                pretty_formula(invariant),
                match &result {
                    InvariantCheckResult::Accepted => "accepted".to_string(),
                    InvariantCheckResult::InitiationFailed { .. } => "rejected: initiation failed".to_string(),
                    InvariantCheckResult::InductivenessFailed { .. } => "rejected: inductiveness failed".to_string(),
                    InvariantCheckResult::ExitClosureFailed { exit_edge, .. } => format!("rejected: exit closure failed at {:?}", exit_edge),
                }
            );
            if !result.is_accepted() {
                log::debug!(
                    target: "loop_invariant",
                    "precomputed invariant failed exit closure — will fall through to synthesis"
                );
                return Ok(None);
            }
            accepted.push(VerifiedLoopInvariant::new(
                loop_info.header,
                invariant.clone(),
            ));
        }
    }
    Ok(Some(accepted))
}

fn conjunct_loop_invariants(invariants: &[VerifiedLoopInvariant]) -> BTreeMap<CfgNodeId, Formula> {
    let mut combined = BTreeMap::new();
    for inv in invariants {
        combined
            .entry(inv.header)
            .and_modify(|current: &mut Formula| {
                *current = Formula::and(current.clone(), inv.formula.clone());
            })
            .or_insert_with(|| inv.formula.clone());
    }
    combined
}

fn first_accepted_candidate(
    function: &str,
    loop_index: usize,
    phase: &str,
    loop_info: &crate::may_must_analysis::loops::LoopInfo,
    cfg: &AbstractCfg,
    candidates: &[Formula],
    oracle: &Oracle,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    accepted_inner: &[(CfgNodeId, Formula)],
    debug_names: &HashMap<String, String>,
) -> Option<Formula> {
    candidates.par_iter().find_map_any(|candidate| {
        let normalized = normalize_candidate(cfg, loop_info.header, candidate);
        // Skip tautologies: after WP normalization through the header, a candidate
        // such as `%cur <= select(stack, 0)` can collapse to `select(stack, 0) <= select(stack, 0)`.
        // Such formulas pass all checks trivially but contribute nothing to the proof.
        if is_tautology(&normalized) {
            return None;
        }
        let result = check_loop_invariant_verbose(
            loop_info,
            cfg,
            candidate,
            oracle,
            assertion_postconditions,
            accepted_inner,
        );
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} {} candidate {} => {}",
            loop_index,
            phase,
            pretty_formula_with_names(&normalized, debug_names),
            render_invariant_result(&result)
        );
        if result.is_accepted() {
            log::info!(
                target: "loop_invariant",
                "function {function} loop {}: {} accepted invariant: {}",
                loop_index, phase, pretty_formula_with_names(&normalized, debug_names)
            );
            Some(normalized)
        } else {
            None
        }
    })
}

/// Return true if `formula` is a tautology that contributes nothing to a proof.
///
/// Checks two classes:
/// * Structural: both sides of a comparison are identical (e.g. `x <= x`).
/// * Complementary disjunctions: two atoms in an `Or` together cover all
///   integers, e.g. `(a <= b) || (b <= a)` (total order) or
///   `(a < b) || (a >= b)` (complement). These pass all invariant checks
///   trivially but encode no information about program state.
pub(crate) fn is_tautology(formula: &Formula) -> bool {
    match formula {
        Formula::Le(a, b) | Formula::Ge(a, b) | Formula::Eq(a, b) => {
            format!("{a:?}") == format!("{b:?}")
        }
        Formula::And(items) => items.iter().all(is_tautology),
        Formula::Or(items) => {
            if items.iter().any(is_tautology) {
                return true;
            }
            // Check all pairs for complementary coverage.
            for i in 0..items.len() {
                for j in (i + 1)..items.len() {
                    if atoms_cover_all_integers(&items[i], &items[j]) {
                        return true;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Return true if `f1 || f2` is always true for integer-valued terms.
///
/// Covers two patterns:
/// * Complementary ops with the same terms: `a < b || a >= b`, `a <= b || a > b`.
/// * Total-order swapped: `a <= b || b <= a` (integers are totally ordered).
fn atoms_cover_all_integers(f1: &Formula, f2: &Formula) -> bool {
    let key = |a: &crate::common::formula::Term, b: &crate::common::formula::Term| {
        (format!("{a:?}"), format!("{b:?}"))
    };
    match (f1, f2) {
        // Complementary: f1 and f2 partition the integer line.
        (Formula::Lt(a1, b1), Formula::Ge(a2, b2))
        | (Formula::Ge(a1, b1), Formula::Lt(a2, b2))
        | (Formula::Le(a1, b1), Formula::Gt(a2, b2))
        | (Formula::Gt(a1, b1), Formula::Le(a2, b2)) => key(a1, b1) == key(a2, b2),
        // Swapped total-order: Le(a,b) || Le(b,a) = a<=b || b<=a = True.
        (Formula::Le(a1, b1), Formula::Le(a2, b2)) | (Formula::Ge(a1, b1), Formula::Ge(a2, b2)) => {
            key(a1, b1) == key(b2, a2)
        }
        _ => false,
    }
}

fn render_invariant_result(result: &InvariantCheckResult) -> String {
    match result {
        InvariantCheckResult::Accepted => "accepted".to_string(),
        InvariantCheckResult::InitiationFailed { .. } => "rejected: initiation failed".to_string(),
        InvariantCheckResult::InductivenessFailed { .. } => {
            "rejected: inductiveness failed".to_string()
        }
        InvariantCheckResult::ExitClosureFailed { exit_edge, .. } => {
            format!("rejected: exit closure failed at edge {:?}", exit_edge)
        }
    }
}

fn format_candidates(candidates: &[Formula], debug_names: &HashMap<String, String>) -> String {
    if candidates.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            candidates
                .iter()
                .map(|f| pretty_formula_with_names(f, debug_names))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

/// Format an [`AssertionResult`] for human-readable output.
///
/// The rendered string includes the assertion location, the judgement, and —
/// for `BugFound` — a formatted counterexample grouped by function.
///
/// # Output format
///
/// ```text
/// assertion #<id>  <location>
///   judgement: <Verified|UNSAFE|Unknown>
///   [counterexample or reach/state summary if Unknown]
/// ```
pub fn render_result(result: &AssertionResult) -> String {
    let names = &result.debug_names;
    let location = if !result.source_location.file.is_empty() {
        result.source_location.to_string()
    } else if result.source_location.line > 0 {
        result.source_location.to_string()
    } else {
        result.site_label.clone()
    };
    let mut lines = vec![format!("  assertion #{}  {}", result.site_id, location)];
    match &result.judgement {
        Judgement::Verified => lines.push("    judgement: Verified".to_string()),
        Judgement::Unknown => {
            lines.push("    judgement: Unknown".to_string());
            lines.push(format!(
                "    reach: {}",
                result.entry_summary.reach.pretty(names)
            ));
            lines.push(format!(
                "    state: {}",
                result.entry_summary.state.pretty(names)
            ));
        }
        Judgement::BugFound { model } => {
            lines.push("    judgement: UNSAFE".to_string());
            if let Some(model) = model.as_ref() {
                if !model.is_empty() {
                    lines.push("    counterexample:".to_string());
                    lines.push(render_counterexample(model, names));
                }
            }
        }
    }
    lines.join("\n")
}

/// Format an [`SmtModel`] as a grouped counterexample trace.
///
/// Variables are grouped by their owning function (the prefix before the first
/// `$` in the SMT name).  Synthetic names such as call-site temporaries and the
/// internal `__retval` carrier are filtered out by [`parse_model_var_name`].
///
/// # Output format
///
/// ```text
/// [function1]
///   var1 = value1
///   var2 = value2
/// [function2]
///   var3 = value3
/// ```
fn render_counterexample(model: &SmtModel, debug_names: &HashMap<String, String>) -> String {
    use std::collections::{BTreeMap, BTreeSet};
    let mut by_function: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Track (func, display_name) pairs already covered by a scalar entry so we
    // can suppress the redundant ArrayDefault memory entry for the same variable.
    let mut scalar_names_seen: BTreeSet<(String, String)> = BTreeSet::new();

    for (var, value) in &model.scalar {
        if let Some((func, local)) = parse_model_var_name(var.name()) {
            let display = debug_names
                .get(var.name())
                .cloned()
                .unwrap_or(local.clone());
            scalar_names_seen.insert((func.clone(), display.clone()));
            by_function
                .entry(func)
                .or_default()
                .push(format!("      {} = {}", display, value));
        }
    }
    for (name, value) in &model.memory {
        if let Some((func, local)) = parse_model_var_name(name) {
            let display = debug_names.get(name).cloned().unwrap_or(local.clone());
            // Skip ArrayDefault memory entries whose source name is already shown
            // by a scalar — Z3 picks an arbitrary default for unconstrained memory
            // regions, which would contradict the (more accurate) scalar value.
            if matches!(value, ModelValue::ArrayDefault(_))
                && scalar_names_seen.contains(&(func.clone(), display.clone()))
            {
                continue;
            }
            by_function.entry(func).or_default().push(format!(
                "      {}: {}",
                display,
                format_array_value(value)
            ));
        }
    }

    if by_function.is_empty() {
        return "      (no concrete values)".to_string();
    }

    let mut lines = Vec::new();
    for (func, mut entries) in by_function {
        entries.sort();
        entries.dedup();
        lines.push(format!("      [{}]", func));
        lines.extend(entries);
    }
    lines.join("\n")
}

/// Parse a namespaced SMT variable name into `(function, display_name)`.
///
/// The convention used by the adapter is `function$local`, e.g. `main$%x` or
/// `find_max$__ext_0`.  This function:
/// - returns `None` for call-site intermediates (`callN$...`);
/// - returns `None` for the internal return-value carrier `__retval`;
/// - maps `__ext_N` to the display string `param[N]`.
///
/// # Examples
///
/// - `main$%x` → `Some(("main", "%x"))`
/// - `find_max$__ext_0` → `Some(("find_max", "param[0]"))`
/// - `__retval` → `None`
/// - `call1$temp` → `None`
fn parse_model_var_name(name: &str) -> Option<(String, String)> {
    let dollar = name.find('$')?;
    let func = name[..dollar].to_string();
    let local = &name[dollar + 1..];

    // Skip call-site intermediate renames (callN$...)
    if local.starts_with("call") && local.contains('$') {
        return None;
    }
    // Skip synthetic return-value carrier
    if local == "__retval" {
        return None;
    }

    let display = if let Some(n) = local.strip_prefix("__ext_") {
        format!("param[{}]", n)
    } else {
        local.to_string()
    };

    Some((func, display))
}

/// Render a [`ModelValue`] that may represent a memory array.
///
/// `ArrayDefault` values are printed as `all elements = <default>` rather than
/// enumerating every index, keeping counterexample output concise.
///
/// # Examples
///
/// - `ArrayDefault(5)` → `"all elements = 5"`
/// - `Int(42)` → `"42"`
/// - `Bool(true)` → `"true"`
fn format_array_value(value: &ModelValue) -> String {
    match value {
        ModelValue::ArrayDefault(v) => format!("all elements = {}", v),
        other => other.to_string(),
    }
}

/// Pretty-print a [`Formula`] with soft line-wrapping at conjunction boundaries.
///
/// Short formulas (≤ 100 characters) are returned as-is.  Longer formulas have
/// their `&&` conjuncts broken onto separate indented lines so that log output
/// remains readable without truncation.
///
/// # Purpose
///
/// Used in invariant debugging logs to keep output concise and readable.  The
/// wrapping threshold is 100 characters.
pub fn pretty_formula(formula: &Formula) -> String {
    pretty_formula_with_names(formula, &std::collections::HashMap::new())
}

/// Like [`pretty_formula`] but substitutes region names with source variable
/// names from LLVM debug info (e.g. `select(main$stack0, 0)` → `array[0]`).
/// Pass `&adapted.debug_names` when the `AdaptedProcedure` is in scope.
pub fn pretty_formula_with_names(
    formula: &Formula,
    names: &std::collections::HashMap<String, String>,
) -> String {
    const WRAP_WIDTH: usize = 100;
    let rendered = formula.pretty(names);
    if rendered.len() <= WRAP_WIDTH {
        rendered
    } else {
        rendered.replace(" && ", "\n      && ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AssignValue, SourceLocation, TransferEffect, TransferFn};
    use crate::common::formula::{Sort, Term, Var};

    fn one_assertion_cfg() -> (AbstractCfg, AssertionSite) {
        let mut cfg = AbstractCfg::new("entry");
        let assert_node = cfg.add_node(
            "assert",
            TransferFn::new(vec![TransferEffect::Assign {
                target: Var::int("x"),
                value: AssignValue::Term(Term::int(1)),
            }]),
        );
        cfg.add_edge(cfg.entry(), assert_node, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(assert_node).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 1,
            node: assert_node,
            source_location: SourceLocation::new("t.c", 1, 1),
            location: "after assert".to_string(),
            obligation: Formula::eq(Term::var("x", Sort::Int), Term::int(1)),
        };
        (cfg, site)
    }

    #[test]
    fn analyze_returns_verified_for_trivial_safe_case() {
        let (cfg, site) = one_assertion_cfg();
        let oracle = Oracle::new();
        let result = analyze(&cfg, &site, &oracle).unwrap();
        assert!(matches!(result.judgement, Judgement::Verified));
    }

    #[test]
    fn analyze_rejects_cyclic_cfg() {
        let mut cfg = AbstractCfg::new("entry");
        let n = cfg.add_node("n", TransferFn::identity());
        cfg.add_edge(cfg.entry(), n, Formula::True, vec![]).unwrap();
        cfg.add_edge(n, cfg.entry(), Formula::True, vec![]).unwrap();
        cfg.mark_exit(n).unwrap();
        let site = AssertionSite {
            id: 1,
            node: n,
            source_location: SourceLocation::new("t.c", 1, 1),
            location: "loop".to_string(),
            obligation: Formula::True,
        };
        let oracle = Oracle::new();
        assert!(matches!(
            analyze(&cfg, &site, &oracle),
            Err(BackwardError::CyclicCfgUnsupported)
        ));
    }

    #[test]
    fn render_result_contains_judgement() {
        let (cfg, site) = one_assertion_cfg();
        let oracle = Oracle::new();
        let result = analyze(&cfg, &site, &oracle).unwrap();
        let rendered = render_result(&result);
        assert!(rendered.contains("judgement: Verified"));
    }
}
