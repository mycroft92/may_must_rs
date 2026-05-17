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
//! invariant-only path used by the interprocedural driver before full analysis.
//!
//! # Invariant synthesis
//!
//! Three algorithmic strategies are tried in order before an optional LLM-guided
//! CEGIS loop:
//!
//! 1. **Algorithmic** — pattern-matched candidates derived from loop guards and
//!    transfer effects (counter bounds, predicate assignments, …).
//! 2. **CHC** — Constrained Horn Clause solving for simple counter patterns.
//! 3. **Houdini** — weakening a large template set until an inductive subset
//!    remains.
//!
//! Each candidate is checked with [`check_loop_invariant_verbose`] from
//! [`loops`].  Loops are processed innermost-first so that inner invariants are
//! available when checking outer ones.

#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId};
use crate::common::adapter::AssertionSite;
use crate::common::formula::{Formula, ModelValue, SmtModel};
use crate::common::oracle::{Oracle, OracleError};
use crate::common::source::SourceLocation;
use crate::may_must_analysis::llm_provider::{
    build_full_loop_context, build_loop_invariant_prompt, collect_variable_sorts, parse_candidate,
    CegisAttempt, LlmBackend,
};
use crate::may_must_analysis::loops::{
    algorithmic_candidates, chc_loop_invariant, check_loop_invariant_verbose,
    collect_loop_body_int_constants, detect_loops, houdini_candidates, normalize_candidate,
    sort_innermost_first, InvariantCheckResult,
};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::providers::LoopContext;
use crate::may_must_analysis::rules::{Judgement, RuleEngine, RuleError};
use crate::may_must_analysis::summaries::SummaryTables;
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

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

/// Enumeration of the invariant-synthesis strategies available to
/// [`synthesize_loop_invariants`].
///
/// Strategies are tried in the order listed in [`InvariantConfig::methods`].
/// When the list is empty the default ordering is `Chc → Houdini → Template`.
///
/// # Variants
///
/// * `Chc` — Constrained Horn Clause solving for simple counter patterns (fast, specific).
/// * `Houdini` — weakening a large template set until an inductive subset remains (slower, general).
/// * `Template` — reserved for custom user-provided invariants (currently unused).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum InvariantMethod {
    Chc,
    Houdini,
    Template,
}

/// Runtime configuration for the loop-invariant synthesis pass.
///
/// An empty `methods` list enables the full default strategy sequence.
/// `skip_algorithmic` suppresses the fast pattern-based candidates even when
/// `methods` includes them — used when callers know the patterns will not match.
/// When `llm` is `Some` and `force` is set, LLM-guided CEGIS is attempted
/// before (or instead of) algorithmic strategies.
///
/// # Fields
///
/// * `methods` — strategies to try in order; empty means use default sequence.
/// * `llm` — optional configuration for LLM-guided CEGIS candidate generation.
/// * `skip_algorithmic` — if true, skip the fast pattern-matching phase.
pub struct InvariantConfig {
    pub methods: Vec<InvariantMethod>,
    pub llm: Option<LlmInvariantConfig>,
    pub skip_algorithmic: bool,
    /// Skip analysis of functions with more than this many instructions,
    /// returning UNKNOWN immediately. 0 means unlimited.
    pub max_function_size: usize,
}

impl Default for InvariantConfig {
    fn default() -> Self {
        Self {
            methods: Vec::new(),
            llm: None,
            skip_algorithmic: false,
            max_function_size: 500,
        }
    }
}

pub struct LlmInvariantConfig {
    pub backend: Box<dyn LlmBackend>,
    pub max_tries: usize,
    pub force: bool,
    pub prompt_template: Option<String>,
}

pub fn analyze(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
) -> Result<AssertionResult, BackwardError> {
    analyze_with_tables(cfg, "", site, oracle, &SummaryTables::new(), None, None)
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
/// 1. Back edges are detected and excluded from the topological order.
/// 2. If `precomputed` invariants are supplied and non-empty they are used as-is
///    (unless `force_llm` overrides them).
/// 3. Otherwise [`synthesize_loop_invariants`] is called, which tries
///    algorithmic, CHC, Houdini, Template, and LLM strategies in sequence.
/// 4. The accepted invariants are injected into `reach` at loop headers before
///    the final [`run_backward`] call.
///
/// # Parameters
///
/// * `tables` — interprocedural must/not-may summaries and cached loop
///   invariants produced by a prior module-level pass.
/// * `config` — controls which synthesis strategies are enabled.
/// * `precomputed` — invariants computed ahead of time by the driver's
///   [`discover_loop_invariants`] pass; avoids redundant synthesis work.
pub fn analyze_with_tables(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    tables: &SummaryTables,
    config: Option<&InvariantConfig>,
    precomputed: Option<&[(CfgNodeId, Formula)]>,
) -> Result<AssertionResult, BackwardError> {
    if cfg.topological_order().is_some() {
        return run_backward(cfg, site, oracle, &BTreeSet::new(), &[], tables);
    }

    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();
    let force_llm = config
        .and_then(|config| config.llm.as_ref())
        .is_some_and(|llm| llm.force);

    // Compute assertion-specific backward states once; shared by exit-closure
    // checking and synthesis so neither call repeats the backward pass.
    let assertion_postconditions = compute_preliminary_backward_states(cfg, site, &excluded)?;

    if let Some(precomputed) = precomputed {
        if !precomputed.is_empty() && !force_llm {
            // config=None signals the observer pattern: invariants skip exit closure and
            // are verified by run_backward directly.  In the regular (config=Some) path,
            // check exit closure first to see whether the precomputed invariant is strong
            // enough to discharge this specific assertion.
            let exit_closure_ok = config.is_none()
                || precomputed_satisfy_exit_closure(
                    cfg,
                    &assertion_postconditions,
                    precomputed,
                    oracle,
                )?;
            if exit_closure_ok {
                return run_backward(cfg, site, oracle, &excluded, precomputed, tables);
            }
            // Exit closure failed: the precomputed invariant does not discharge this
            // assertion.  Fall through to synthesis to find a stronger invariant.
            // Using run_backward here with an invariant that failed exit closure is
            // unsound — the backward state from the exit condition can collapse to
            // False at the entry via loop-initialization substitution, giving a
            // spurious Verified even when the assertion is violable.
            log::debug!(
                target: "loop_invariant",
                "function {function}: precomputed invariant failed exit closure — falling through to synthesis"
            );
        }
    }

    let invariants = synthesize_loop_invariants(
        cfg,
        function,
        &assertion_postconditions,
        &site.location,
        oracle,
        config,
    )?;
    if invariants.is_empty() {
        return Err(BackwardError::CyclicCfgUnsupported);
    }
    run_backward(cfg, site, oracle, &excluded, &invariants, tables)
}

/// Core bidirectional analysis pass.
///
/// This function implements the combined may/must check described in the paper:
///
/// 1. **Forward reach injection** — for each loop header `h` the accepted loop
///    invariant is conjuncted into `summary.reach` at `h`, establishing the
///    forward overapproximation of reachable states.  Back edges are blocked so
///    the [`RuleEngine`] can run in topological order.
///
/// 2. **Backward state seeding** — the weakest precondition of `NOT obligation`
///    is computed at the assertion node and stored as its initial `state`.  This
///    encodes the condition under which the assertion could be violated.
///
/// 3. **Fixpoint** — [`RuleEngine::run_to_fixpoint`] propagates both `reach`
///    (forward) and `state` (backward) simultaneously using the transfer
///    functions and edge guards of the CFG.
///
/// 4. **Decision** at the function entry node:
///    - `reach AND state` satisfiable → [`Judgement::BugFound`] with a concrete
///      model.
///    - `reach AND state` unsatisfiable → [`Judgement::Verified`].
///    - Neither can be determined → [`Judgement::Unknown`].
/// Core bidirectional analysis pass.
///
/// This function implements the combined may/must check described in the paper:
///
/// 1. **Forward reach injection** — for each loop header `h` the accepted loop
///    invariant is conjuncted into `summary.reach` at `h`, establishing the
///    forward overapproximation of reachable states.  Back edges are blocked so
///    the [`RuleEngine`] can run in topological order.
///
/// 2. **Backward state seeding** — the weakest precondition of `NOT obligation`
///    is computed at the assertion node and stored as its initial `state`.  This
///    encodes the condition under which the assertion could be violated.
///
/// 3. **Fixpoint** — [`RuleEngine::run_to_fixpoint`] propagates both `reach`
///    (forward) and `state` (backward) simultaneously using the transfer
///    functions and edge guards of the CFG.
///
/// 4. **Decision** at the function entry node:
///    - `reach AND state` satisfiable → [`Judgement::BugFound`] with a concrete
///      model.
///    - `reach AND state` unsatisfiable → [`Judgement::Verified`].
///    - Neither can be determined → [`Judgement::Unknown`].
fn run_backward(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    excluded_edges: &BTreeSet<crate::common::abstract_cfg::CfgEdgeId>,
    loop_invariants: &[(CfgNodeId, Formula)],
    tables: &SummaryTables,
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
    })
}

/// Pre-pass that caches loop invariants before full per-assertion analysis.
///
/// Calls [`synthesize_loop_invariants`] with empty `assertion_postconditions`
/// (scope = `True`), so exit closure is skipped — no assertion site is
/// available yet.  The resulting invariants are cached in [`SummaryTables`]
/// and reused across multiple assertion checks in the same function.
///
/// Returns `None` if any loop cannot be handled (i.e. synthesis fails for it).
///
/// # Purpose
///
/// This is called once per function before all assertion checks (in `driver.rs`)
/// to avoid repeatedly synthesising invariants for each assertion.
pub fn discover_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    oracle: &Oracle,
) -> Option<Vec<(CfgNodeId, Formula)>> {
    synthesize_loop_invariants(cfg, function, &BTreeMap::new(), "", oracle, None).ok()
}

/// Invariant synthesis pipeline for a cyclic CFG.
///
/// Accepts `assertion_postconditions` (WP of `NOT obligation` propagated
/// backward with back edges blocked) and an optional `assertion_location` string
/// for LLM context.  Pass `&BTreeMap::new()` and `""` from
/// [`discover_loop_invariants`] (the pre-pass with no assertion site); pass
/// the computed postconditions and the site label from [`analyze_with_tables`].
///
/// For each detected loop (innermost-first) the function tries the enabled
/// candidate strategies in order.  When `assertion_postconditions` is empty,
/// exit closure is effectively skipped (no assertion site to check against),
/// making this safe to call from the pre-pass.
///
/// Returns [`Err(BackwardError::CyclicCfgUnsupported)`] if no invariant is
/// found for any loop, or `Ok(vec![])` if the CFG has no loops.
fn synthesize_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    assertion_location: &str,
    oracle: &Oracle,
    config: Option<&InvariantConfig>,
) -> Result<Vec<(CfgNodeId, Formula)>, BackwardError> {
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let methods = selected_methods(config);
    let skip_algorithmic = config.is_some_and(|config| config.skip_algorithmic);
    let llm_config = config.and_then(|config| config.llm.as_ref());
    let force_llm = llm_config.is_some_and(|llm| llm.force);
    let mut accepted = Vec::<(CfgNodeId, Formula)>::new();

    for (index, loop_info) in loops.into_iter().enumerate() {
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} header {:?} body {:?}",
            index + 1,
            loop_info.header,
            loop_info.body
        );
        let variable_sorts = collect_variable_sorts(&loop_info, cfg);
        let mut accepted_candidate = None;

        if !skip_algorithmic && !force_llm {
            let candidates = algorithmic_candidates(&loop_info, cfg);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} algorithmic candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "algorithmic",
                &loop_info,
                cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Chc) {
            let candidates = chc_loop_invariant(&loop_info, cfg)
                .into_iter()
                .collect::<Vec<_>>();
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} CHC candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "chc",
                &loop_info,
                cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Houdini) {
            let header_wp = assertion_postconditions
                .get(&loop_info.header)
                .cloned()
                .unwrap_or(Formula::True);
            let loop_constants = collect_loop_body_int_constants(&loop_info, cfg);
            let candidates = houdini_candidates(&variable_sorts, &header_wp, &loop_constants);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} houdini candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "houdini",
                &loop_info,
                cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Template) {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} template candidates: []",
                index + 1
            );
            accepted_candidate = try_template_invariant();
        }

        if accepted_candidate.is_none() {
            if let Some(llm) = llm_config {
                let exit_postcondition =
                    exit_postcondition_for_loop(&loop_info, &assertion_postconditions, cfg);
                let mut attempts = Vec::<CegisAttempt>::new();
                for _ in 0..llm.max_tries.max(1) {
                    let ctx = build_full_loop_context(
                        LoopContext {
                            function: function.to_string(),
                            loop_id: index + 1,
                        },
                        &loop_info,
                        cfg,
                        assertion_location.to_string(),
                        exit_postcondition.clone(),
                        attempts.clone(),
                    );
                    let prompt = build_loop_invariant_prompt(&ctx, llm.prompt_template.as_deref());
                    let Some(raw) = llm.backend.propose(&prompt) else {
                        log::debug!(
                            target: "loop_invariant",
                            "function {function} loop {} llm candidate: <none>",
                            index + 1
                        );
                        continue;
                    };
                    let Some(candidate) = parse_candidate(&raw, &variable_sorts) else {
                        log::debug!(
                            target: "loop_invariant",
                            "function {function} loop {} llm candidate parse failed: {}",
                            index + 1,
                            raw.trim()
                        );
                        continue;
                    };
                    let result = check_loop_invariant_verbose(
                        &loop_info,
                        cfg,
                        &candidate,
                        oracle,
                        &assertion_postconditions,
                        &accepted,
                    );
                    log::debug!(
                        target: "loop_invariant",
                        "function {function} loop {} llm candidate {} => {}",
                        index + 1,
                        pretty_formula(&candidate),
                        render_invariant_result(&result)
                    );
                    if result == InvariantCheckResult::Accepted {
                        accepted_candidate = Some(candidate);
                        break;
                    }
                    attempts.push(CegisAttempt {
                        candidate,
                        failure: render_invariant_result(&result),
                    });
                }
            }
        }

        if accepted_candidate.is_none() {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} accepted no invariant",
                index + 1
            );
            return Err(BackwardError::CyclicCfgUnsupported);
        }

        let candidate = accepted_candidate.expect("checked accepted candidate presence");
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} accepted invariant: {}",
            index + 1,
            pretty_formula(&candidate)
        );
        accepted.push((loop_info.header, candidate));
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

/// Check that every precomputed loop invariant satisfies exit closure for this assertion.
///
/// `discover_loop_invariants` skips exit closure (it has no assertion site). Before
/// reusing those invariants in [`run_backward`], we must verify that each invariant
/// satisfies all three checks — initiation, inductiveness, and exit closure — for
/// the specific assertion site being checked.
///
/// Exit closure is always checked for every loop that has a precomputed invariant.
/// The earlier optimisation that skipped the check when the loop appeared not to
/// write any variable mentioned in the obligation was removed because it produced
/// false-Verified results: when the obligation is on a loaded scalar, its source
/// region name does not appear in the obligation formula, so the syntactic check
/// incorrectly declared the loop irrelevant (see `debug/array-2-false-safe.md`).
///
/// Returns `Ok(true)` if every invariant passes all three checks (including exit
/// closure), `Ok(false)` if any fails. Callers should fall through to
/// [`synthesize_loop_invariants`] when this returns `false`.
fn precomputed_satisfy_exit_closure(
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    precomputed: &[(CfgNodeId, Formula)],
    oracle: &Oracle,
) -> Result<bool, BackwardError> {
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let mut accepted_inner: Vec<(CfgNodeId, Formula)> = Vec::new();
    for loop_info in &loops {
        if let Some((_, invariant)) = precomputed.iter().find(|(h, _)| *h == loop_info.header) {
            let result = check_loop_invariant_verbose(
                loop_info,
                cfg,
                invariant,
                oracle,
                &assertion_postconditions,
                &accepted_inner,
            );
            log::debug!(
                target: "loop_invariant",
                "precomputed exit-closure check for invariant {} => {}",
                pretty_formula(invariant),
                match &result {
                    InvariantCheckResult::Accepted => "accepted".to_string(),
                    InvariantCheckResult::InitiationFailed => "rejected: initiation failed".to_string(),
                    InvariantCheckResult::InductivenessFailed => "rejected: inductiveness failed".to_string(),
                    InvariantCheckResult::ExitClosureFailed { exit_edge } => format!("rejected: exit closure failed at {:?}", exit_edge),
                }
            );
            if result != InvariantCheckResult::Accepted {
                return Ok(false);
            }
            accepted_inner.push((loop_info.header, invariant.clone()));
        }
    }
    Ok(true)
}

fn selected_methods(config: Option<&InvariantConfig>) -> Vec<InvariantMethod> {
    let Some(config) = config else {
        return vec![
            InvariantMethod::Chc,
            InvariantMethod::Houdini,
            InvariantMethod::Template,
        ];
    };
    if config.methods.is_empty() {
        vec![
            InvariantMethod::Chc,
            InvariantMethod::Houdini,
            InvariantMethod::Template,
        ]
    } else {
        config.methods.clone()
    }
}

fn conjunct_loop_invariants(invariants: &[(CfgNodeId, Formula)]) -> BTreeMap<CfgNodeId, Formula> {
    let mut combined = BTreeMap::new();
    for (header, invariant) in invariants {
        combined
            .entry(*header)
            .and_modify(|current: &mut Formula| {
                *current = Formula::and(current.clone(), invariant.clone());
            })
            .or_insert_with(|| invariant.clone());
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
) -> Option<Formula> {
    candidates.par_iter().find_map_any(|candidate| {
        let result = check_loop_invariant_verbose(
            loop_info,
            cfg,
            candidate,
            oracle,
            assertion_postconditions,
            accepted_inner,
        );
        let normalized = normalize_candidate(cfg, loop_info.header, candidate);
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} {} candidate {} => {}",
            loop_index,
            phase,
            pretty_formula(&normalized),
            render_invariant_result(&result)
        );
        (result == InvariantCheckResult::Accepted).then_some(normalized)
    })
}

fn try_template_invariant() -> Option<Formula> {
    None
}

fn exit_postcondition_for_loop(
    loop_info: &crate::may_must_analysis::loops::LoopInfo,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    cfg: &AbstractCfg,
) -> Formula {
    let mut postconditions = Vec::new();
    for edge_id in &loop_info.exit_edges {
        let Ok(edge) = cfg.edge(*edge_id) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        postconditions.push(postcondition.clone());
    }
    Formula::or_all(postconditions)
}

fn render_invariant_result(result: &InvariantCheckResult) -> String {
    match result {
        InvariantCheckResult::Accepted => "accepted".to_string(),
        InvariantCheckResult::InitiationFailed => "rejected: initiation failed".to_string(),
        InvariantCheckResult::InductivenessFailed => "rejected: inductiveness failed".to_string(),
        InvariantCheckResult::ExitClosureFailed { exit_edge } => {
            format!("rejected: exit closure failed at edge {:?}", exit_edge)
        }
    }
}

fn format_candidates(candidates: &[Formula]) -> String {
    if candidates.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            candidates
                .iter()
                .map(pretty_formula)
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
            lines.push(format!("    reach: {}", result.entry_summary.reach));
            lines.push(format!("    state: {}", result.entry_summary.state));
        }
        Judgement::BugFound { model } => {
            lines.push("    judgement: UNSAFE".to_string());
            if let Some(model) = model.as_ref() {
                if !model.is_empty() {
                    lines.push("    counterexample:".to_string());
                    lines.push(render_counterexample(model));
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
fn render_counterexample(model: &SmtModel) -> String {
    use std::collections::BTreeMap;
    let mut by_function: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for (var, value) in &model.scalar {
        if let Some((func, local)) = parse_model_var_name(var.name()) {
            by_function
                .entry(func)
                .or_default()
                .push(format!("      {} = {}", local, value));
        }
    }
    for (name, value) in &model.memory {
        if let Some((func, local)) = parse_model_var_name(name) {
            by_function.entry(func).or_default().push(format!(
                "      {}: {}",
                local,
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
    const WRAP_WIDTH: usize = 100;
    let rendered = formula.to_string();
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
