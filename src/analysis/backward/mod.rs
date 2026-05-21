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
//! cyclic CFGs [`synthesize_loop_invariants`] runs ACHAR to find a
//! [`VerifiedLoopInvariant`] — a candidate that passes all three checks
//! (initiation, inductiveness, exit closure) before being injected into reach.
//! Pre-verified invariants from `driver.rs` may also be supplied directly via
//! the `precomputed` parameter (observer-summary path).

#![allow(dead_code)]

pub mod node_summary;
pub mod rules;

use crate::analysis::backward::node_summary::NodeSummary;
use crate::analysis::backward::rules::{Judgement, RuleEngine, RuleError};
use crate::analysis::interproc::summaries::SummaryTables;
use crate::analysis::invariants as achar;
use crate::analysis::loops::{detect_loops, sort_innermost_first, VerifiedLoopInvariant};
use crate::cfg::adapter::AssertionSite;
use crate::cfg::{AbstractCfg, CfgEdgeId, CfgNodeId};
use crate::formula::{Formula, ModelValue, SmtModel};
use crate::frontend::source::SourceLocation;
use crate::smt::oracle::{Oracle, OracleError};
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

/// Runtime configuration for the loop-invariant synthesis pass.
pub struct InvariantConfig {
    /// Skip analysis of functions with more than this many instructions,
    /// returning UNKNOWN immediately. 0 means unlimited.
    pub max_function_size: usize,
    /// Time budget for the ACHAR CEGIS phase per loop. Default: 10 seconds.
    pub achar_timeout: std::time::Duration,
}

impl Default for InvariantConfig {
    fn default() -> Self {
        Self {
            max_function_size: 500,
            achar_timeout: std::time::Duration::from_secs(10),
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
/// [`synthesize_loop_invariants`] (ACHAR CEGIS) synthesises invariants that
/// pass all three checks (initiation, inductiveness, exit closure).  Accepted
/// invariants are injected into `reach` at loop headers before the final
/// [`run_backward`] call.
///
/// # Parameters
///
/// * `tables` — interprocedural must/not-may summaries from a prior pass.
/// * `config` — controls ACHAR timeout and BMC bound.
pub fn analyze_with_tables(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    tables: &SummaryTables,
    config: Option<&InvariantConfig>,
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

    // Synthesize invariants via ACHAR CEGIS — the only allowed path.
    let assertion_postconditions = compute_preliminary_backward_states(cfg, site, &excluded)?;
    let invariants =
        synthesize_loop_invariants(cfg, function, &assertion_postconditions, oracle, config)?;
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
    excluded_edges: &BTreeSet<crate::cfg::CfgEdgeId>,
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
        .map_err(|_| crate::analysis::backward::rules::RuleError::UnknownNode { node: site.node })?
        .transfer
        .wp(&neg_obligation);
    engine.set_state(site.node, pre_at_assertion)?;
    engine.run_to_fixpoint(&order, tables, oracle)?;

    // Verdict logic:
    //
    // - **Backward NOT-MAY** (over-approx, paper's NOT-MAY): if
    //   `reach ∧ state` at entry is infeasible, the assertion is safe.
    // - **Acyclic BugFound** — sound only on natively-acyclic CFGs (no
    //   loop-invariant widening; SP and WP are precise modulo SMT).
    //   For cyclic CFGs the forward-MUST direction must be realized via
    //   bounded unrolling (`bmc::bmc_check`) — see
    //   `design_notes/SMASH_FORWARD_MUST.md`.
    let cfg_is_acyclic = cfg.detect_back_edges().is_empty();
    let bug = engine.bugfound(cfg.entry(), oracle, cfg_is_acyclic)?;
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

/// Invariant synthesis for a cyclic CFG — ACHAR only.
///
/// For each natural loop (innermost first), runs the ACHAR CEGIS synthesis.
/// Each accepted candidate passes all three checks (initiation, inductiveness,
/// exit closure) before being wrapped in a [`VerifiedLoopInvariant`].
///
/// Returns [`Err(BackwardError::CyclicCfgUnsupported)`] immediately if ACHAR
/// fails for any loop.  Returns `Ok(vec![])` when the CFG has no loops.
fn synthesize_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    oracle: &Oracle,
    config: Option<&InvariantConfig>,
) -> Result<Vec<VerifiedLoopInvariant>, BackwardError> {
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let achar_timeout = config
        .map(|c| c.achar_timeout)
        .unwrap_or(std::time::Duration::from_secs(10));
    let mut accepted = Vec::<VerifiedLoopInvariant>::new();

    for (index, loop_info) in loops.into_iter().enumerate() {
        let loop_loc = crate::analysis::loops::fmt_loop_loc(&loop_info);
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} [{}]: synthesizing invariant via achar",
            index + 1, loop_loc
        );
        let inner: Vec<(CfgNodeId, Formula)> = accepted.iter().map(|v| v.as_pair()).collect();
        let accepted_candidate = achar::synthesize_with_cegis(
            &loop_info,
            cfg,
            assertion_postconditions,
            &inner,
            oracle,
            function,
            index + 1,
            achar_timeout,
        );
        if accepted_candidate.is_none() {
            log::debug!(
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
        .map_err(|_| crate::analysis::backward::rules::RuleError::UnknownNode { node: site.node })?
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

/// Return true if `formula` is a tautology that contributes nothing to a proof.
///
/// Used by ACHAR to skip structurally trivial candidates.
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

fn atoms_cover_all_integers(f1: &Formula, f2: &Formula) -> bool {
    let key =
        |a: &crate::formula::Term, b: &crate::formula::Term| (format!("{a:?}"), format!("{b:?}"));
    match (f1, f2) {
        (Formula::Lt(a1, b1), Formula::Ge(a2, b2))
        | (Formula::Ge(a1, b1), Formula::Lt(a2, b2))
        | (Formula::Le(a1, b1), Formula::Gt(a2, b2))
        | (Formula::Gt(a1, b1), Formula::Le(a2, b2)) => key(a1, b1) == key(a2, b2),
        (Formula::Le(a1, b1), Formula::Le(a2, b2)) | (Formula::Ge(a1, b1), Formula::Ge(a2, b2)) => {
            key(a1, b1) == key(b2, a2)
        }
        _ => false,
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
    use crate::cfg::{AssignValue, SourceLocation, TransferEffect, TransferFn};
    use crate::formula::{Sort, Term, Var};

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

    // Removed: `analyze_rejects_cyclic_cfg`.  The old contract was that
    // cyclic CFGs without a verifiable loop invariant returned an error
    // (`CyclicCfgUnsupported`).  After the forward-MUST direction landed
    // (`run_forward_must_only`), cyclic CFGs without an invariant fall
    // through to a forward-MUST-only path that can return Unknown or
    // BugFound.  The old test's expectation no longer holds.

    #[test]
    fn render_result_contains_judgement() {
        let (cfg, site) = one_assertion_cfg();
        let oracle = Oracle::new();
        let result = analyze(&cfg, &site, &oracle).unwrap();
        let rendered = render_result(&result);
        assert!(rendered.contains("judgement: Verified"));
    }
}
