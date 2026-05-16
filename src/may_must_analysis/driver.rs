//! Module-level orchestration of the may/must analysis.
//!
//! # Responsibilities
//!
//! This module drives the full interprocedural analysis of an LLVM module:
//!
//! 1. **Return-summary inference** — for each function, a [`ReturnSummary`]
//!    relating the return value to the formal parameters is computed.  Acyclic
//!    functions are handled directly by `compute_return_summary`; looping
//!    functions that observe an array argument are handled by the *observer
//!    pattern* ([`infer_cyclic_observer_summary`]).
//!
//! 2. **Call order / recursion detection** — [`recursive_functions`] identifies
//!    mutually recursive functions so their summaries can be flagged.
//!
//! 3. **Loop invariant pre-computation** — before the per-assertion backward
//!    pass, [`discover_loop_invariants`] is called for each looping function.
//!    The results are cached in [`SummaryTables`] and reused across multiple
//!    assertions in the same function.
//!
//! 4. **Per-function verification** — [`analyze_with_summaries`] lowers a
//!    [`FunctionGraph`] via the adapter, retrieves or synthesises loop
//!    invariants, and calls [`analyze_with_tables`] for each [`AssertionSite`].
//!
//! # Observer pattern for cyclic callees
//!
//! When a looping callee reads an array parameter and returns a summary value
//! (e.g. a maximum or sum), [`infer_cyclic_observer_summary`] synthesises an
//! invariant by examining which array indices the function accesses, then
//! verifying a candidate relation `retval >= array[i]` via the full
//! bidirectional check.  The invariant synthesis step
//! ([`observer_summary_invariants`]) intentionally skips the exit-closure check
//! because the authoritative proof is delegated to the subsequent
//! `analyze_with_tables` call.

#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId, SourceLocation};
use crate::common::adapter::{
    adapt, adapt_with_purity_and_summaries, collect_callee_names, compute_return_summary,
    ext_region_name, synthetic_retval_name, AdaptedProcedure, AdapterError, AssertionSite,
    CallSummaryRegistry, ReturnSummary,
};
use crate::common::alias_analysis::run_alias_analysis;
use crate::common::formula::{Formula, Memory, Term, Var};
use crate::common::llvm_utils::program_graph::FunctionGraph;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::{
    analyze, analyze_with_tables, discover_loop_invariants, render_result, AssertionResult,
    BackwardError, InvariantConfig,
};
use crate::may_must_analysis::loops::{
    check_loop_invariant_verbose, detect_loops, normalize_candidate, sort_innermost_first,
    InvariantCheckResult, LoopInfo,
};
use crate::may_must_analysis::providers::{CandidateProvider, NoProvider};
use crate::may_must_analysis::rules::{Judgement, RuleEngine};
use crate::may_must_analysis::summaries::{MustSummary, NotMaySummary, SummaryTables};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug)]
pub struct ProcedureReport {
    pub procedure: String,
    pub assertions: Vec<AssertionResult>,
    pub failures: Vec<String>,
    pub loop_count: usize,
    pub instruction_count: usize,
    pub recursive: bool,
}

impl fmt::Display for ProcedureReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "procedure {}", self.procedure)?;
        for assertion in &self.assertions {
            writeln!(f, "{}", render_result(assertion))?;
        }
        for failure in &self.failures {
            writeln!(f, "  unsupported: {failure}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SafetyVerdict {
    Safe,
    Unsafe,
    Unknown,
}

impl fmt::Display for SafetyVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SafetyVerdict::Safe => write!(f, "SAFE"),
            SafetyVerdict::Unsafe => write!(f, "UNSAFE"),
            SafetyVerdict::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

impl ProcedureReport {
    pub fn verdict(&self) -> SafetyVerdict {
        if !self.failures.is_empty() {
            return SafetyVerdict::Unknown;
        }
        if self.assertions.is_empty() {
            return SafetyVerdict::Safe;
        }
        let mut all_verified = true;
        for assertion in &self.assertions {
            match assertion.judgement {
                Judgement::Verified => {}
                Judgement::BugFound { .. } => return SafetyVerdict::Unsafe,
                Judgement::Unknown => all_verified = false,
            }
        }
        if all_verified {
            SafetyVerdict::Safe
        } else {
            SafetyVerdict::Unknown
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error(transparent)]
    Adapter(#[from] AdapterError),
}

#[derive(Clone, Debug, Default)]
pub struct ModuleReport {
    pub reports: Vec<ProcedureReport>,
    pub summaries: SummaryTables,
    pub computed_summaries: Vec<ReturnSummary>,
}

pub fn analyze_function_graph(
    graph: &FunctionGraph,
    oracle: &Oracle,
) -> Result<ProcedureReport, DriverError> {
    analyze_with_summaries(
        graph,
        &BTreeSet::new(),
        &CallSummaryRegistry::new(),
        oracle,
        None,
        None,
    )
}

/// Analyse every function in an LLVM module and return a [`ModuleReport`].
///
/// Convenience wrapper that runs with a default [`InvariantConfig`] and no
/// external candidate provider.  See [`analyze_module_with_llm`] for the
/// full pipeline description.
pub fn analyze_module(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<ModuleReport, DriverError> {
    analyze_module_with_provider(graphs, memory_pure, &NoProvider, oracle)
}

/// Analyse every function in an LLVM module, using `provider` for external
/// summaries, and return a [`ModuleReport`].
///
/// Convenience wrapper around [`analyze_module_with_llm`] that supplies a
/// default [`InvariantConfig`].
pub fn analyze_module_with_provider(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
) -> Result<ModuleReport, DriverError> {
    analyze_module_with_llm(
        graphs,
        memory_pure,
        provider,
        oracle,
        &InvariantConfig::default(),
    )
}

/// Full whole-module analysis entry point.
///
/// Orchestrates the following passes in order:
///
/// 0. Run [`run_alias_analysis`] once on the entire module.  The resulting
///    [`AliasResult`] is shared across all lowering calls so that
///    `resolve_memory_effects` can resolve pointer operations that the local
///    `PointerEnv` alone cannot handle.
/// 1. Load manually-provided summaries from `provider` for any callee not
///    defined in the module.
/// 2. Iteratively infer [`ReturnSummary`] entries for all in-module functions
///    (up to `graphs.len()` rounds to converge mutual calls).
/// 3. Convert inferred summaries to must/not-may entries in [`SummaryTables`].
/// 4. Pre-compute and cache loop invariants for every looping function via
///    [`discover_loop_invariants`].
/// 5. Run [`analyze_with_summaries`] for each function using `inv_config` to
///    control the invariant search, and collect per-procedure reports.
pub fn analyze_module_with_llm(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
    inv_config: &InvariantConfig,
) -> Result<ModuleReport, DriverError> {
    let alias = run_alias_analysis(graphs);
    let mut summaries = CallSummaryRegistry::new();

    let in_graph = graphs
        .iter()
        .map(|graph| graph.name.clone())
        .collect::<BTreeSet<_>>();
    for callee in collect_callee_names(graphs) {
        if in_graph.contains(&callee) {
            continue;
        }
        if let Some(summary) = provider.function_summary(&callee) {
            summaries.insert(summary);
        }
    }

    for _ in 0..graphs.len().max(1) {
        let snapshot = summaries.clone();
        for graph in graphs {
            if let Ok(adapted) =
                adapt_with_purity_and_summaries(graph, memory_pure, &snapshot, &alias)
            {
                if let Some(summary) = infer_return_summary(graph, &adapted, oracle) {
                    summaries.insert(summary);
                }
            }
        }
    }

    let recursive = recursive_functions(graphs);
    let mut summary_tables = SummaryTables::new();
    for summary in summaries.summaries().values() {
        summary_tables.add_must(
            summary.function.clone(),
            MustSummary {
                precondition: crate::common::formula::Formula::True,
                postcondition: summary.relation.clone(),
            },
        );
        summary_tables.add_notmay(
            summary.function.clone(),
            NotMaySummary {
                precondition: crate::common::formula::Formula::True,
                postcondition: crate::common::formula::Formula::not(summary.relation.clone()),
            },
        );
    }
    let mut reports = Vec::new();
    for graph in graphs {
        let adapted = if summaries.is_empty() && memory_pure.is_empty() {
            adapt(graph)
        } else {
            adapt_with_purity_and_summaries(graph, memory_pure, &summaries, &alias)
        };
        let Ok(adapted) = adapted else {
            continue;
        };
        if adapted.cfg.topological_order().is_some() {
            continue;
        }
        if let Some(invariants) = discover_loop_invariants(&adapted.cfg, &adapted.name, oracle) {
            summary_tables.set_loop_invariants(adapted.name.clone(), invariants);
        }
    }
    for graph in graphs {
        let report = match analyze_with_summaries(
            graph,
            memory_pure,
            &summaries,
            oracle,
            Some(&summary_tables),
            Some(inv_config),
        ) {
            Ok(report) => report,
            Err(error) => ProcedureReport {
                procedure: graph.name.clone(),
                assertions: Vec::new(),
                failures: vec![error.to_string()],
                loop_count: 0,
                instruction_count: graph.vertices.len(),
                recursive: false,
            },
        };
        reports.push(report);
        if let Some(report) = reports.last_mut() {
            report.recursive = recursive.contains(&graph.name);
        }
    }
    Ok(ModuleReport {
        reports,
        summaries: summary_tables,
        computed_summaries: summaries.summaries().values().cloned().collect(),
    })
}

pub fn analyze_function_graph_with_purity(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<ProcedureReport, DriverError> {
    analyze_with_summaries(
        graph,
        memory_pure,
        &CallSummaryRegistry::new(),
        oracle,
        None,
        None,
    )
}

/// Lower and verify a single function, returning a [`ProcedureReport`].
///
/// This is the per-function workhorse called by both [`analyze_module_with_llm`]
/// and the standalone `analyze_function_graph*` helpers.
///
/// The function runs [`run_alias_analysis`] on `graph` alone before lowering.
/// When called from the full module analysis the per-function AA is a subset
/// of the module-wide one; it is still sound (flow-insensitive AA over a
/// subset of the IR is an over-approximation of the same constraints).
///
/// If `tables` supplies pre-computed loop invariants for this function they
/// are used directly; otherwise [`discover_loop_invariants`] is called.
/// When `config` is `None`, the default invariant-search configuration is used.
pub fn analyze_with_summaries(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    summaries: &CallSummaryRegistry,
    oracle: &Oracle,
    tables: Option<&SummaryTables>,
    config: Option<&InvariantConfig>,
) -> Result<ProcedureReport, DriverError> {
    let max_size = config.map_or(500, |c| c.max_function_size);
    if max_size > 0 && graph.vertices.len() > max_size {
        return Ok(ProcedureReport {
            procedure: graph.name.clone(),
            assertions: Vec::new(),
            failures: vec![format!(
                "function too large ({} instructions > limit {}): skipped",
                graph.vertices.len(),
                max_size
            )],
            loop_count: 0,
            instruction_count: graph.vertices.len(),
            recursive: false,
        });
    }

    let alias = run_alias_analysis(std::slice::from_ref(graph));
    let adapted = if summaries.is_empty() && memory_pure.is_empty() {
        adapt(graph)?
    } else {
        adapt_with_purity_and_summaries(graph, memory_pure, summaries, &alias)?
    };
    let precomputed_owned = tables
        .and_then(|tables| {
            let invariants = tables.get_loop_invariants(&adapted.name);
            (!invariants.is_empty()).then(|| invariants.to_vec())
        })
        .or_else(|| discover_loop_invariants(&adapted.cfg, &adapted.name, oracle));
    let precomputed = precomputed_owned.as_deref();

    let mut assertions = Vec::new();
    let mut failures = Vec::new();
    for site in &adapted.assertions {
        let result = if let Some(tables) = tables {
            analyze_with_tables(
                &adapted.cfg,
                &adapted.name,
                site,
                oracle,
                tables,
                config,
                precomputed,
            )
        } else {
            analyze(&adapted.cfg, site, oracle)
        };
        match result {
            Ok(result) => assertions.push(result),
            Err(BackwardError::CyclicCfgUnsupported) => failures.push(format!(
                "assertion #{} ({}): CFG has a cycle and no loop invariant was accepted",
                site.id, site.location
            )),
            Err(error) => failures.push(format!(
                "assertion #{} ({}): {}",
                site.id, site.location, error
            )),
        }
    }

    Ok(ProcedureReport {
        procedure: adapted.name,
        assertions,
        failures,
        loop_count: adapted.cfg.detect_back_edges().len(),
        instruction_count: graph.vertices.len(),
        recursive: false,
    })
}

fn infer_return_summary(
    graph: &FunctionGraph,
    adapted: &AdaptedProcedure,
    oracle: &Oracle,
) -> Option<ReturnSummary> {
    compute_return_summary(graph, adapted)
        .or_else(|| infer_cyclic_observer_summary(graph, adapted, oracle))
}

/// Infer a return summary for a looping function that observes an array argument.
///
/// This implements the *observer pattern*: if a function iterates over an array
/// pointer parameter and returns a value derived from the array elements, this
/// function attempts to prove relations of the form
/// `retval >= array[i]` for each candidate index `i`.
///
/// The approach:
/// 1. Skip acyclic functions and functions without pointer parameters.
/// 2. For each pointer parameter, scan the CFG for accessed indices
///    ([`observer_candidate_indices`]).
/// 3. For each index, construct a synthetic assertion site at the function exit
///    and call [`observer_summary_invariants`] to get a loop invariant.
/// 4. Run the full [`analyze_with_tables`] bidirectional check to verify the
///    obligation.
/// 5. Collect all verified relations into a conjunction forming the
///    [`ReturnSummary`].
///
/// # Example
///
/// For a function `find_max(array, n)` that returns the maximum element,
/// this synthesises the summary: `retval >= array[0] && retval >= array[1] && ...`
fn infer_cyclic_observer_summary(
    graph: &FunctionGraph,
    adapted: &AdaptedProcedure,
    oracle: &Oracle,
) -> Option<ReturnSummary> {
    if adapted.cfg.topological_order().is_some() || graph.pointer_param_indices.is_empty() {
        return None;
    }

    let retval_name = synthetic_retval_name(&adapted.name);
    let mut relations = Vec::new();
    for &param_index in &graph.pointer_param_indices {
        let indices = observer_candidate_indices(&adapted.cfg, &adapted.name, param_index);
        for index in indices {
            let obligation = Formula::ge(
                Term::Var(Var::int(retval_name.clone())),
                Term::select(
                    Memory::var(ext_region_name(&adapted.name, param_index)),
                    Term::int(index),
                ),
            );
            let Some(site) = synthetic_exit_assertion(&adapted.cfg, obligation.clone()) else {
                continue;
            };
            let Some(invariants) = observer_summary_invariants(&adapted.cfg, &site, oracle, index)
            else {
                continue;
            };
            let result = analyze_with_tables(
                &adapted.cfg,
                &adapted.name,
                &site,
                oracle,
                &SummaryTables::new(),
                None,
                Some(&invariants),
            )
            .ok()?;
            if matches!(result.judgement, Judgement::Verified) {
                relations.push(obligation);
            }
        }
    }

    if relations.is_empty() {
        return None;
    }

    Some(ReturnSummary {
        function: adapted.name.clone(),
        formal_parameters: graph
            .params
            .iter()
            .map(|param| format!("{}${param}", adapted.name))
            .collect(),
        retval_name,
        relation: Formula::and_all(relations),
        write_effects: Vec::new(),
    })
}

fn synthetic_exit_assertion(cfg: &AbstractCfg, obligation: Formula) -> Option<AssertionSite> {
    Some(AssertionSite {
        id: 0,
        node: cfg.exit()?,
        source_location: SourceLocation::default(),
        location: "summary exit".to_string(),
        obligation,
    })
}

fn observer_candidate_indices(cfg: &AbstractCfg, function: &str, param_index: usize) -> Vec<i64> {
    let ext_region = ext_region_name(function, param_index);
    let mut indices = BTreeSet::new();
    let mut saw_dynamic = false;
    let mut max_nonnegative_constant = 0i64;

    for node in cfg.nodes().values() {
        for effect in &node.transfer.effects {
            collect_observer_indices_effect(
                effect,
                &ext_region,
                &mut indices,
                &mut saw_dynamic,
                &mut max_nonnegative_constant,
            );
        }
    }
    for edge in cfg.edges().values() {
        collect_observer_indices_formula(
            &edge.guard,
            &ext_region,
            &mut indices,
            &mut saw_dynamic,
            &mut max_nonnegative_constant,
        );
    }

    if saw_dynamic {
        for index in 0..=max_nonnegative_constant {
            indices.insert(index);
        }
    }
    indices.into_iter().collect()
}

/// Collect array access indices from a transfer effect.
///
/// Extracts constant indices from `select` operations on the given `ext_region`;
/// when dynamic indices are encountered, records that and marks up to the
/// maximum non-negative constant as accessed.
fn collect_observer_indices_effect(
    effect: &crate::common::abstract_cfg::TransferEffect,
    ext_region: &str,
    indices: &mut BTreeSet<i64>,
    saw_dynamic: &mut bool,
    max_nonnegative_constant: &mut i64,
) {
    use crate::common::abstract_cfg::{AssignValue, TransferEffect};

    match effect {
        TransferEffect::Assign { value, .. } => match value {
            AssignValue::Term(term) => collect_observer_indices_term(
                term,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            ),
            AssignValue::Predicate(formula) => collect_observer_indices_formula(
                formula,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            ),
        },
        TransferEffect::Assume(formula) | TransferEffect::Obligation(formula) => {
            collect_observer_indices_formula(
                formula,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        TransferEffect::Store { value, .. } | TransferEffect::MemoryStore { value, .. } => {
            collect_observer_indices_term(
                value,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        TransferEffect::GetElementPtr { offset, .. } => collect_observer_indices_term(
            offset,
            ext_region,
            indices,
            saw_dynamic,
            max_nonnegative_constant,
        ),
        _ => {}
    }
}

fn collect_observer_indices_formula(
    formula: &Formula,
    ext_region: &str,
    indices: &mut BTreeSet<i64>,
    saw_dynamic: &mut bool,
    max_nonnegative_constant: &mut i64,
) {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => {}
        Formula::Not(inner) => collect_observer_indices_formula(
            inner,
            ext_region,
            indices,
            saw_dynamic,
            max_nonnegative_constant,
        ),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_observer_indices_formula(
                    item,
                    ext_region,
                    indices,
                    saw_dynamic,
                    max_nonnegative_constant,
                );
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_observer_indices_formula(
                lhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_formula(
                rhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_observer_indices_term(
                lhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_term(
                rhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        Formula::MemoryEq(lhs, rhs) => {
            collect_observer_indices_memory(
                lhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_memory(
                rhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
    }
}

fn collect_observer_indices_term(
    term: &Term,
    ext_region: &str,
    indices: &mut BTreeSet<i64>,
    saw_dynamic: &mut bool,
    max_nonnegative_constant: &mut i64,
) {
    match term {
        Term::Var(_) => {}
        Term::Int(value) => {
            if *value >= 0 {
                *max_nonnegative_constant = (*max_nonnegative_constant).max(*value);
            }
        }
        Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_observer_indices_formula(
            inner,
            ext_region,
            indices,
            saw_dynamic,
            max_nonnegative_constant,
        ),
        Term::Select(memory, index) => {
            collect_observer_indices_memory(
                memory,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            if matches!(memory.as_ref(), Memory::Var(name) if name == ext_region) {
                if let Some(constant) = const_int_value(index) {
                    indices.insert(constant);
                } else {
                    *saw_dynamic = true;
                }
            }
            collect_observer_indices_term(
                index,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        Term::Add(lhs, rhs)
        | Term::Sub(lhs, rhs)
        | Term::Mul(lhs, rhs)
        | Term::Div(lhs, rhs)
        | Term::Rem(lhs, rhs) => {
            collect_observer_indices_term(
                lhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_term(
                rhs,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
        Term::Neg(inner) => collect_observer_indices_term(
            inner,
            ext_region,
            indices,
            saw_dynamic,
            max_nonnegative_constant,
        ),
    }
}

fn collect_observer_indices_memory(
    memory: &Memory,
    ext_region: &str,
    indices: &mut BTreeSet<i64>,
    saw_dynamic: &mut bool,
    max_nonnegative_constant: &mut i64,
) {
    match memory {
        Memory::Var(_) => {}
        Memory::Store(inner, index, value) => {
            collect_observer_indices_memory(
                inner,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_term(
                index,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
            collect_observer_indices_term(
                value,
                ext_region,
                indices,
                saw_dynamic,
                max_nonnegative_constant,
            );
        }
    }
}

fn const_int_value(term: &Term) -> Option<i64> {
    match term {
        Term::Int(value) => Some(*value),
        Term::Add(lhs, rhs) => Some(const_int_value(lhs)? + const_int_value(rhs)?),
        Term::Sub(lhs, rhs) => Some(const_int_value(lhs)? - const_int_value(rhs)?),
        Term::Neg(inner) => Some(-const_int_value(inner)?),
        _ => None,
    }
}

/// Synthesise loop invariants needed to discharge an observer-pattern obligation.
///
/// For each detected loop the function examines the preliminary backward state
/// at the header (the state propagated backward from the synthetic exit
/// assertion with back edges cut).  It expects the header state to contain a
/// conjunct of the form `counter >= exit_value` (exit condition) and a
/// comparison `accumulator < observed_value` (the potential violation), and
/// constructs the disjunctive invariant:
///
/// ```text
/// counter <= observed_index  OR  accumulator >= observed_value
/// ```
///
/// The invariant is checked for initiation and inductiveness via
/// [`check_loop_invariant_verbose`] with `assertion_postconditions` set to
/// `&BTreeMap::new()` — the exit-closure check is **intentionally skipped**
/// here.  The rationale: this invariant only needs to be inductive; the actual
/// obligation (`retval >= array[observed_index]`) is verified by the
/// [`analyze_with_tables`] call in [`infer_cyclic_observer_summary`], which is
/// the authoritative discharge step.
///
/// # Design note
///
/// Exit closure is skipped here because the final proof is delegated to
/// [`analyze_with_tables`] with the full assertion context.  This avoids
/// building a separate exit-closure check that may differ from the authoritative
/// verification in [`analyze_with_tables`].
fn observer_summary_invariants(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    observed_index: i64,
) -> Option<Vec<(CfgNodeId, Formula)>> {
    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();
    let assertion_postconditions = preliminary_backward_states(cfg, site, &excluded).ok()?;
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let mut accepted = Vec::new();

    for loop_info in loops {
        let header_state = assertion_postconditions.get(&loop_info.header)?;
        let Some((counter, accumulator, observed)) = extract_counter_acc_obs(header_state) else {
            return None;
        };
        let candidate = Formula::or(
            Formula::le(counter, Term::int(observed_index)),
            Formula::ge(accumulator, observed),
        );
        // Skip exit closure check: the invariant only needs to be inductive here.
        // The actual obligation is verified by the analyze_with_tables call in
        // infer_cyclic_observer_summary, which is the authoritative check.
        let result = check_loop_invariant_verbose(
            &loop_info,
            cfg,
            &candidate,
            oracle,
            &BTreeMap::new(),
            &accepted,
        );
        if result != InvariantCheckResult::Accepted {
            return None;
        }
        accepted.push((
            loop_info.header,
            normalize_candidate(cfg, loop_info.header, &candidate),
        ));
    }
    Some(accepted)
}

fn preliminary_backward_states(
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

fn loop_counter_term(cfg: &AbstractCfg, loop_info: &LoopInfo) -> Option<Term> {
    for edge_id in cfg.outgoing_edges(loop_info.header) {
        let edge = cfg.edge(edge_id).ok()?;
        if loop_info.body.contains(&edge.target) {
            if let Some(counter) = counter_term_from_guard(&edge.guard) {
                return Some(counter);
            }
        }
    }
    counter_term_from_guard(&loop_info.back_edge_guard)
}

fn counter_term_from_guard(guard: &Formula) -> Option<Term> {
    match guard {
        Formula::Lt(lhs, _) | Formula::Le(lhs, _) => Some(lhs.clone()),
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Ge(lhs, _) | Formula::Gt(lhs, _) => Some(lhs.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn summary_accumulator_term(cfg: &AbstractCfg, site: &AssertionSite) -> Option<Term> {
    let pre = cfg
        .node(site.node)
        .ok()?
        .transfer
        .wp(&Formula::not(site.obligation.clone()));
    match pre {
        Formula::Not(inner) => match *inner {
            Formula::Ge(lhs, _) => Some(lhs),
            Formula::Le(_, rhs) => Some(rhs),
            _ => None,
        },
        _ => None,
    }
}

fn summary_observed_term(cfg: &AbstractCfg, site: &AssertionSite) -> Option<Term> {
    let pre = cfg
        .node(site.node)
        .ok()?
        .transfer
        .wp(&Formula::not(site.obligation.clone()));
    match pre {
        Formula::Not(inner) => match *inner {
            Formula::Ge(_, rhs) => Some(rhs),
            Formula::Le(lhs, _) => Some(lhs),
            _ => None,
        },
        _ => None,
    }
}

/// Extract `(counter_term, accumulator_term, observed_term)` from a header
/// backward state formula.
///
/// The formula is expected to be a conjunction containing:
/// - One conjunct matching [`extract_exit_counter`] — the loop exit condition
///   (e.g. `i >= n`).
/// - One conjunct matching [`extract_lt_pair`] — the potential violation
///   (e.g. `acc < array[i]`).
///
/// Returns `None` if either component is missing.
///
/// # Purpose
///
/// Used by [`observer_summary_invariants`] to decompose the backward state
/// into components for building the observer-pattern invariant.
fn extract_counter_acc_obs(formula: &Formula) -> Option<(Term, Term, Term)> {
    let conjuncts: Vec<&Formula> = match formula {
        Formula::And(items) => items.iter().collect(),
        other => vec![other],
    };
    let mut counter = None;
    let mut acc_obs = None;
    for conjunct in &conjuncts {
        if counter.is_none() {
            if let Some(t) = extract_exit_counter(conjunct) {
                counter = Some(t);
                continue;
            }
        }
        if acc_obs.is_none() {
            if let Some(pair) = extract_lt_pair(conjunct) {
                acc_obs = Some(pair);
            }
        }
    }
    let counter = counter?;
    let (acc, obs) = acc_obs?;
    Some((counter, acc, obs))
}

/// Extract the left-hand side of a loop exit condition of the form
/// `lhs >= rhs`, `lhs > rhs`, `NOT (lhs < rhs)`, or `NOT (lhs <= rhs)`.
///
/// This is used by [`extract_counter_acc_obs`] to identify the counter
/// variable after the loop has terminated.
///
/// # Examples
///
/// - `i >= n` → `Some(i)`
/// - `NOT (i < n)` → `Some(i)`
/// - `i < n` → `None` (not an exit condition)
fn extract_exit_counter(formula: &Formula) -> Option<Term> {
    match formula {
        Formula::Ge(lhs, _) | Formula::Gt(lhs, _) => Some(lhs.clone()),
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Lt(lhs, _) | Formula::Le(lhs, _) => Some(lhs.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Extract `(lhs, rhs)` from a formula expressing `lhs < rhs`, `lhs <= rhs`,
/// `NOT (lhs >= rhs)`, or `NOT (lhs > rhs)`.
///
/// Used by [`extract_counter_acc_obs`] to identify the accumulator and the
/// observed value (array element) in the violation condition.
///
/// # Examples
///
/// - `acc < array[i]` → `Some((acc, array[i]))`
/// - `NOT (acc >= array[i])` → `Some((acc, array[i]))`
/// - `acc >= array[i]` → `None`
fn extract_lt_pair(formula: &Formula) -> Option<(Term, Term)> {
    match formula {
        Formula::Lt(lhs, rhs) | Formula::Le(lhs, rhs) => Some((lhs.clone(), rhs.clone())),
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Ge(lhs, rhs) | Formula::Gt(lhs, rhs) => Some((lhs.clone(), rhs.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// Compute the set of functions that are (mutually) recursive.
///
/// A function is considered recursive if it can reach itself through the
/// intra-module call graph (direct or indirect).  The result is used to tag
/// [`ProcedureReport::recursive`] and may be used in the future to skip or
/// specialise summary inference for recursive callees.
///
/// # Algorithm
///
/// Build the call graph from all `FunctionGraph` vertices, then test each
/// function for reachability to itself via depth-first search.
fn recursive_functions(graphs: &[FunctionGraph]) -> BTreeSet<String> {
    let in_graph = graphs
        .iter()
        .map(|graph| graph.name.clone())
        .collect::<BTreeSet<_>>();
    let mut calls = BTreeMap::<String, BTreeSet<String>>::new();
    for graph in graphs {
        let callees = graph
            .vertices
            .iter()
            .filter_map(|instruction| instruction.get_called_function())
            .filter(|callee| callee != "may_assert" && in_graph.contains(callee))
            .collect::<BTreeSet<_>>();
        calls.insert(graph.name.clone(), callees);
    }
    let mut recursive = BTreeSet::new();
    for name in &in_graph {
        if reaches(name, name, &calls, &mut BTreeSet::new()) {
            recursive.insert(name.clone());
        }
    }
    recursive
}

fn reaches(
    start: &str,
    target: &str,
    calls: &BTreeMap<String, BTreeSet<String>>,
    seen: &mut BTreeSet<String>,
) -> bool {
    let Some(callees) = calls.get(start) else {
        return false;
    };
    for callee in callees {
        if callee == target {
            return true;
        }
        if seen.insert(callee.clone()) && reaches(callee, target, calls, seen) {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::adapter::ReturnSummary;
    use crate::common::formula::{Formula, Term, Var};
    use crate::common::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::common::llvm_utils::program_graph::generate_program_graph;
    use crate::may_must_analysis::providers::ManualProvider;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    fn with_graphs(ir: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
    }

    fn compile_fixture(stem: &str) -> PathBuf {
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let source = {
            let direct = repo_root.join("tests").join(format!("{stem}.c"));
            if direct.exists() {
                direct
            } else {
                repo_root.join("tests/flow").join(format!("{stem}.c"))
            }
        };
        let status = Command::new("sh")
            .arg("tests/build_ir.sh")
            .arg(&source)
            .current_dir(repo_root)
            .status()
            .expect("run tests/build_ir.sh");
        assert!(
            status.success(),
            "failed to compile fixture {}",
            source.display()
        );
        repo_root.join("tests/out").join(format!("{stem}.bc"))
    }

    fn with_bc_graphs(stem: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let fixture = compile_fixture(stem);
        let context = Context::new();
        let module = context
            .parse_bc_file(fixture.to_str().expect("fixture path utf-8"))
            .unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
    }

    fn procedure<'a>(report: &'a ModuleReport, name: &str) -> &'a ProcedureReport {
        report
            .reports
            .iter()
            .find(|procedure| procedure.procedure == name)
            .unwrap_or_else(|| panic!("missing procedure report for {name}"))
    }

    fn assert_all_verified(report: &ProcedureReport, expected_assertions: usize) {
        assert_eq!(report.assertions.len(), expected_assertions);
        assert_eq!(report.verdict(), SafetyVerdict::Safe);
        assert!(report.failures.is_empty());
        assert!(report
            .assertions
            .iter()
            .all(|assertion| matches!(assertion.judgement, Judgement::Verified)));
    }

    #[test]
    fn straight_line_assertion_is_safe() {
        with_graphs(
            r#"
                declare void @may_assert(i1)
                define i32 @main(i32 %x) {
                entry:
                    %c = icmp eq i32 %x, %x
                    call void @may_assert(i1 %c)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn assume_discharges_same_condition() {
        // assume(x > 0) followed by assert(x > 0): the assume constrains the
        // entry state so the assertion is trivially verified.
        with_graphs(
            r#"
                declare void @may_assert(i1)
                declare void @may_assume(i1)
                define i32 @main(i32 %x) {
                entry:
                    %pos = icmp sgt i32 %x, 0
                    call void @may_assume(i1 %pos)
                    call void @may_assert(i1 %pos)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn assume_without_assertion_is_safe() {
        // A function with only an assume and no assertion should trivially be safe.
        with_graphs(
            r#"
                declare void @may_assume(i1)
                define i32 @main(i32 %x) {
                entry:
                    %pos = icmp sgt i32 %x, 0
                    call void @may_assume(i1 %pos)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn assume_does_not_discharge_stronger_assertion() {
        // assume(x > 0) does NOT discharge assert(x > 1): still unsafe.
        with_graphs(
            r#"
                declare void @may_assert(i1)
                declare void @may_assume(i1)
                define i32 @main(i32 %x) {
                entry:
                    %pos  = icmp sgt i32 %x, 0
                    %pos2 = icmp sgt i32 %x, 1
                    call void @may_assume(i1 %pos)
                    call void @may_assert(i1 %pos2)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Unsafe);
            },
        );
    }

    #[test]
    fn unconstrained_assertion_is_unsafe() {
        with_graphs(
            r#"
                declare void @may_assert(i1)
                define i32 @main(i32 %x) {
                entry:
                    %c = icmp eq i32 %x, 0
                    call void @may_assert(i1 %c)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Unsafe);
            },
        );
    }

    #[test]
    fn callee_summary_can_prove_callsite_safe() {
        with_graphs(
            r#"
                declare i32 @inc(i32)
                declare void @may_assert(i1)
                define i32 @main(i32 %x) {
                entry:
                    %v = call i32 @inc(i32 %x)
                    %ok = icmp sgt i32 %v, %x
                    call void @may_assert(i1 %ok)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let mut summaries = CallSummaryRegistry::new();
                summaries.insert(ReturnSummary {
                    function: "inc".to_string(),
                    formal_parameters: vec!["inc$%x".to_string()],
                    retval_name: "inc$__retval".to_string(),
                    relation: Formula::eq(
                        Term::Var(Var::int("inc$__retval")),
                        Term::add(Term::Var(Var::int("inc$%x")), Term::int(1)),
                    ),
                    write_effects: Vec::new(),
                });
                let report = super::analyze_with_summaries(
                    &graphs[0],
                    &BTreeSet::new(),
                    &summaries,
                    &oracle,
                    None,
                    None,
                )
                .unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn float_local_store_and_load_do_not_block_integer_assertions() {
        with_graphs(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %average = alloca float
                    %sumf = sitofp i32 6 to float
                    %lenf = sitofp i32 2 to float
                    %div = fdiv float %sumf, %lenf
                    store float %div, ptr %average
                    %loaded = load float, ptr %average
                    %ok = icmp eq i32 1, 1
                    call void @may_assert(i1 %ok)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_function_graph(&graphs[0], &oracle).unwrap();
                assert_eq!(report.verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn extern_summary_via_provider_is_used() {
        with_graphs(
            r#"
                declare i32 @inc(i32)
                declare void @may_assert(i1)
                define i32 @main(i32 %x) {
                entry:
                    %v = call i32 @inc(i32 %x)
                    %ok = icmp sgt i32 %v, %x
                    call void @may_assert(i1 %ok)
                    ret i32 0
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let summary = ReturnSummary {
                    function: "inc".to_string(),
                    formal_parameters: vec!["inc$%x".to_string()],
                    retval_name: "inc$__retval".to_string(),
                    relation: Formula::eq(
                        Term::Var(Var::int("inc$__retval")),
                        Term::add(Term::Var(Var::int("inc$%x")), Term::int(1)),
                    ),
                    write_effects: Vec::new(),
                };
                let provider = ManualProvider::new().with_function_summary(summary);
                let reports =
                    analyze_module_with_provider(graphs, &BTreeSet::new(), &provider, &oracle)
                        .unwrap();
                assert_eq!(reports.reports[0].verdict(), SafetyVerdict::Safe);
            },
        );
    }

    #[test]
    fn loop_counter_assertion_is_safe() {
        with_graphs(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %call = call i32 @subject(i32 4)
                    ret i32 %call
                }

                define internal i32 @subject(i32 %n) {
                entry:
                    %i = alloca i32
                    store i32 0, ptr %i
                    br label %header

                header:
                    %cur = load i32, ptr %i
                    %cond = icmp slt i32 %cur, %n
                    br i1 %cond, label %body, label %exit

                body:
                    %old = load i32, ptr %i
                    %next = add i32 %old, 1
                    store i32 %next, ptr %i
                    br label %header

                exit:
                    %done = load i32, ptr %i
                    %ok = icmp sge i32 %done, 0
                    call void @may_assert(i1 %ok)
                    ret i32 %done
                }
            "#,
            |graphs| {
                let oracle = Oracle::new();
                let report = analyze_module(graphs, &BTreeSet::new(), &oracle).unwrap();
                let subject = report
                    .reports
                    .iter()
                    .find(|procedure| procedure.procedure == "subject")
                    .expect("subject procedure report");
                assert_eq!(subject.verdict(), SafetyVerdict::Safe);
                assert!(report
                    .summaries
                    .get_loop_invariants("subject")
                    .iter()
                    .any(|(_, invariant)| invariant.to_string().contains(">= 0")));
            },
        );
    }

    #[test]
    fn array_max_callee_verified_with_return_summary() {
        with_bc_graphs("array_max_callee", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "main"), 5);
            assert!(report
                .computed_summaries
                .iter()
                .any(|summary| summary.function == "find_max"));
        });
    }

    #[test]
    fn global_int_store_then_assert_verified() {
        with_bc_graphs("global_int", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "test"), 1);
        });
    }

    #[test]
    fn array_init_verified_after_memcpy_modeling() {
        with_bc_graphs("array_init", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "main"), 3);
        });
    }

    #[test]
    fn array_max_offset_verified_with_nonzero_base_offset() {
        with_bc_graphs("array_max_offset", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "main"), 3);
        });
    }

    #[test]
    fn struct_fields_verified_with_per_field_regions() {
        with_bc_graphs("struct_fields", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            // 3 assertions: p.x == 3, p.y == 7, p.x + p.y == 10
            assert_all_verified(procedure(&report, "main"), 3);
        });
    }

    #[test]
    fn array_max_5_verified_with_cyclic_callee_summary() {
        with_bc_graphs("array_max_5", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "main"), 5);
            assert!(report
                .computed_summaries
                .iter()
                .any(|summary| summary.function == "max_of_5"));
        });
    }

    #[test]
    fn ptrtoint_distinct_stack_addrs_verified() {
        // Two distinct stack allocas must get distinct flat addresses.
        // ptrtoint of each produces a concrete integer; the assertion
        // addr_a != addr_b is trivially true under the flat layout model.
        with_bc_graphs("ptrtoint_compare", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "test_distinct_stack_addrs"), 1);
        });
    }
}
