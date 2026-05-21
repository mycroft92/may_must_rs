//! Module-level orchestration of the may/must analysis.
//!
//! # Responsibilities
//!
//! 1. **Return-summary inference** — for each function a [`ReturnSummary`]
//!    relating the return value to formal parameters is computed.  Acyclic
//!    functions use `compute_return_summary`; looping functions that observe an
//!    array argument use the *observer pattern* ([`infer_cyclic_observer_summary`]).
//!
//! 2. **Per-function verification** — [`analyze_with_summaries`] lowers a
//!    [`FunctionGraph`] via the adapter and enqueues one assertion query per
//!    [`AssertionSite`] into the [`Scheduler`].
//!
//! 3. **Recursion detection** — [`recursive_functions`] identifies mutually
//!    recursive functions so their [`ProcedureReport`] can be flagged.
//!
//! # Observer pattern for cyclic callees
//!
//! When a looping callee reads an array parameter and returns a summary value
//! (e.g. maximum or sum), [`infer_cyclic_observer_summary`] synthesises an
//! invariant by examining which array indices the function accesses, then
//! verifying a candidate relation `retval >= array[i]` via the full
//! bidirectional check (ACHAR synthesises the required loop invariant).
use crate::common::abstract_cfg::{AbstractCfg, SourceLocation};
use crate::common::adapter::{
    adapt, adapt_with_purity_and_summaries, collect_callee_names, compute_return_summary,
    ext_region_name, extract_ptr_writes, ptr_write_summary_if_any, synthetic_retval_name,
    AdaptedProcedure, AdapterError, AssertionSite, CallSummaryRegistry, ReturnSummary,
};
use crate::common::alias_analysis::run_alias_analysis;
use crate::common::formula::{Formula, Memory, Term, Var};
use crate::common::llvm_utils::program_graph::FunctionGraph;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::{
    analyze_with_tables, render_result, AssertionResult, InvariantConfig,
};
use crate::may_must_analysis::providers::{CandidateProvider, NoProvider};
use crate::may_must_analysis::rules::Judgement;
use crate::may_must_analysis::scheduler;
use crate::may_must_analysis::smash;
use crate::may_must_analysis::summaries::{MaySummary, NotMaySummary, SummaryTables};
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
/// Convenience wrapper with a default [`InvariantConfig`] and no external
/// candidate provider.
pub fn analyze_module(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<ModuleReport, DriverError> {
    analyze_module_with_provider(
        graphs,
        memory_pure,
        &NoProvider,
        oracle,
        &InvariantConfig::default(),
    )
}

/// Analyse every function in an LLVM module, using `provider` for external
/// summaries, and return a [`ModuleReport`].
pub fn analyze_module_with_provider(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
    inv_config: &InvariantConfig,
) -> Result<ModuleReport, DriverError> {
    let alias = run_alias_analysis(graphs);
    let mut summaries = CallSummaryRegistry::new();

    for graph in graphs {
        summaries.scan_graph_vtables(graph);
    }

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

    // Build summary_tables from inferred return summaries.
    let mut summary_tables = SummaryTables::new();
    for summary in summaries.summaries().values() {
        summary_tables.add_forward_may(
            summary.function.clone(),
            MaySummary {
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

    // Step 6B: one module-wide scheduler, pre-loaded with summary_tables.
    // As each procedure's queries are drained, their contextual summaries
    // accumulate in sched.table and become visible to later procedures via
    // legacy_tables_for_dispatch (initial_tables ⊕ sched.table).
    let mut sched = scheduler::Scheduler::with_initial_tables(summary_tables.clone());

    // Track query IDs per procedure for result collection.
    let mut proc_query_ids: BTreeMap<String, Vec<crate::may_must_analysis::query::QueryId>> =
        BTreeMap::new();
    // Collect adaptation errors and size-limit skips.
    let mut proc_failures: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Metrics per procedure.
    let mut proc_loop_counts: BTreeMap<String, usize> = BTreeMap::new();

    for graph in graphs {
        // Size guard.
        let max_size = inv_config.max_function_size;
        if max_size > 0 && graph.vertices.len() > max_size {
            proc_failures
                .entry(graph.name.clone())
                .or_default()
                .push(format!(
                    "function too large ({} instructions > limit {}): skipped",
                    graph.vertices.len(),
                    max_size
                ));
            continue;
        }

        let adapted = match adapt_with_purity_and_summaries(graph, memory_pure, &summaries, &alias)
        {
            Ok(a) => a,
            Err(e) => {
                proc_failures
                    .entry(graph.name.clone())
                    .or_default()
                    .push(e.to_string());
                continue;
            }
        };

        proc_loop_counts.insert(adapted.name.clone(), adapted.cfg.detect_back_edges().len());

        let interface = crate::may_must_analysis::query::ProcedureInterface::new(
            adapted.name.clone(),
            adapted.formal_parameters.iter().cloned(),
        );
        sched.register_procedure(scheduler::ProcedureContext {
            cfg: adapted.cfg.clone(),
            assertions: adapted.assertions.clone(),
            debug_names: adapted.debug_names.clone(),
            interface,
        });

        let mut ids = Vec::new();
        for site in &adapted.assertions {
            let neg_obligation = Formula::not(site.obligation.clone());
            let pre_at_assertion = match adapted.cfg.node(site.node) {
                Ok(node) => node.transfer.wp(&neg_obligation),
                Err(_) => neg_obligation.clone(),
            };
            let query = crate::may_must_analysis::query::Query::new(
                adapted.name.clone(),
                Formula::True,
                pre_at_assertion,
            );
            let provenance = scheduler::AssertionProvenance { site: site.clone() };
            ids.push(sched.enqueue(query, Some(provenance)));
        }
        proc_query_ids.insert(adapted.name.clone(), ids);
    }

    // Drain once — earlier procedures' contextual summaries feed later ones.
    sched.drain(oracle, Some(inv_config));

    // Reconstruct per-procedure reports from completed outcomes.
    let mut reports = Vec::new();
    for graph in graphs {
        if let Some(failures) = proc_failures.remove(&graph.name) {
            reports.push(ProcedureReport {
                procedure: graph.name.clone(),
                assertions: Vec::new(),
                failures,
                loop_count: 0,
                instruction_count: graph.vertices.len(),
                recursive: recursive.contains(&graph.name),
            });
            continue;
        }

        let ids = proc_query_ids.get(&graph.name).cloned().unwrap_or_default();
        let mut assertions = Vec::new();
        for id in &ids {
            if let Some(scheduler::DispatchOutcome::Completed(run)) = sched.completed_outcome(*id) {
                assertions.push(run.assertion.clone());
            }
        }

        reports.push(ProcedureReport {
            procedure: graph.name.clone(),
            assertions,
            failures: Vec::new(),
            loop_count: proc_loop_counts.get(&graph.name).copied().unwrap_or(0),
            instruction_count: graph.vertices.len(),
            recursive: recursive.contains(&graph.name),
        });
    }

    // Merge contextual summaries back so the ModuleReport carries the
    // full picture (initial return summaries + contextual discoveries).
    summary_tables.extend_from(&sched.table);

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
/// The function runs [`run_alias_analysis`] on `graph` alone before lowering.
/// When called from the full module analysis the per-function AA is a subset
/// of the module-wide one; it is still sound (flow-insensitive AA over a
/// subset of the IR is an over-approximation of the same constraints).
///
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
    let legacy_tables_for_scheduler: SummaryTables = tables.cloned().unwrap_or_default();
    let mut sched = scheduler::Scheduler::with_initial_tables(legacy_tables_for_scheduler);
    let interface = crate::may_must_analysis::query::ProcedureInterface::new(
        adapted.name.clone(),
        adapted.formal_parameters.iter().cloned(),
    );
    sched.register_procedure(scheduler::ProcedureContext {
        cfg: adapted.cfg.clone(),
        assertions: adapted.assertions.clone(),
        debug_names: adapted.debug_names.clone(),
        interface,
    });
    for site in &adapted.assertions {
        let neg_obligation = Formula::not(site.obligation.clone());
        let pre_at_assertion = match adapted.cfg.node(site.node) {
            Ok(node) => node.transfer.wp(&neg_obligation),
            Err(_) => neg_obligation.clone(),
        };
        let query = crate::may_must_analysis::query::Query::new(
            adapted.name.clone(),
            Formula::True,
            pre_at_assertion,
        );
        let provenance = scheduler::AssertionProvenance { site: site.clone() };
        sched.enqueue(query, Some(provenance));
    }
    let outcomes = sched.drain(oracle, config);
    let site_results: Vec<smash::SmashRunResult> = outcomes
        .into_iter()
        .filter_map(|o| match o {
            scheduler::DispatchOutcome::Completed(run) => Some(run),
            scheduler::DispatchOutcome::Unprovenanced => None,
        })
        .collect();

    let mut assertions = Vec::new();
    let failures: Vec<String> = Vec::new();
    for run in site_results {
        assertions.push(run.assertion);
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
    let ptr_writes = extract_ptr_writes(graph, &adapted.name, &adapted.ptr_at);

    let base = compute_return_summary(graph, adapted)
        .or_else(|| infer_cyclic_observer_summary(graph, adapted, oracle))
        .or_else(|| {
            // For functions whose return value has no integer formula (e.g. constructors
            // returning void or an opaque pointer), still produce a summary if there are
            // pointer write effects to propagate (e.g. vptr stores).
            if ptr_writes.is_empty() {
                None
            } else {
                ptr_write_summary_if_any(graph, adapted)
            }
        });

    base.map(|mut s| {
        s.ptr_writes = ptr_writes;
        s
    })
}

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
            let result = analyze_with_tables(
                &adapted.cfg,
                &adapted.name,
                &site,
                oracle,
                &SummaryTables::new(),
                None,
                &adapted.debug_names,
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
        ptr_writes: Vec::new(),
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
            // Try C source first, then C++ (both in tests/ and tests/flow/).
            let candidates = [
                repo_root.join("tests").join(format!("{stem}.c")),
                repo_root.join("tests/flow").join(format!("{stem}.c")),
                repo_root.join("tests").join(format!("{stem}.cpp")),
                repo_root.join("tests/flow").join(format!("{stem}.cpp")),
            ];
            candidates
                .into_iter()
                .find(|p| p.exists())
                .unwrap_or_else(|| repo_root.join("tests").join(format!("{stem}.c")))
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
                    ptr_writes: Vec::new(),
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
                    ptr_writes: Vec::new(),
                };
                let provider = ManualProvider::new().with_function_summary(summary);
                let reports = analyze_module_with_provider(
                    graphs,
                    &BTreeSet::new(),
                    &provider,
                    &oracle,
                    &InvariantConfig::default(),
                )
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
    fn array_max_5_cyclic_callee_no_summary_dart_finds_spurious_bug() {
        // ACHAR cannot synthesize the array-indexed loop invariant needed for
        // max_of_5's return summary (requires `i <= k || current_max >= array[k]`).
        // Without a return summary, computed_max is unconstrained at the call site.
        // DART then finds a path where computed_max < values[k] — a false positive.
        with_bc_graphs("array_max_5", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            let main_report = procedure(&report, "main");
            assert_eq!(main_report.assertions.len(), 5);
            // Spurious Unsafe: no return summary → unconstrained retval → DART false positive.
            assert_eq!(main_report.verdict(), SafetyVerdict::Unsafe);
            assert!(!report
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

    #[test]
    fn vtable_dispatch_verifies() {
        // Full end-to-end virtual dispatch: new Counter(), store vptr in constructor,
        // load vptr in caller, resolve IndirectCall via ptr_at + vtable_fn_ptrs,
        // apply Counter::get's return summary, discharge may_assert(v == 42).
        //
        // The ptr_at map (pointer store-to-load forwarding) propagates the vptr write
        // from the C2 constructor through C1 to the caller, enabling the IndirectCall
        // to resolve to _ZNK7Counter3getEv and the assertion to be Verified.
        with_bc_graphs("vtable_dispatch", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let reports = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            let main_report = reports
                .reports
                .iter()
                .find(|r| r.procedure == "_Z20test_vtable_dispatchv")
                .expect("test_vtable_dispatch function not found in reports");
            assert_eq!(
                main_report.verdict(),
                SafetyVerdict::Safe,
                "vtable dispatch should be Verified but got {:?}",
                main_report.verdict()
            );
        });
    }

    #[test]
    fn reach_error_on_unreachable_branch_is_safe() {
        // reach_error() called only on the false branch of (x == x), which is
        // never taken.  The checker must prove the call site unreachable and
        // return Safe.
        with_graphs(
            r#"
                declare void @reach_error()

                define void @main(i32 %x) {
                entry:
                    %eq = icmp eq i32 %x, %x
                    br i1 %eq, label %ok, label %err
                err:
                    call void @reach_error()
                    ret void
                ok:
                    ret void
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
    fn reach_error_on_reachable_branch_is_unsafe() {
        // reach_error() is called on the false branch of (x == 0), which is
        // reachable for x != 0.  The checker must find a counterexample.
        with_graphs(
            r#"
                declare void @reach_error()

                define void @main(i32 %x) {
                entry:
                    %eq = icmp eq i32 %x, 0
                    br i1 %eq, label %ok, label %err
                err:
                    call void @reach_error()
                    ret void
                ok:
                    ret void
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
    fn array_1_verified() {
        // array-1: loop iterates `for (j=0; j<SIZE; j++)` with SIZE=1, writing
        // array[j]=nondet and tightening `menor = min(menor, array[j])`.  After
        // the loop, `array[0] >= menor` holds because `menor` is the running min.
        // ACHAR finds the invariant `((j==0)||(array[0]>=menor)) && (SIZE==1)`
        // via the `counter-assert-disj+imm` tier (Tier 2b): the conjoined
        // immutable preheader fact `SIZE==1` rules out the spurious SIZE=0
        // exit-closure case.
        with_bc_graphs("array-1", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            let proc = procedure(&report, "main");
            assert_eq!(
                proc.verdict(),
                SafetyVerdict::Safe,
                "array-1 must be Verified: array[0]>=menor is always safe"
            );
        });
    }

    #[test]
    fn array_2_is_unsafe_via_forward_must() {
        // **Litmus test for forward MUST + backward NOT-MAY interplay.**
        //
        // array-2 has assertion `array[0] > menor` (strict).  The body
        // forces `menor <= array[0]` (non-strict), so when
        // `menor_orig <= array[0]` the body sets `menor = array[0]` and
        // the assertion FAILS at iteration 1.
        //
        // Forward MUST (realized as bounded-unroll DART per
        // `design_notes/SMASH_FORWARD_MUST.md`) must find this concrete
        // bug.  Verdict: UNSAFE.
        //
        // Companion test: `array_1_verified` — backward NOT-MAY proves
        // the non-strict assertion safe via the ACHAR invariant
        // `((j==0)||(array[0]>=menor)) ∧ (SIZE==1)`.
        with_bc_graphs("array-2", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            let proc = procedure(&report, "main");
            assert_eq!(
                proc.verdict(),
                SafetyVerdict::Unsafe,
                "array-2 must be UNSAFE via forward MUST (DART-style bounded unroll)"
            );
        });
    }

    #[test]
    fn heap_distinct_malloc_sites_do_not_alias() {
        // Two calls to malloc in the same function must produce distinct abstract
        // regions so that a write through one pointer does not invalidate the
        // constraint on the other.  Without per-call-site heap regions, both
        // pointers would share one region and the store to *b would make the
        // assertion *a == 1 unprovable.
        with_bc_graphs("heap_distinct", |graphs| {
            let oracle = Oracle::new();
            let memory_pure = crate::common::adapter::infer_memory_pure_functions(graphs);
            let report = analyze_module(graphs, &memory_pure, &oracle).unwrap();
            assert_all_verified(procedure(&report, "heap_distinct"), 1);
        });
    }
}
