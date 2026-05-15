#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId, SourceLocation};
use crate::common::adapter::{
    adapt, adapt_with_purity_and_summaries, collect_callee_names, compute_return_summary,
    ext_region_name, synthetic_retval_name, AdaptedProcedure, AdapterError, AssertionSite,
    CallSummaryRegistry, ReturnSummary,
};
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

pub fn analyze_module(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<ModuleReport, DriverError> {
    analyze_module_with_provider(graphs, memory_pure, &NoProvider, oracle)
}

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

pub fn analyze_module_with_llm(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
    inv_config: &InvariantConfig,
) -> Result<ModuleReport, DriverError> {
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
            if let Ok(adapted) = adapt_with_purity_and_summaries(graph, memory_pure, &snapshot) {
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
            adapt_with_purity_and_summaries(graph, memory_pure, &summaries)
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

pub fn analyze_with_summaries(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    summaries: &CallSummaryRegistry,
    oracle: &Oracle,
    tables: Option<&SummaryTables>,
    config: Option<&InvariantConfig>,
) -> Result<ProcedureReport, DriverError> {
    let adapted = if summaries.is_empty() && memory_pure.is_empty() {
        adapt(graph)?
    } else {
        adapt_with_purity_and_summaries(graph, memory_pure, summaries)?
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
}
