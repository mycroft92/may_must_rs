#![allow(dead_code)]

use crate::common::adapter::{
    adapt, adapt_with_purity_and_summaries, collect_callee_names, compute_return_summary,
    AdapterError, CallSummaryRegistry, ReturnSummary,
};
use crate::common::llvm_utils::program_graph::FunctionGraph;
use crate::common::oracle::Oracle;
use crate::may_must_analysis::backward::{
    analyze, analyze_with_tables, discover_loop_invariants, render_result, AssertionResult,
    BackwardError, InvariantConfig,
};
use crate::may_must_analysis::providers::{CandidateProvider, NoProvider};
use crate::may_must_analysis::rules::Judgement;
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
                if let Some(summary) = compute_return_summary(graph, &adapted) {
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

    fn with_graphs(ir: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
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
}
