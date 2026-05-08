#![allow(dead_code)]

use crate::analysis::adapter::{
    adapt, adapt_with_purity_and_summaries, collect_callee_names, compute_return_summary,
    AdapterError, CallSummaryRegistry,
};
use crate::analysis::backward::{analyze, render_result, AssertionResult, BackwardError};
use crate::analysis::oracle::Oracle;
use crate::analysis::providers::{CandidateProvider, NoProvider};
use crate::analysis::rules::Judgement;
use crate::llvm_utils::program_graph::FunctionGraph;
use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Debug)]
pub struct ProcedureReport {
    pub procedure: String,
    pub assertions: Vec<AssertionResult>,
    pub failures: Vec<String>,
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

pub fn analyze_function_graph(
    graph: &FunctionGraph,
    oracle: &Oracle,
) -> Result<ProcedureReport, DriverError> {
    analyze_with_summaries(graph, &BTreeSet::new(), &CallSummaryRegistry::new(), oracle)
}

pub fn analyze_module(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<Vec<ProcedureReport>, DriverError> {
    analyze_module_with_provider(graphs, memory_pure, &NoProvider, oracle)
}

pub fn analyze_module_with_provider(
    graphs: &[FunctionGraph],
    memory_pure: &BTreeSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
) -> Result<Vec<ProcedureReport>, DriverError> {
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
            let adapted = adapt_with_purity_and_summaries(graph, memory_pure, &snapshot)?;
            if let Some(summary) = compute_return_summary(graph, &adapted) {
                summaries.insert(summary);
            }
        }
    }

    let mut reports = Vec::new();
    for graph in graphs {
        reports.push(analyze_with_summaries(
            graph,
            memory_pure,
            &summaries,
            oracle,
        )?);
    }
    Ok(reports)
}

pub fn analyze_function_graph_with_purity(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    oracle: &Oracle,
) -> Result<ProcedureReport, DriverError> {
    analyze_with_summaries(graph, memory_pure, &CallSummaryRegistry::new(), oracle)
}

fn analyze_with_summaries(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    summaries: &CallSummaryRegistry,
    oracle: &Oracle,
) -> Result<ProcedureReport, DriverError> {
    let adapted = if summaries.is_empty() && memory_pure.is_empty() {
        adapt(graph)?
    } else {
        adapt_with_purity_and_summaries(graph, memory_pure, summaries)?
    };

    let mut assertions = Vec::new();
    let mut failures = Vec::new();
    for site in &adapted.assertions {
        match analyze(&adapted.cfg, site, oracle) {
            Ok(result) => assertions.push(result),
            Err(BackwardError::CyclicCfgUnsupported) => failures.push(format!(
                "assertion #{} ({}): CFG has a cycle; loops are not supported",
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
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::adapter::ReturnSummary;
    use crate::analysis::formula::{Formula, Term, Var};
    use crate::analysis::providers::ManualProvider;
    use crate::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::llvm_utils::program_graph::generate_program_graph;

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
                });
                let report = super::analyze_with_summaries(
                    &graphs[0],
                    &BTreeSet::new(),
                    &summaries,
                    &oracle,
                )
                .unwrap();
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
                };
                let provider = ManualProvider::new().with_function_summary(summary);
                let reports =
                    analyze_module_with_provider(graphs, &BTreeSet::new(), &provider, &oracle)
                        .unwrap();
                assert_eq!(reports[0].verdict(), SafetyVerdict::Safe);
            },
        );
    }
}
