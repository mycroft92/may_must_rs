//! CLI entry point.
//!
//! The binary keeps orchestration here and leaves the core work to modules:
//! parse command-line assertions, parse LLVM bitcode through `llvm_wrap`, build
//! per-function graphs, always dump DOT debug graphs, then run the current
//! paper-shaped interprocedural driver.
//!
//! Paper correspondence:
//!
//! ```text
//! CLI / bitcode input -> choose query and procedure to analyze
//! run_analysis(...)   -> instantiate P, query Q, and the active driver
//! ```

mod errors;
mod llvm_utils;
use crate::analysis::call_projection::{
    normalize_projected_query_to_callee_boundary, project_call_query,
};
use crate::analysis::cfg::{EdgeKind, PaperEdge, PaperProcedure};
use crate::analysis::driver::{
    InterproceduralConfig, InterproceduralOracleProvider, IntraproceduralConfig,
    IntraproceduralResult, PaperDriver,
};
use crate::analysis::formula::Predicate;
use crate::analysis::llvm_adapter::{adapt_function_graph, AdaptedProcedure, LlvmEdgeRegistry};
use crate::analysis::oracle::SmtPredicateOracle;
use crate::analysis::summaries::ReachabilityQuery;
use crate::analysis::transfer::{
    assertion_site_predicate, assertion_violation_predicate, AssertionTargetMode,
    SmtLlvmTransitionOracle,
};
use crate::analysis::vocabulary::{EdgeId, ProcedureName};
use crate::llvm_utils::llvm_wrap::*;
use crate::llvm_utils::program_graph::FunctionGraph;
use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use log::*;
use std::collections::BTreeMap;
use std::path::Path;
mod expressions;

mod analysis;
mod smt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QueryStatus {
    Reachable,
    NotReached,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AssertionPathPredicates {
    site: EdgeId,
    site_post: Predicate,
    violation_post: Predicate,
}

fn handle(module: Module, input_file: &str, assertion: Option<String>, max_obligations: usize) {
    match llvm_utils::program_graph::generate_program_graph(&module) {
        Ok(graphs) => {
            if should_dump_graphs() {
                let graph_dir = graph_output_dir(input_file);
                debug!("Dumping DOT graphs to {graph_dir}");
                llvm_utils::program_graph::dump_graphs(&graphs, &graph_dir);
            } else {
                debug!("Skipping DOT graph dump because MAY_MUST_SKIP_DOT=1");
            }
            run_analysis(&graphs, assertion, max_obligations);
        }
        Err(err) => error!("{err}"),
    }
}

fn run_analysis(graphs: &[FunctionGraph], assertion: Option<String>, max_obligations: usize) {
    if assertion.is_some() {
        println!("The paper-style driver does not support --assert yet.");
        return;
    }

    if graphs.is_empty() {
        println!("No functions found.");
        return;
    }

    let predicates = SmtPredicateOracle;
    let mut adapted = BTreeMap::<ProcedureName, AdaptedProcedure>::new();
    for graph in graphs {
        debug!("Adapting graph {}", graph.name);
        let procedure_name = ProcedureName::new(graph.name.clone());
        match adapt_function_graph(graph) {
            Ok(adapted_procedure) => {
                adapted.insert(procedure_name, adapted_procedure);
                debug!("Adapted graph {}", graph.name);
            }
            Err(err) => {
                println!("Unable to adapt {}: {err}", graph.name);
            }
        }
    }
    if adapted.is_empty() {
        println!("No adaptable functions found.");
        return;
    }

    let procedures = adapted
        .iter()
        .map(|(name, adapted)| (name.clone(), adapted.procedure.clone()))
        .collect::<BTreeMap<_, _>>();
    let registries = adapted
        .iter()
        .map(|(name, adapted)| (name.clone(), adapted.registry.clone()))
        .collect::<BTreeMap<_, _>>();
    let parameters = graphs
        .iter()
        .map(|graph| (ProcedureName::new(graph.name.clone()), graph.params.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut executed_assertion_job = false;

    for graph in graphs {
        let procedure_name = ProcedureName::new(graph.name.clone());
        let Some(registry) = registries.get(&procedure_name) else {
            continue;
        };
        let path_predicates = assertion_path_predicates(registry);
        if path_predicates.is_empty() {
            debug!(
                "Skipping top-level query for {}: no embedded may_assert target",
                procedure_name
            );
            continue;
        }
        for site_predicates in path_predicates {
            executed_assertion_job = true;
            println!(
                "Assertion Site <{}:{}>",
                procedure_name, site_predicates.site
            );

            let site_query = ReachabilityQuery::new(
                procedure_name.clone(),
                Predicate::True,
                site_predicates.site_post.clone(),
            )
            .with_target_assertion(site_predicates.site);
            let site_status = run_query(
                &predicates,
                &procedures,
                &registries,
                &parameters,
                &site_query,
                max_obligations,
                AssertionTargetMode::SiteReachability,
            );

            match site_status {
                QueryStatus::Unknown => {
                    println!("Verdict: UNKNOWN");
                    continue;
                }
                QueryStatus::NotReached => {
                    println!("Verdict: ASSERTION UNREACHABLE");
                    continue;
                }
                QueryStatus::Reachable => {}
            }

            let violation_query = ReachabilityQuery::new(
                procedure_name.clone(),
                Predicate::True,
                site_predicates.violation_post.clone(),
            )
            .with_target_assertion(site_predicates.site);
            let violation_status = run_query(
                &predicates,
                &procedures,
                &registries,
                &parameters,
                &violation_query,
                max_obligations,
                AssertionTargetMode::Violation,
            );
            match violation_status {
                QueryStatus::Reachable => println!("Verdict: ASSERTION VIOLATION REACHABLE"),
                QueryStatus::NotReached => println!("Verdict: ASSERTION TRUE WHEN REACHED"),
                QueryStatus::Unknown => println!("Verdict: UNKNOWN"),
            }
        }
    }

    if !executed_assertion_job {
        println!("No embedded may_assert targets found.");
    }
}

fn run_query(
    predicates: &SmtPredicateOracle,
    procedures: &BTreeMap<ProcedureName, PaperProcedure>,
    registries: &BTreeMap<ProcedureName, LlvmEdgeRegistry>,
    parameters: &BTreeMap<ProcedureName, Vec<String>>,
    query: &ReachabilityQuery,
    max_obligations: usize,
    assertion_target_mode: AssertionTargetMode,
) -> QueryStatus {
    let provider = LlvmInterproceduralProvider {
        procedures,
        registries,
        parameters,
        assertion_target_mode,
    };
    let mut driver = PaperDriver::new();
    let result = match driver.run_interprocedural(
        predicates,
        &provider,
        query,
        InterproceduralConfig {
            intraprocedural: IntraproceduralConfig { max_obligations },
            max_call_depth: 6,
        },
    ) {
        Ok(result) => result,
        Err(err) => {
            println!(
                "Query <{}: {} => {}>",
                query.procedure, query.pre, query.post
            );
            println!("Result: UNKNOWN");
            println!("Reason: {err}");
            return QueryStatus::Unknown;
        }
    };
    print_query_result(query, &result);
    debug_dump_summaries(&driver, procedures);
    query_status(&result)
}

fn print_query_result(query: &ReachabilityQuery, result: &IntraproceduralResult) {
    println!(
        "Query <{}: {} => {}>",
        query.procedure, query.pre, query.post
    );
    match query_status(result) {
        QueryStatus::Reachable => println!("Result: REACHABLE"),
        QueryStatus::NotReached => println!("Result: NOT REACHED"),
        QueryStatus::Unknown => {
            println!("Result: UNKNOWN");
            println!("Reason: obligation limit reached or unresolved internal call");
        }
    }
    println!(
        "Stats: {} obligations, {} must steps, {} refinement steps, {} may edges",
        result.stats.obligations_processed,
        result.stats.must_steps,
        result.stats.refinement_steps,
        result.state.may_edges().count(),
    );
}

fn query_status(result: &IntraproceduralResult) -> QueryStatus {
    if result.reached_target {
        QueryStatus::Reachable
    } else if result.stopped_by_limit {
        QueryStatus::Unknown
    } else {
        QueryStatus::NotReached
    }
}

fn assertion_path_predicates(registry: &LlvmEdgeRegistry) -> Vec<AssertionPathPredicates> {
    registry
        .iter()
        .filter_map(|metadata| {
            let site_post = assertion_site_predicate(metadata)?;
            let violation_post = assertion_violation_predicate(metadata)?;
            Some(AssertionPathPredicates {
                site: metadata.edge_id,
                site_post,
                violation_post,
            })
        })
        .collect()
}

fn should_dump_graphs() -> bool {
    std::env::var("MAY_MUST_SKIP_DOT")
        .map(|value| value != "1")
        .unwrap_or(true)
}

fn debug_dump_summaries(
    driver: &PaperDriver,
    procedures: &BTreeMap<ProcedureName, PaperProcedure>,
) {
    let mut total = 0usize;
    for procedure in procedures.keys() {
        for summary in driver.summaries().for_procedure(procedure) {
            total += 1;
            debug!(
                "Summary[{}] procedure={}, kind={:?}, pre={}, post={}, evidence={:?}",
                total, summary.procedure, summary.kind, summary.pre, summary.post, summary.evidence
            );
        }
    }
    if total == 0 {
        debug!("Summary table is currently empty");
    }
}

struct LlvmInterproceduralProvider<'a> {
    procedures: &'a BTreeMap<ProcedureName, PaperProcedure>,
    registries: &'a BTreeMap<ProcedureName, LlvmEdgeRegistry>,
    parameters: &'a BTreeMap<ProcedureName, Vec<String>>,
    assertion_target_mode: AssertionTargetMode,
}

impl InterproceduralOracleProvider for LlvmInterproceduralProvider<'_> {
    fn procedure(&self, procedure: &ProcedureName) -> Option<&PaperProcedure> {
        self.procedures.get(procedure)
    }

    fn transitions(
        &self,
        procedure: &ProcedureName,
        target_assertion: Option<crate::analysis::vocabulary::EdgeId>,
    ) -> Option<Box<dyn crate::analysis::oracle::TransitionOracle + '_>> {
        let registry = self.registries.get(procedure)?;
        Some(Box::new(
            SmtLlvmTransitionOracle::with_target_assertion_mode(
                registry,
                target_assertion,
                self.assertion_target_mode,
            ),
        ))
    }

    fn project_call_query(
        &self,
        caller_query: &ReachabilityQuery,
        call_edge: &PaperEdge,
        omega_n1: &Predicate,
        source_region: &Predicate,
        dest_region: &Predicate,
    ) -> Option<ReachabilityQuery> {
        let EdgeKind::Call { callee } = &call_edge.transition.kind else {
            return None;
        };
        let caller_registry = self.registries.get(&caller_query.procedure)?;
        let call_metadata = caller_registry.metadata(call_edge.id)?;
        let callee_parameters = self
            .parameters
            .get(callee)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let projected = project_call_query(
            &caller_query.procedure,
            callee,
            call_edge.id,
            call_metadata,
            caller_registry,
            callee_parameters,
            omega_n1,
            source_region,
            dest_region,
        );
        debug!(
            "Projected MayCall query for {} via {}: pre={}, post={}",
            callee, call_edge.id, projected.pre, projected.post
        );
        Some(projected)
    }

    fn normalize_projected_callee_query(
        &self,
        caller_query: &ReachabilityQuery,
        call_edge: &PaperEdge,
        projected: ReachabilityQuery,
    ) -> ReachabilityQuery {
        let EdgeKind::Call { callee } = &call_edge.transition.kind else {
            return projected;
        };
        let Some(caller_registry) = self.registries.get(&caller_query.procedure) else {
            return projected;
        };
        let Some(call_metadata) = caller_registry.metadata(call_edge.id) else {
            return projected;
        };
        let callee_parameters = self
            .parameters
            .get(callee)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let normalized = normalize_projected_query_to_callee_boundary(
            callee,
            call_metadata,
            callee_parameters,
            projected,
        );
        debug!(
            "Normalized callee query for summary generation {} via {}: pre={}, post={}",
            callee, call_edge.id, normalized.pre, normalized.post
        );
        normalized
    }
}

fn graph_output_dir(input_file: &str) -> String {
    let stem = Path::new(input_file)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("module");
    format!("graph_dot/{stem}")
}

fn init_logger(level: &u8) {
    let env;
    match level {
        0 => {
            env = Env::default().filter_or("CRICK_LOG", "info");
        }
        _ => {
            env = Env::default().filter_or("CRICK_LOG", "trace");
        }
    }
    Builder::from_env(env).format_level(true).init();
}

fn main() {
    let matches = command!() // requires `cargo` feature
        .arg(arg!([name] "LLVM BC file to operate on"))
        .arg(arg!(
            -d --debug ... "Turn debugging information on"
        ))
        .arg(arg!(-a --assert <STRING> "assertion to check, e.g. 'main => %23 == 1'. If omitted, embedded may_assert calls are checked"))
        .arg(
            arg!(--"max-steps" <N> "maximum intraprocedural obligations per query")
                .required(false)
                .value_parser(value_parser!(usize))
                .default_value("20000"),
        )
        .get_matches();

    let inpfile;
    init_logger(
        matches
            .get_one::<u8>("debug")
            .expect("Counts are defaulted"),
    );
    match matches.get_one::<String>("name") {
        Some(name) => {
            inpfile = name;
        }
        None => {
            info!("Nothing to process");
            return;
        }
    }
    let assertion_ast = matches.get_one::<String>("assert").cloned();
    let max_steps = *matches.get_one::<usize>("max-steps").unwrap_or(&20_000);

    initialize_target();
    let context = Context::new();
    match context.parse_bc_file(inpfile) {
        Some(module) => handle(module, inpfile, assertion_ast, max_steps),
        None => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::llvm_adapter::LlvmEdgeMetadata;
    use crate::analysis::vocabulary::NodeId;

    #[test]
    fn assertion_path_predicates_include_site_and_violation_jobs() {
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(LlvmEdgeMetadata {
            edge_id: EdgeId(7),
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Call,
            instruction_text: "call void @may_assert(i1 %cond)".to_string(),
            assignment: None,
            called_function: Some("may_assert".to_string()),
            operands: vec!["%cond".to_string()],
            branch_condition: None,
            successor_index: None,
        });

        let jobs = assertion_path_predicates(&registry);
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].site, EdgeId(7));
        assert_eq!(jobs[0].site_post, Predicate::atom("assert_violation(e7)"));
        assert_eq!(
            jobs[0].violation_post,
            Predicate::and([
                Predicate::atom("assert_violation(e7)"),
                Predicate::not(Predicate::atom("%cond")),
            ])
        );
    }
}
