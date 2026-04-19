//! CLI entry point.
//!
//! The binary keeps orchestration here and leaves the core work to modules:
//! parse command-line assertions, parse LLVM bitcode through `llvm_wrap`, build
//! per-function graphs, always dump DOT debug graphs, then run the current
//! paper-shaped intraprocedural driver.
//!
//! Paper correspondence:
//!
//! ```text
//! CLI / bitcode input -> choose query and procedure to analyze
//! run_analysis(...)   -> instantiate P, query Q, and the active driver
//! ```

mod errors;
mod llvm_utils;
use crate::analysis::driver::{IntraproceduralConfig, PaperDriver};
use crate::analysis::formula::Predicate;
use crate::analysis::llvm_adapter::adapt_function_graph;
use crate::analysis::oracle::SmtPredicateOracle;
use crate::analysis::summaries::ReachabilityQuery;
use crate::analysis::transfer::{assertion_violation_predicate, SmtLlvmTransitionOracle};
use crate::llvm_utils::llvm_wrap::*;
use crate::llvm_utils::program_graph::FunctionGraph;
use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use log::*;
use std::path::Path;
mod expressions;

mod analysis;
mod smt;

fn handle(module: Module, input_file: &str, assertion: Option<String>, max_obligations: usize) {
    match llvm_utils::program_graph::generate_program_graph(&module) {
        Ok(graphs) => {
            let graph_dir = graph_output_dir(input_file);
            llvm_utils::program_graph::dump_graphs(&graphs, &graph_dir);
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
    let driver = PaperDriver::new();

    for graph in graphs {
        let adapted = match adapt_function_graph(graph) {
            Ok(adapted) => adapted,
            Err(err) => {
                println!("Unable to adapt {}: {err}", graph.name);
                continue;
            }
        };
        let query = default_query_for_graph(graph, &adapted.registry);
        let transitions = SmtLlvmTransitionOracle::with_target_assertion(
            &adapted.registry,
            query.target_assertion,
        );
        let result = match driver.run_intraprocedural(
            &predicates,
            &transitions,
            &adapted.procedure,
            &query,
            IntraproceduralConfig { max_obligations },
        ) {
            Ok(result) => result,
            Err(err) => {
                println!(
                    "Query <{}: {} => {}>",
                    query.procedure, query.pre, query.post
                );
                println!("Result: UNKNOWN");
                println!("Reason: {err}");
                continue;
            }
        };

        println!(
            "Query <{}: {} => {}>",
            query.procedure, query.pre, query.post
        );
        if result.reached_target {
            println!("Result: REACHABLE");
        } else if result.stopped_by_limit {
            println!("Result: UNKNOWN");
            println!("Reason: obligation limit reached");
        } else {
            println!("Result: NOT REACHED");
        }
        println!(
            "Stats: {} obligations, {} must steps, {} refinement steps, {} may edges",
            result.stats.obligations_processed,
            result.stats.must_steps,
            result.stats.refinement_steps,
            result.state.may_edges().count(),
        );
    }
}

fn default_query_for_graph(
    graph: &FunctionGraph,
    registry: &crate::analysis::llvm_adapter::LlvmEdgeRegistry,
) -> ReachabilityQuery {
    let target = registry
        .iter()
        .find(|metadata| metadata.called_function.as_deref() == Some("may_assert"));
    let post = target
        .and_then(assertion_violation_predicate)
        .unwrap_or(Predicate::False);
    let query = ReachabilityQuery::new(graph.name.clone(), Predicate::True, post);
    match target {
        Some(metadata) => query.with_target_assertion(metadata.edge_id),
        None => query,
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
