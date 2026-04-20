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
use crate::analysis::cfg::{EdgeKind, PaperEdge, PaperProcedure};
use crate::analysis::driver::{InterproceduralConfig, InterproceduralOracleProvider};
use crate::analysis::driver::{IntraproceduralConfig, PaperDriver};
use crate::analysis::formula::Predicate;
use crate::analysis::llvm_adapter::{adapt_function_graph, AdaptedProcedure, LlvmEdgeRegistry};
use crate::analysis::oracle::SmtPredicateOracle;
use crate::analysis::summaries::ReachabilityQuery;
use crate::analysis::transfer::{assertion_violation_predicate, SmtLlvmTransitionOracle};
use crate::analysis::vocabulary::ProcedureName;
use crate::llvm_utils::llvm_wrap::*;
use crate::llvm_utils::program_graph::FunctionGraph;
use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use log::*;
use std::collections::{BTreeMap, BTreeSet};
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
    let mut driver = PaperDriver::new();
    let mut adapted = BTreeMap::<ProcedureName, AdaptedProcedure>::new();
    for graph in graphs {
        let procedure_name = ProcedureName::new(graph.name.clone());
        match adapt_function_graph(graph) {
            Ok(adapted_procedure) => {
                adapted.insert(procedure_name, adapted_procedure);
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
    let provider = LlvmInterproceduralProvider {
        procedures: &procedures,
        registries: &registries,
    };

    for graph in graphs {
        let procedure_name = ProcedureName::new(graph.name.clone());
        let Some(registry) = registries.get(&procedure_name) else {
            continue;
        };
        let query = default_query_for_graph(graph, registry);
        let result = match driver.run_interprocedural(
            &predicates,
            &provider,
            &query,
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
            println!("Reason: obligation limit reached or unresolved internal call");
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

struct LlvmInterproceduralProvider<'a> {
    procedures: &'a BTreeMap<ProcedureName, PaperProcedure>,
    registries: &'a BTreeMap<ProcedureName, LlvmEdgeRegistry>,
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
        Some(Box::new(SmtLlvmTransitionOracle::with_target_assertion(
            registry,
            target_assertion,
        )))
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

        let mut shared = BTreeSet::new();
        for operand in &call_metadata.operands {
            shared.insert(operand.clone());
        }
        for metadata in caller_registry.iter() {
            for operand in &metadata.operands {
                if operand.starts_with('@') {
                    shared.insert(operand.clone());
                }
            }
        }
        if shared.is_empty() {
            return None;
        }

        let call_pre = project_predicate(
            &Predicate::and([omega_n1.clone(), source_region.clone()]),
            &shared,
        );
        let call_post = project_predicate(dest_region, &shared);
        Some(ReachabilityQuery::new(callee.clone(), call_pre, call_post))
    }
}

fn project_predicate(predicate: &Predicate, shared: &BTreeSet<String>) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Atom(atom) => {
            if atom_uses_shared_symbol(atom, shared) || !atom_has_symbolic_name(atom) {
                Predicate::atom(atom.clone())
            } else {
                Predicate::True
            }
        }
        Predicate::Not(inner) => Predicate::not(project_predicate(inner, shared)),
        Predicate::And(parts) => {
            Predicate::and(parts.iter().map(|part| project_predicate(part, shared)))
        }
        Predicate::Or(parts) => {
            Predicate::or(parts.iter().map(|part| project_predicate(part, shared)))
        }
    }
}

fn atom_uses_shared_symbol(atom: &str, shared: &BTreeSet<String>) -> bool {
    shared
        .iter()
        .filter(|token| !token.is_empty())
        .any(|token| atom.contains(token))
}

fn atom_has_symbolic_name(atom: &str) -> bool {
    atom.contains('%') || atom.contains('@')
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
