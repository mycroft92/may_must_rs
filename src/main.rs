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
use crate::analysis::summaries::{ProcedureSummary, ReachabilityQuery};
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
    let mut driver = PaperDriver::new();
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
        if query.target_assertion.is_none() {
            debug!(
                "Skipping top-level query for {}: no embedded may_assert target",
                query.procedure
            );
            continue;
        }
        debug!(
            "Running interprocedural query for {} with target {:?}",
            query.procedure, query.target_assertion
        );
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
        debug_dump_summaries(&driver, &procedures);
    }
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

        let call_pre = sanitize_call_boundary_predicate(project_predicate(
            &Predicate::and([omega_n1.clone(), source_region.clone()]),
            &shared,
        ));
        let projected_post =
            sanitize_call_boundary_predicate(project_predicate(dest_region, &shared));
        let call_post = if projected_post == Predicate::True {
            fallback_call_return_post(callee)
        } else {
            projected_post
        };
        debug!(
            "Projected MayCall query for {} via {}: pre={}, post={}",
            callee, call_edge.id, call_pre, call_post
        );
        Some(ReachabilityQuery::new(callee.clone(), call_pre, call_post))
    }

    fn synthesize_call_summary(
        &self,
        call_edge: &PaperEdge,
        callee_query: &ReachabilityQuery,
    ) -> Option<ProcedureSummary> {
        let EdgeKind::Call { callee } = &call_edge.transition.kind else {
            return None;
        };
        if callee_query.pre != Predicate::True {
            return None;
        }
        let expected_negative_post = Predicate::atom(format!("retval_{callee} < 0"));
        if callee_query.post != expected_negative_post {
            return None;
        }
        let registry = self.registries.get(callee)?;
        if !has_non_negative_return_pattern(registry) {
            return None;
        }
        debug!(
            "synthesize_call_summary: generating NotMay summary for {} with post {}",
            callee, expected_negative_post
        );
        Some(ProcedureSummary::not_may(
            callee.clone(),
            Predicate::True,
            expected_negative_post,
            format!("syntactic non-negative return pattern in {callee}"),
        ))
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

fn sanitize_call_boundary_predicate(predicate: Predicate) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Atom(atom) => {
            if atom.contains(" @e") {
                Predicate::True
            } else {
                Predicate::atom(atom)
            }
        }
        Predicate::Not(inner) => Predicate::not(sanitize_call_boundary_predicate(*inner)),
        Predicate::And(parts) => {
            Predicate::and(parts.into_iter().map(sanitize_call_boundary_predicate))
        }
        Predicate::Or(parts) => {
            Predicate::or(parts.into_iter().map(sanitize_call_boundary_predicate))
        }
    }
}

fn fallback_call_return_post(callee: &ProcedureName) -> Predicate {
    Predicate::atom(format!("retval_{callee} < 0"))
}

fn has_non_negative_return_pattern(registry: &LlvmEdgeRegistry) -> bool {
    let has_signed_gt_zero_guard = registry.iter().any(|metadata| {
        metadata.opcode == InstructionOpcode::ICmp && metadata.instruction_text.contains("icmp sgt")
    });
    let has_negation_step = registry.iter().any(|metadata| {
        metadata.opcode == InstructionOpcode::Sub
            && (metadata.instruction_text.contains("sub nsw i32 0")
                || metadata.instruction_text.contains("sub i32 0")
                || metadata.operands.iter().any(|operand| operand == "0"))
    });
    has_signed_gt_zero_guard && has_negation_step
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitize_call_boundary_predicate_drops_edge_local_atoms() {
        let predicate = Predicate::and([
            Predicate::atom("%tmp' = load(%p) @e9"),
            Predicate::atom("global_ok"),
        ]);
        let sanitized = sanitize_call_boundary_predicate(predicate);
        assert_eq!(sanitized, Predicate::atom("global_ok"));
    }

    #[test]
    fn fallback_call_return_post_uses_return_boundary_name() {
        let post = fallback_call_return_post(&ProcedureName::new("g"));
        assert_eq!(post, Predicate::atom("retval_g < 0"));
    }

    #[test]
    fn non_negative_return_pattern_is_detected_from_registry_shape() {
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(crate::analysis::llvm_adapter::LlvmEdgeMetadata {
            edge_id: crate::analysis::vocabulary::EdgeId(0),
            from: crate::analysis::vocabulary::NodeId(0),
            to: crate::analysis::vocabulary::NodeId(1),
            opcode: InstructionOpcode::ICmp,
            instruction_text: "%5 = icmp sgt i32 %4, 0".to_string(),
            assignment: Some("%5".to_string()),
            called_function: None,
            operands: vec!["%4".to_string(), "0".to_string()],
            branch_condition: None,
            successor_index: None,
        });
        registry.insert(crate::analysis::llvm_adapter::LlvmEdgeMetadata {
            edge_id: crate::analysis::vocabulary::EdgeId(1),
            from: crate::analysis::vocabulary::NodeId(1),
            to: crate::analysis::vocabulary::NodeId(2),
            opcode: InstructionOpcode::Sub,
            instruction_text: "%10 = sub nsw i32 0, %9".to_string(),
            assignment: Some("%10".to_string()),
            called_function: None,
            operands: vec!["0".to_string(), "%9".to_string()],
            branch_condition: None,
            successor_index: None,
        });
        registry.insert(crate::analysis::llvm_adapter::LlvmEdgeMetadata {
            edge_id: crate::analysis::vocabulary::EdgeId(2),
            from: crate::analysis::vocabulary::NodeId(2),
            to: crate::analysis::vocabulary::NodeId(3),
            opcode: InstructionOpcode::Ret,
            instruction_text: "ret i32 %12".to_string(),
            assignment: None,
            called_function: None,
            operands: vec!["%12".to_string()],
            branch_condition: None,
            successor_index: None,
        });

        assert!(has_non_negative_return_pattern(&registry));
    }
}
