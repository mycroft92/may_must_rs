//! CLI entry point for the current LLVM-to-SMASH prototype.
//!
//! The binary still prints raw `FunctionGraph` summaries and optional DOT
//! output, but its only active solver path is now the paper-shaped rule
//! driver. By default that driver uses the internal Knaster-Tarski summary
//! generator. An external JSON summary catalog can be enabled explicitly
//! through the CLI and falls back to the internal generator when an entry is
//! missing.
//!
//! The CLI remains intentionally honest about phase boundaries: loop regions
//! are extracted and reported into the rule pipeline, but verified loop
//! invariants are not active yet, so cyclic procedures still return
//! `Unknown`/unsupported on the rule-driven path. An opt-in trace switch can
//! also dump the rule-engine predicate state (`Π_n`, `Ω_n`, and `N_e`) after
//! initialization and each successful rule application.

mod analysis;
mod assertions;
mod errors;
mod expressions;
mod llvm_utils;
mod smt;

use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use llvm_utils::llvm_wrap::{initialize_target, Context, Module};
use llvm_utils::program_graph::{dump_graphs, generate_program_graph};
use std::path::Path;
use std::sync::Arc;

enum RuleProcedureSummary {
    Checked(analysis::driver::RuleProcedureReport),
    Unsupported { procedure: String, reason: String },
}

fn main() {
    let matches = command!()
        .arg(arg!(<INPUT> "LLVM bitcode file").value_parser(value_parser!(String)))
        .arg(arg!(--"no-dot" "Skip DOT graph emission"))
        .arg(arg!(--"print-states" "Print rule-engine predicate states after each successful step"))
        .arg(
            arg!(--"external-summaries" <SUMMARY_JSON> "Load external loop/function summaries from a JSON catalog")
                .required(false)
                .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(--"kt-max-iterations" <KT_MAX_ITERATIONS> "Maximum Knaster-Tarski iterations for internal loop summary generation")
                .required(false)
                .value_parser(value_parser!(usize))
                .default_value("16"),
        )
        .get_matches();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let dump_dot = !matches.get_flag("no-dot");
    let print_states = matches.get_flag("print-states");
    let external_summaries = matches.get_one::<String>("external-summaries").cloned();
    let kt_max_iterations = *matches.get_one::<usize>("kt-max-iterations").unwrap();
    init_logging(print_states);
    initialize_target();

    let context = Context::new();
    let Some(module) = context.parse_bc_file(input) else {
        eprintln!("Unable to parse bitcode file: {input}");
        std::process::exit(1);
    };
    handle(
        module,
        input,
        dump_dot,
        external_summaries,
        kt_max_iterations,
    );
}

fn init_logging(print_states: bool) {
    let default_filter = if print_states {
        "info,analysis_trace=debug"
    } else {
        "info"
    };
    Builder::from_env(Env::default().default_filter_or(default_filter)).init();
}

fn handle(
    module: Module,
    input_file: &str,
    dump_dot: bool,
    external_summaries: Option<String>,
    kt_max_iterations: usize,
) {
    match generate_program_graph(&module) {
        Ok(graphs) => {
            let mut rule_summaries = Vec::<RuleProcedureSummary>::new();
            let memory_pure_functions =
                analysis::llvm_adapter::infer_memory_pure_functions(&graphs);
            if dump_dot {
                let out_dir = graph_output_dir(input_file);
                dump_graphs(&graphs, &out_dir);
                println!("DOT graphs written to {out_dir}");
            }
            for graph in &graphs {
                println!(
                    "Function {}: {} visible instructions, {} assertion sites",
                    graph.name,
                    graph.vertices.len(),
                    graph.asserts.len()
                );
            }

            let external_summary_generator = match external_summaries {
                Some(path) => {
                    match analysis::loops::JsonSummaryCatalogGenerator::from_path(&path) {
                        Ok(generator) => {
                            Some(Arc::new(generator) as Arc<dyn analysis::loops::SummaryGenerator>)
                        }
                        Err(error) => {
                            eprintln!("{error}");
                            std::process::exit(1);
                        }
                    }
                }
                None => None,
            };
            match analysis::driver::analyze_function_graphs_rules_with_purity_best_effort_with_options(
                &graphs,
                &memory_pure_functions,
                analysis::driver::RuleDriverOptions {
                    knaster_tarski_max_iterations: kt_max_iterations,
                    external_summary_generator,
                },
            ) {
                Ok(results) => {
                    for (procedure, report) in results {
                        match report {
                            Ok(report) => rule_summaries.push(RuleProcedureSummary::Checked(report)),
                            Err(error) => {
                                rule_summaries.push(RuleProcedureSummary::Unsupported {
                                    procedure,
                                    reason: error.to_string(),
                                })
                            }
                        }
                    }
                }
                Err(error) => {
                    for graph in &graphs {
                        rule_summaries.push(RuleProcedureSummary::Unsupported {
                            procedure: graph.name.clone(),
                            reason: error.to_string(),
                        });
                    }
                }
            }

            println!();
            println!("Rule-check summaries:");
            for summary in rule_summaries {
                match summary {
                    RuleProcedureSummary::Checked(report) => println!("{report}"),
                    RuleProcedureSummary::Unsupported { procedure, reason } => {
                        println!("procedure {procedure}");
                        println!("  unsupported: {reason}");
                    }
                }
                println!();
            }
        }
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}

fn graph_output_dir(input_file: &str) -> String {
    let stem = Path::new(input_file)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("graph");
    format!("graph_dot/{stem}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_output_dir_uses_input_stem() {
        assert_eq!(graph_output_dir("/tmp/sample.bc"), "graph_dot/sample");
    }
}
