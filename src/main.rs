//! CLI entry point for the current LLVM-to-SMASH prototype.
//!
//! The binary still prints raw `FunctionGraph` summaries and optional DOT
//! output, but it now also exposes two executable analysis slices:
//!
//! - `--simple-check` for the broader bounded single-procedure executor
//! - `--rule-check` for the paper-shaped rule driver with module-level summary
//!   reuse across supported calls

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
use log::LevelFilter;
use std::path::Path;

enum SimpleProcedureSummary {
    Checked(analysis::driver::SimpleProcedureReport),
    Unsupported { procedure: String, reason: String },
}

enum RuleProcedureSummary {
    Checked(analysis::driver::RuleProcedureReport),
    Unsupported { procedure: String, reason: String },
}

fn main() {
    let matches = command!()
        .arg(arg!(<INPUT> "LLVM bitcode file").value_parser(value_parser!(String)))
        .arg(arg!(--"no-dot" "Skip DOT graph emission"))
        .arg(arg!(--"simple-check" "Run the current bounded single-procedure checker"))
        .arg(arg!(--"rule-check" "Run the current acyclic summary-driven rule checker"))
        .arg(arg!(--"trace-predicates" "Emit predicate traces for the simple checker as debug logs"))
        .arg(
            arg!(--"max-step" <MAX_STEP> "Temporary per-edge loop visit bound for the simple checker")
                .required(false)
                .value_parser(value_parser!(usize))
                .default_value("3"),
        )
        .get_matches();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let dump_dot = !matches.get_flag("no-dot");
    let trace_predicates = matches.get_flag("trace-predicates");
    let max_step = *matches.get_one::<usize>("max-step").unwrap();
    let simple_check = matches.get_flag("simple-check") || trace_predicates;
    let rule_check = matches.get_flag("rule-check");
    init_logging(trace_predicates);
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
        simple_check,
        rule_check,
        analysis::driver::SimpleDriverOptions {
            max_step,
            trace_predicates,
        },
    );
}

fn init_logging(trace_predicates: bool) {
    let mut builder = Builder::from_env(Env::default().default_filter_or("info"));
    if trace_predicates {
        builder.filter_module(analysis::driver::TRACE_TARGET, LevelFilter::Debug);
        builder.filter_module("llvm_reader::llvm_utils::program_graph", LevelFilter::Info);
        builder.filter_module("main::llvm_utils::program_graph", LevelFilter::Info);
    }
    builder.init();
}

fn handle(
    module: Module,
    input_file: &str,
    dump_dot: bool,
    simple_check: bool,
    rule_check: bool,
    options: analysis::driver::SimpleDriverOptions,
) {
    match generate_program_graph(&module) {
        Ok(graphs) => {
            let mut simple_summaries = Vec::<SimpleProcedureSummary>::new();
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
                if simple_check {
                    match analysis::driver::analyze_function_graph_simple_with_purity(
                        graph,
                        &memory_pure_functions,
                        options.clone(),
                    ) {
                        Ok(report) => {
                            simple_summaries.push(SimpleProcedureSummary::Checked(report))
                        }
                        Err(error) => simple_summaries.push(SimpleProcedureSummary::Unsupported {
                            procedure: graph.name.clone(),
                            reason: error.to_string(),
                        }),
                    }
                }
                if rule_check {
                    // Module-level rule execution is reported after discovery so
                    // call summaries can be shared across procedures.
                }
            }
            if rule_check {
                match analysis::driver::analyze_function_graphs_rules_with_purity_best_effort(
                    &graphs,
                    &memory_pure_functions,
                ) {
                    Ok(results) => {
                        for (procedure, report) in results {
                            match report {
                                Ok(report) => {
                                    rule_summaries.push(RuleProcedureSummary::Checked(report))
                                }
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
            }
            if simple_check {
                println!();
                println!("Simple-check summaries:");
                for summary in simple_summaries {
                    match summary {
                        SimpleProcedureSummary::Checked(report) => println!("{report}"),
                        SimpleProcedureSummary::Unsupported { procedure, reason } => {
                            println!("procedure {procedure}");
                            println!("  unsupported: {reason}");
                        }
                    }
                    println!();
                }
            }
            if rule_check {
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
            if !simple_check && !rule_check {
                println!(
                    "Paper CFG/transfer lowering is implemented; use --simple-check for the bounded checker or --rule-check for the current acyclic summary-driven rule checker."
                );
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
    fn checked_summary_uses_driver_display() {
        let rendered = format!(
            "{}",
            analysis::driver::SimpleProcedureReport::summary_only(
                "subject",
                analysis::rules::QueryJudgement::No,
                analysis::driver::DEFAULT_MAX_STEP,
                1,
                0,
                0,
                1,
                0,
            )
        );
        assert!(rendered.contains("procedure subject"));
        assert!(rendered.contains("judgement: No"));
        assert!(rendered.contains("max step: 3"));
    }
}
