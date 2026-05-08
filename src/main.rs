//! CLI entry point for the current LLVM-to-abstract-CFG prototype.
//!
//! The binary parses LLVM bitcode, builds raw instruction graphs, optionally
//! emits DOT output, lowers each procedure into the current abstract CFG, and
//! runs the active backward safety checker. Loops are still reported honestly:
//! cyclic CFGs remain unsupported by the checker and therefore yield
//! `UNKNOWN`.

mod analysis;
mod assertions;
mod errors;
mod expressions;
mod llvm_utils;
mod smt;

use analysis::driver::ProcedureReport;
use clap::{arg, command, value_parser};
use llvm_utils::llvm_wrap::{initialize_target, Context, Module};
use llvm_utils::program_graph::{dump_graphs, generate_program_graph};
use std::path::Path;

enum CliReport {
    Checked(ProcedureReport),
    Unsupported { procedure: String, reason: String },
}

fn main() {
    let matches = command!()
        .arg(arg!(<INPUT> "LLVM bitcode file").value_parser(value_parser!(String)))
        .arg(arg!(--"no-dot" "Skip DOT graph emission"))
        .get_matches();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let dump_dot = !matches.get_flag("no-dot");
    initialize_target();

    let context = Context::new();
    let Some(module) = context.parse_bc_file(input) else {
        eprintln!("Unable to parse bitcode file: {input}");
        std::process::exit(1);
    };
    handle(module, input, dump_dot);
}

fn handle(module: Module, input_file: &str, dump_dot: bool) {
    match generate_program_graph(&module) {
        Ok(graphs) => {
            let memory_pure_functions = analysis::adapter::infer_memory_pure_functions(&graphs);
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
            let oracle = analysis::oracle::Oracle::new();

            println!();
            println!("Analysis summaries:");
            let reports =
                collect_reports(&graphs, &memory_pure_functions, &oracle).unwrap_or_else(|error| {
                    eprintln!("{error}");
                    std::process::exit(1);
                });
            for report in reports {
                match report {
                    CliReport::Checked(report) => {
                        println!("{report}");
                        println!("  verdict: {}", report.verdict());
                    }
                    CliReport::Unsupported { procedure, reason } => {
                        println!("procedure {procedure}");
                        println!("  unsupported: {reason}");
                        println!("  verdict: UNKNOWN");
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

fn collect_reports(
    graphs: &[llvm_utils::program_graph::FunctionGraph],
    memory_pure_functions: &std::collections::BTreeSet<String>,
    oracle: &analysis::oracle::Oracle,
) -> Result<Vec<CliReport>, analysis::driver::DriverError> {
    match analysis::driver::analyze_module(graphs, memory_pure_functions, oracle) {
        Ok(reports) => Ok(reports.into_iter().map(CliReport::Checked).collect()),
        Err(_) => {
            let mut reports = Vec::new();
            for graph in graphs {
                match analysis::driver::analyze_function_graph_with_purity(
                    graph,
                    memory_pure_functions,
                    oracle,
                ) {
                    Ok(report) => reports.push(CliReport::Checked(report)),
                    Err(error) => reports.push(CliReport::Unsupported {
                        procedure: graph.name.clone(),
                        reason: error.to_string(),
                    }),
                }
            }
            Ok(reports)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_output_dir_uses_input_stem() {
        assert_eq!(graph_output_dir("/tmp/sample.bc"), "graph_dot/sample");
    }

    #[test]
    fn collect_reports_falls_back_to_unsupported_entries() {
        initialize_target();
        let context = Context::new();
        let module = context
            .parse_ir_str(
                r#"
                    declare void @may_assert(i1)
                    define void @main(float %x) {
                    entry:
                        %c = fcmp ogt float %x, 0.0
                        call void @may_assert(i1 %c)
                        ret void
                    }
                "#,
                "test",
            )
            .unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let oracle = analysis::oracle::Oracle::new();
        let reports = collect_reports(&graphs, &std::collections::BTreeSet::new(), &oracle)
            .expect("fallback reporting should succeed");
        assert!(matches!(
            reports.as_slice(),
            [CliReport::Unsupported { procedure, .. }] if procedure == "main"
        ));
    }
}
