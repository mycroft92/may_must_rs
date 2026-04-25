//! CLI entry point for the reconstructed milestone.
//!
//! The active CLI surface stops at LLVM graph construction and DOT dumping.
//! The paper-shaped CFG/effect lowering exists in the crate and is unit-tested,
//! and a minimal acyclic single-procedure checker can now be run explicitly.

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

fn main() {
    Builder::from_env(Env::default().default_filter_or("info")).init();
    initialize_target();

    let matches = command!()
        .arg(arg!(<INPUT> "LLVM bitcode file").value_parser(value_parser!(String)))
        .arg(arg!(--"no-dot" "Skip DOT graph emission"))
        .arg(arg!(--"simple-check" "Run the current acyclic single-procedure checker"))
        .get_matches();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let dump_dot = !matches.get_flag("no-dot");
    let simple_check = matches.get_flag("simple-check");

    let context = Context::new();
    let Some(module) = context.parse_bc_file(input) else {
        eprintln!("Unable to parse bitcode file: {input}");
        std::process::exit(1);
    };
    handle(module, input, dump_dot, simple_check);
}

fn handle(module: Module, input_file: &str, dump_dot: bool, simple_check: bool) {
    match generate_program_graph(&module) {
        Ok(graphs) => {
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
                    match analysis::driver::analyze_function_graph_simple(graph) {
                        Ok(report) => println!(
                            "  simple-check: {:?} (paths={}, pruned={}, obligations={}, feasible={})",
                            report.judgement,
                            report.explored_paths,
                            report.pruned_paths,
                            report.checked_obligations,
                            report.feasible_obligations
                        ),
                        Err(error) => println!("  simple-check: unsupported ({error})"),
                    }
                }
            }
            if !simple_check {
                println!(
                    "Paper CFG/transfer lowering is implemented; use --simple-check for the current acyclic branch checker."
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
