//! CLI entry point for the reconstructed milestone.
//!
//! The active CLI surface stops at LLVM graph construction and DOT dumping.
//! The paper-shaped CFG/effect lowering exists in the crate and is unit-tested,
//! but it is not wired into a forward or backward analysis driver yet.

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
        .get_matches();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let dump_dot = !matches.get_flag("no-dot");

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
            println!("Paper CFG/transfer lowering is implemented but not wired into the CLI yet.");
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
