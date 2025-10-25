mod errors;
mod llvm_utils;
use crate::expressions::exp::{parse_cmd_line, Assertion, Expr, Statement};
use crate::llvm_utils::llvm_wrap::*;
use clap::{arg, command, value_parser, ArgAction, Command};
use env_logger::{Builder, Env};
use log::*;
use std::env;
mod expressions;

fn handle(module: Module) {
    match llvm_utils::program_graph::generate_program_graph(&module) {
        Ok(res_) => {
            llvm_utils::program_graph::dump_graphs(&res_, "graph_dot");
        }
        Err(err) => error!("{err}"),
    }
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
        .arg(arg!(-a --assert <STRING> "assertion to look for"))
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
    let assert_stmt;
    match matches.get_one::<String>("assert") {
        Some(cmd) => {
            assert_stmt = cmd;
        }
        None => {
            info!("Nothing to process");
            return;
        }
    }

    let assertion_ast;
    match parse_cmd_line(assert_stmt) {
        Err(e) => {
            std::process::exit(1);
        }
        Ok(assertion) => {
            assertion_ast = assertion;
        }
    }

    initialize_target();
    let context = Context::new();
    match context.parse_bc_file(inpfile) {
        Some(module) => handle(module),
        None => {}
    }
}
