mod errors;
mod llvm_utils;
use crate::llvm_utils::llvm_wrap::*;
use clap::{arg, command, value_parser, ArgAction, Command};
use env_logger::{Builder, Env};
use log::*;
use std::env;

fn handle(module: Module) {
    let mut fset = module.get_all_functions();
    for f in &mut fset {
        info!("Function visit: {}\n", f.get_name());
        let mut bbs = f.get_all_basic_blocks();
        match bbs {
            None => info!("Skipping, no bbs found\n"),
            Some(bbs) => {
                for bb in bbs {
                    let instrs = bb.get_all_instructions();
                    for i in instrs {
                        if i.is_branch_instruction() {
                            info!("Branch: {} \n", i);
                        }
                    }
                }
            }
        }
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
    Builder::from_env(env)
        .format_level(false)
        .format_timestamp_nanos()
        .init();
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

    initialize_target();
    let context = Context::new();
    match context.parse_bc_file(inpfile) {
        Some(module) => handle(module),
        None => {}
    }
}
