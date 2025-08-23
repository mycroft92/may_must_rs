mod llvm_utils;

use crate::llvm_utils::llvm_wrap::*;

use std::env;
fn handle(module: Module) {
    let mut fset = module.get_all_functions();
    for f in &mut fset {
        print!("Function visit: {}\n", f.get_name());
        let mut bbs = f.get_all_basic_blocks();
        match bbs {
            None => print!("Skipping, no bbs found\n"),
            Some(bbs) => {
                for bb in bbs {
                    let instrs = bb.get_all_instructions();
                    for i in instrs {
                        if i.is_branch_instruction() {
                            print!("Branch: {} \n", i);
                        }
                    }
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: {} <bitcode-file>", args[0]);
        return;
    }

    initialize_target();
    let context = Context::new();
    match context.parse_bc_file(args[1].as_str()) {
        Some(module) => handle(module),
        None => {}
    }
}
