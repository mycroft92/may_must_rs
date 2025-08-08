mod llvm_wrap;
use crate::llvm_wrap::*;

use std::env;
fn handle(module: Module) {
    let mut fset = module.get_all_functions();
    for f in &mut fset {
        print!("Function visit: {}\n", f.get_name());
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
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
