//! CLI entrypoint for the reconstructed may/must analyzer.

mod analysis;
mod cfg;
mod formula;
mod frontend;
mod pointer_analysis;
mod smt;

use analysis::backward::{self, InvariantConfig};
use analysis::interproc::driver::{ModuleReport, SafetyVerdict};
use analysis::interproc::providers::NoProvider;
use cfg::adapter::{ReturnSummary, WriteEffectSummary};
use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use frontend::llvm_wrap::{initialize_target, Context, Module};
use frontend::program_graph::{dump_graphs, generate_program_graph, FunctionGraph};
use smt::oracle::Oracle;
use std::path::Path;

fn main() {
    let version = concat!(
        env!("CARGO_PKG_VERSION"),
        " (",
        env!("GIT_COMMIT_HASH"),
        ")"
    );
    println!(
        "Smash-plus-ultra v{} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("GIT_COMMIT_HASH")
    );
    let matches = command!()
        .version(version)
        .arg(arg!(<INPUT> "LLVM bitcode file").value_parser(value_parser!(String)))
        .arg(arg!(--"no-dot" "Skip DOT graph emission"))
        .arg(arg!(--"show-summaries" "Print inferred summaries"))
        .arg(arg!(--"debug-invariants" "Enable loop invariant debug logging"))
        .arg(arg!(--"diff-debug" "Print each rule firing and new predicates added"))
        .arg(
            arg!(--"max-function-size" <N> "Skip analysis of functions with more than N instructions (default: 500; 0 = unlimited)")
                .required(false)
                .value_parser(value_parser!(usize))
                .default_value("500"),
        )
        .arg(
            arg!(--"achar-timeout" <SECS> "Time budget in seconds for the ACHAR CEGIS loop invariant synthesis phase per loop (default: 10)")
                .required(false)
                .value_parser(value_parser!(u64))
                .default_value("10"),
        )
        .get_matches();

    init_logging(
        matches.get_flag("debug-invariants"),
        matches.get_flag("diff-debug"),
    );
    log::info!(
        "Smash-plus-ultra v{} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("GIT_COMMIT_HASH")
    );
    initialize_target();

    let input = matches.get_one::<String>("INPUT").unwrap();
    let context = Context::new();
    let Some(module) = context.parse_bc_file(input) else {
        eprintln!("Unable to parse bitcode file: {input}");
        std::process::exit(1);
    };

    let inv_config = invariant_config(&matches);
    handle(
        module,
        input,
        !matches.get_flag("no-dot"),
        matches.get_flag("show-summaries"),
        inv_config,
    );
}

fn init_logging(debug_invariants: bool, diff_debug: bool) {
    let default_filter = match (debug_invariants, diff_debug) {
        (_, true) => "info,loop_invariant=debug,rules=debug",
        (true, false) => "info,loop_invariant=debug",
        _ => "info",
    };
    Builder::from_env(Env::default().default_filter_or(default_filter)).init();
}

fn invariant_config(matches: &clap::ArgMatches) -> InvariantConfig {
    let max_function_size = *matches
        .get_one::<usize>("max-function-size")
        .unwrap_or(&500);
    let achar_timeout_secs = *matches.get_one::<u64>("achar-timeout").unwrap_or(&10);
    InvariantConfig {
        max_function_size,
        achar_timeout: std::time::Duration::from_secs(achar_timeout_secs),
    }
}

fn handle(
    module: Module,
    input_file: &str,
    dump_dot: bool,
    show_summaries: bool,
    inv_config: InvariantConfig,
) {
    let graphs = match generate_program_graph(&module) {
        Ok(graphs) => graphs,
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    };

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

    let memory_pure = cfg::adapter::infer_memory_pure_functions(&graphs);
    let oracle = Oracle::new();
    let report = analysis::interproc::driver::analyze_module_with_provider(
        &graphs,
        &memory_pure,
        &NoProvider,
        &oracle,
        &inv_config,
    )
    .unwrap_or_else(|error| {
        eprintln!("{error}");
        std::process::exit(1);
    });

    print_module_report(&report, &graphs, show_summaries);
}

fn print_module_report(report: &ModuleReport, graphs: &[FunctionGraph], show_summaries: bool) {
    println!();
    println!("Analysis summaries:");
    let mut module_verdict = SafetyVerdict::Safe;
    for procedure in &report.reports {
        let graph = graphs
            .iter()
            .find(|graph| graph.name == procedure.procedure);
        let assertion_count = procedure.assertions.len();
        let instruction_count = graph
            .map(|graph| graph.vertices.len())
            .unwrap_or(procedure.instruction_count);
        let loop_count = procedure.loop_count;
        let recursive = procedure.recursive;
        println!(
            "procedure {}  [{} assertion(s), {} instruction(s){}{}]",
            procedure.procedure,
            assertion_count,
            instruction_count,
            if loop_count > 0 {
                format!(" | {loop_count} loop(s)")
            } else {
                String::new()
            },
            if recursive { " | recursive" } else { "" }
        );
        for assertion in &procedure.assertions {
            println!("{}", backward::render_result(assertion));
        }
        for failure in &procedure.failures {
            println!("  unsupported: {failure}");
        }
        if recursive {
            println!("  note: procedure participates in a direct or indirect call cycle");
        }
        let verdict = procedure.verdict();
        println!("  verdict: {verdict}");
        module_verdict = combine_verdict(module_verdict, verdict);
        println!();
    }
    println!("module verdict: {module_verdict}");

    if show_summaries {
        println!();
        println!("[return summaries]");
        for summary in &report.computed_summaries {
            print_summary(summary);
        }
        println!("[forward-may summaries]");
        for name in report.summaries.all_procedure_names() {
            for summary in report.summaries.forward_may(&name) {
                println!(
                    "  {name}: {} => {}",
                    summary.precondition, summary.postcondition
                );
            }
        }
        println!("[not-may summaries]");
        for name in report.summaries.all_procedure_names() {
            for summary in report.summaries.notmay(&name) {
                println!(
                    "  {name}: {} => {}",
                    summary.precondition, summary.postcondition
                );
            }
        }
        println!("[loop invariants]");
        for name in report.summaries.all_procedure_names() {
            for (header, invariant) in report.summaries.get_loop_invariants(&name) {
                println!(
                    "  {name} @ {:?}: {}",
                    header,
                    backward::pretty_formula(invariant)
                );
            }
        }
    }
}

fn print_summary(summary: &ReturnSummary) {
    println!("  {}:", summary.function);
    println!("    params: {}", summary.formal_parameters.join(", "));
    println!("    retval: {}", summary.retval_name);
    println!("    relation: {}", summary.relation);
    for write in &summary.write_effects {
        print_write_effect(write);
    }
}

fn print_write_effect(write: &WriteEffectSummary) {
    println!(
        "    write param #{} {} -> {}: {}",
        write.param_index, write.ext_region_name, write.obs_name, write.relation
    );
}

fn combine_verdict(lhs: SafetyVerdict, rhs: SafetyVerdict) -> SafetyVerdict {
    match (lhs, rhs) {
        (SafetyVerdict::Unsafe, _) | (_, SafetyVerdict::Unsafe) => SafetyVerdict::Unsafe,
        (SafetyVerdict::Unknown, _) | (_, SafetyVerdict::Unknown) => SafetyVerdict::Unknown,
        (SafetyVerdict::Safe, SafetyVerdict::Safe) => SafetyVerdict::Safe,
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
        assert_eq!(graph_output_dir("tests/out/foo.bc"), "graph_dot/foo");
    }
}
