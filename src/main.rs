//! CLI entry point.
//!
//! The binary keeps orchestration here and leaves the core work to modules:
//! parse command-line assertions, parse LLVM bitcode through `llvm_wrap`, build
//! per-function graphs, always dump DOT debug graphs, then run the current
//! SMASH-style analyzer.

mod errors;
mod llvm_utils;
use crate::analysis::may_must::{AnalysisAnswer, SmashAnalyzer, SmashConfig};
use crate::analysis::predicates::Formula;
use crate::analysis::smt_engine::{SmtAnalysisAnswer, SmtAnalysisEngine, SmtEngineConfig};
use crate::analysis::summary_store::SmtQuery;
use crate::expressions::exp::{parse_cmd_line, Assertion};
use crate::llvm_utils::llvm_wrap::*;
use crate::llvm_utils::program_graph::FunctionGraph;
use clap::{arg, command, value_parser};
use env_logger::{Builder, Env};
use log::*;
use std::path::Path;
mod expressions;

mod analysis;
mod smt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EngineChoice {
    Legacy,
    Smt,
}

impl EngineChoice {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "legacy" => Ok(Self::Legacy),
            "smt" => Ok(Self::Smt),
            other => Err(format!(
                "unknown analysis engine '{other}', expected 'legacy' or 'smt'"
            )),
        }
    }
}

fn handle(
    module: Module,
    input_file: &str,
    assertion: Option<Assertion>,
    max_steps: usize,
    engine: EngineChoice,
) {
    match llvm_utils::program_graph::generate_program_graph(&module) {
        Ok(graphs) => {
            let graph_dir = graph_output_dir(input_file);
            llvm_utils::program_graph::dump_graphs(&graphs, &graph_dir);
            match engine {
                EngineChoice::Legacy => run_legacy_analysis(graphs, assertion, max_steps),
                EngineChoice::Smt => run_smt_analysis(&graphs, assertion, max_steps),
            }
        }
        Err(err) => error!("{err}"),
    }
}

fn run_legacy_analysis(graphs: Vec<FunctionGraph>, assertion: Option<Assertion>, max_steps: usize) {
    let mut analyzer = SmashAnalyzer::new(
        graphs,
        SmashConfig {
            max_steps,
            ..SmashConfig::default()
        },
    );
    let reports = match assertion {
        Some(assertion) => vec![analyzer.analyze_assertion(assertion)],
        None => analyzer.analyze_embedded_assertions(),
    };

    if reports.is_empty() {
        println!("No embedded may_assert calls found.");
        return;
    }

    for report in reports {
        println!(
            "Query <{}: {} => {}>",
            report.query.function, report.query.pre, report.query.post
        );
        match report.answer {
            AnalysisAnswer::BugFound { trace } => {
                println!("Result: BUG reachable (must summary)");
                println!("Trace:");
                for (idx, step) in trace.iter().enumerate() {
                    println!("  {}. {}", idx + 1, step);
                }
            }
            AnalysisAnswer::ProvenSafe => {
                println!("Result: SAFE (not-may summary)");
            }
            AnalysisAnswer::Unknown { reason } => {
                println!("Result: UNKNOWN");
                println!("Reason: {reason}");
            }
        }
        println!(
            "Summaries: {} must, {} not-may",
            report.must_summaries, report.not_may_summaries
        );
    }
}

fn run_smt_analysis(graphs: &[FunctionGraph], assertion: Option<Assertion>, max_steps: usize) {
    if assertion.is_some() {
        println!("SMT engine does not support --assert yet; rerun with --engine legacy.");
        return;
    }

    let mut analyzer = SmtAnalysisEngine::new(SmtEngineConfig {
        max_steps,
        ..SmtEngineConfig::default()
    });
    let reports = analyzer.analyze_embedded_assertions(graphs);

    if reports.is_empty() {
        println!("No embedded may_assert calls found.");
        return;
    }

    for report in reports {
        println!(
            "Query <{}: {} => {}>",
            report.query.function,
            report.query.pre,
            smt_query_post(&report.query)
        );
        match report.answer {
            SmtAnalysisAnswer::BugFound { trace } => {
                println!("Result: BUG reachable (must summary)");
                println!("Trace:");
                for (idx, step) in trace.iter().enumerate() {
                    println!("  {}. {}", idx + 1, step);
                }
            }
            SmtAnalysisAnswer::ProvenSafe => {
                println!("Result: SAFE (not-may summary)");
            }
            SmtAnalysisAnswer::Unknown { reason } => {
                println!("Result: UNKNOWN");
                println!("Reason: {reason}");
            }
        }
        println!(
            "Summaries: {} must, {} not-may",
            report.must_summaries, report.not_may_summaries
        );
    }
}

fn smt_query_post(query: &SmtQuery) -> String {
    if query.post == Formula::True {
        query.target.to_string()
    } else {
        format!("{}:{}", query.target, query.post)
    }
}

fn graph_output_dir(input_file: &str) -> String {
    let stem = Path::new(input_file)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("module");
    format!("graph_dot/{stem}")
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
        .arg(arg!(-a --assert <STRING> "assertion to check, e.g. 'main => %23 == 1'. If omitted, embedded may_assert calls are checked"))
        .arg(
            arg!(--"max-steps" <N> "maximum symbolic execution steps per query")
                .required(false)
                .value_parser(value_parser!(usize))
                .default_value("20000"),
        )
        .arg(
            arg!(--engine <ENGINE> "analysis engine to run: legacy or smt")
                .required(false)
                .default_value("legacy"),
        )
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
    let assertion_ast = matches
        .get_one::<String>("assert")
        .map(|cmd| parse_cmd_line(cmd).unwrap_or_else(|_| std::process::exit(1)));
    let max_steps = *matches.get_one::<usize>("max-steps").unwrap_or(&20_000);
    let engine = matches
        .get_one::<String>("engine")
        .map(|value| {
            EngineChoice::parse(value).unwrap_or_else(|err| {
                eprintln!("{err}");
                std::process::exit(2);
            })
        })
        .unwrap_or(EngineChoice::Legacy);

    initialize_target();
    let context = Context::new();
    match context.parse_bc_file(inpfile) {
        Some(module) => handle(module, inpfile, assertion_ast, max_steps, engine),
        None => {}
    }
}
