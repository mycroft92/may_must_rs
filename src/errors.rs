//! Shared error type for the analyzer.
//!
//! The project uses a single `ProgError` enum so parsing, LLVM graph building,
//! and filesystem operations can all return the same `Result<T>` alias. Error
//! variants stay close to the subsystem that detects them, but callers do not
//! need to thread multiple error types through the frontend / graph-building
//! pipeline. The deeper paper analysis layers use narrower local error types
//! and are converted only when the CLI/frontend boundary needs one umbrella
//! result.

use crate::llvm_utils::llvm_wrap::Instruction;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProgError {
    #[error("Error making program graph: {inst}, {1}", inst=(.0).print())]
    GraphError(Instruction, String),
    #[error("No definition for: {0}")]
    NoDefinitionForGraph(String),
    #[error("IO Error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("Error Parsing File: {0}")]
    ParseError(String),
}

pub type Result<T> = std::result::Result<T, ProgError>;
