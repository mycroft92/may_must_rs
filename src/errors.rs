//! Shared error type for the analyzer.
//!
//! The project uses a single `ProgError` enum so parsing, LLVM graph building,
//! and filesystem operations can all return the same `Result<T>` alias. Error
//! variants stay close to the subsystem that detects them, but callers do not
//! need to thread multiple error types through the analysis pipeline.

use crate::llvm_utils::llvm_wrap::Instruction;
use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProgError {
    #[error("Error processing bc file")]
    LLVMError(String),
    #[error("Error making program graph: {inst}, {1}", inst=(.0).print())]
    GraphError(Instruction, String),
    #[error("No definition for: {0}")]
    NoDefinitionForGraph(String),
    #[error("IO Error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("Unknown Error: {0}")]
    UnknownError(String),
    #[error("Error Parsing File: {0}")]
    ParseError(String),
}

pub type Result<a> = std::result::Result<a, ProgError>;
