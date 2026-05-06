#![allow(dead_code)]

//! LLVM-facing utilities.
//!
//! `llvm_wrap` is the unsafe boundary around LLVM's C API. `program_graph`
//! consumes those wrappers and builds the raw instruction-level
//! `FunctionGraph`s that the analysis adapter lowers later. The rest of the
//! codebase should not need to know about raw `LLVM*Ref` handles or about how
//! loop/call summaries are eventually built on top of the graph.

pub mod llvm_wrap;
pub mod program_graph;
