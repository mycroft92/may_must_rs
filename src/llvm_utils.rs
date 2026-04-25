#![allow(dead_code)]

//! LLVM-facing utilities.
//!
//! `llvm_wrap` is the unsafe boundary around LLVM's C API. `program_graph`
//! consumes those wrappers and builds analysis-owned CFG data structures.

pub mod llvm_wrap;
pub mod program_graph;
