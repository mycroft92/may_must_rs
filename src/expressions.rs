#![allow(dead_code)]

//! Parser and AST entry point for user-facing assertion expressions.
//!
//! This module stays intentionally tiny so the assertion language can evolve
//! independently from LLVM parsing and the paper analysis core, including the
//! newer summary and loop-invariant plumbing.

pub mod exp;
