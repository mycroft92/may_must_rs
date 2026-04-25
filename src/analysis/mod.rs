#![allow(dead_code)]

//! Paper-core analysis modules that mirror the notation in the SMASH paper.
//!
//! Current milestone status:
//!
//! - implemented but not wired: `formula`, `state`, `cfg`, `transfer`,
//!   `llvm_adapter`, `oracle`, `rules`, `summaries`;
//! - planned: forward/backward drivers and loop handling.
//!
//! The intention is to keep this tree LLVM-independent except for
//! `llvm_adapter`, which lowers one `FunctionGraph` into the paper-shaped CFG
//! plus normalized local effects.

pub mod cfg;
pub mod formula;
pub mod llvm_adapter;
pub mod oracle;
pub mod rules;
pub mod state;
pub mod summaries;
pub mod transfer;
