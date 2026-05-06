#![allow(dead_code)]

//! Paper-core analysis modules that mirror the notation in the SMASH paper.
//!
//! Current milestone status:
//!
//! - CLI-active: `driver`, `rules`, `oracle`, and the lowering stack needed by
//!   them;
//! - reusable core representations: `formula`, `state`, `cfg`, `transfer`,
//!   `llvm_adapter`, `summaries`;
//! - newly wired structural hooks: visible memory summary ports, SCC-based loop
//!   regions, and a provider seam for future loop invariants;
//! - still planned: verified loop summaries/invariants, richer call/memory
//!   summaries, and opt-in external candidate providers.
//!
//! The intention is to keep this tree LLVM-independent except for
//! `llvm_adapter`, which lowers one `FunctionGraph` into the paper-shaped CFG
//! plus normalized local effects.

pub mod cfg;
pub mod driver;
pub mod formula;
pub mod llvm_adapter;
pub mod oracle;
pub mod rules;
pub mod state;
pub mod summaries;
pub mod transfer;
