#![allow(dead_code)]

//! Paper-core analysis modules that mirror the notation in the SMASH paper.
//!
//! Current milestone status:
//!
//! - CLI-active: `driver`, `rules`, `oracle`, and the lowering stack needed by
//!   them;
//! - reusable core representations: `formula`, `state`, `cfg`, `transfer`,
//!   `llvm_adapter`, `summaries`, `loops`;
//! - newly wired structural hooks: visible memory summary ports, extracted
//!   loop regions, accepted-summary repositories, and a trait-based summary
//!   generator seam with an optional Tokio/JSON adapter;
//! - still planned: verified loop summaries/invariants, richer call/memory
//!   summaries, and CLI wiring for external candidate providers.
//!
//! The intention is to keep this tree LLVM-independent except for
//! `llvm_adapter`, which lowers one `FunctionGraph` into the paper-shaped CFG
//! plus normalized local effects.

pub mod cfg;
pub mod driver;
pub mod formula;
pub mod llvm_adapter;
pub mod loops;
pub mod oracle;
pub mod rules;
pub mod simplify;
pub mod state;
pub mod summaries;
pub mod transfer;
