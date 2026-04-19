//! Paper-shaped may/must analysis scaffold.
//!
//! `analysis2` is intentionally independent from `crate::analysis`.  The
//! existing `analysis` tree is an executable prototype.  This tree is a
//! second, paper-first model whose names are meant to map directly to the
//! SMASH rules: `Pi`, `Omega`, `Gamma_e`, may edges, must summaries, and
//! not-may summaries.
//!
//! Keep the core paper-rule modules free of LLVM and Z3 details. Option A
//! adapter modules (`llvm_adapter`, `transfer`) can depend on LLVM wrappers,
//! but `cfg`, `state`, `rules`, `summaries`, and `oracle` should stay readable
//! in paper vocabulary.

pub mod cfg;
pub mod design;
pub mod driver;
pub mod formula;
pub mod llvm_adapter;
pub mod oracle;
pub mod rules;
pub mod state;
pub mod summaries;
pub mod transfer;
pub mod vocabulary;
