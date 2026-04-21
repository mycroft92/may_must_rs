//! Paper-shaped may/must analysis.
//!
//! This is now the primary `crate::analysis` tree. Its names are meant to map
//! directly to the SMASH rules: `Pi`, `Omega`, `Gamma_e`, may edges, must
//! summaries, and not-may summaries.
//!
//! Paper correspondence by module:
//!
//! ```text
//! vocabulary.rs   -> identifiers for P, n, e, region ids
//! formula.rs      -> phi / beta / theta / query and summary predicates
//! cfg.rs          -> P, e, Gamma_e
//! state.rs        -> Pi_n, Omega_n, N_e
//! summaries.rs    -> queries and procedure summaries
//! call_projection.rs -> LLVM call-boundary query projection/renaming helpers
//! rules.rs        -> named paper rules
//! oracle.rs       -> abstract set / transition reasoning boundary
//! llvm_adapter.rs -> LLVM -> (P, e, metadata)
//! transfer.rs     -> LLVM-backed approximation of Gamma_e reasoning
//! driver.rs       -> analysis control flow
//! ```
//!
//! Keep the core paper-rule modules free of LLVM and Z3 details. Option A
//! adapter modules (`llvm_adapter`, `transfer`) can depend on LLVM wrappers,
//! but `cfg`, `state`, `rules`, `summaries`, and `oracle` should stay readable
//! in paper vocabulary.

pub mod call_projection;
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
