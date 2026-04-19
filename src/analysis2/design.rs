//! Design notes for `analysis2`.
//!
//! This module exists so `cargo doc` and editor navigation can surface the
//! paper-to-code contract.  The longer human-facing note lives in
//! `src/analysis2/design.md`.

/// Short summary of the `analysis2` boundary.
pub const DESIGN_SUMMARY: &str = "\
analysis2 is a paper-shaped scaffold. It defines Pi_n partitions, Omega_n \
must-reachable sets, Gamma_e edge semantics, summaries, and named rule \
functions without depending on the existing analysis implementation. LLVM \
integration is handled through Option A adapters (external edge metadata + \
transition oracle).";
