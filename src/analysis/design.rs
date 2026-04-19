//! Design notes for the active paper-shaped analysis.
//!
//! This module exists so `cargo doc` and editor navigation can surface the
//! paper-to-code contract.  The longer human-facing note lives in
//! `src/analysis/design.md`, and the flow-oriented companion lives in
//! `src/analysis/analysis_flow.md`.

/// Short summary of the active analysis boundary.
pub const DESIGN_SUMMARY: &str = "\
src/analysis is the active paper-shaped implementation. It defines Pi_n \
partitions, Omega_n must-reachable sets, Gamma_e edge semantics, summaries, \
and named rule functions. LLVM integration is handled through Option A \
adapters (external edge metadata plus transition oracle), while the previous \
mixed implementation is preserved under obsolete/src/analysis.";
