//! Grammar-based loop invariant synthesis (ACHAR approach).
//!
//! # Status
//!
//! Placeholder — not yet implemented.
//!
//! # Intended approach
//!
//! Given a loop and the assertion postconditions derived from the exit edges,
//! enumerate invariant shapes according to a grammar over the CFG's variable
//! and memory vocabulary, then check each candidate with the three-part
//! soundness criterion (initiation, inductiveness, exit closure).
//!
//! The grammar is intended to cover:
//!
//! - Linear arithmetic atoms over loop variables and integer constants.
//! - Observer atoms: `counter <= k || accumulator rel select(region, k)`.
//! - Conjunctions and disjunctions of the above up to a bounded depth.
//!
//! This module is intentionally independent of the entry-safety synthesis pass
//! in `loops.rs` — the two passes do not share candidate infrastructure.

use crate::common::abstract_cfg::{AbstractCfg, CfgNodeId};
use crate::common::formula::Formula;
use crate::may_must_analysis::loops::{InnerInvariants, LoopInfo};
use std::collections::BTreeMap;

/// Generate loop invariant candidates using a grammar over the loop vocabulary.
///
/// Currently unimplemented — always returns an empty list.
pub fn grammar_candidates(
    _info: &LoopInfo,
    _cfg: &AbstractCfg,
    _assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    _inner: InnerInvariants<'_>,
) -> Vec<Formula> {
    vec![]
}
