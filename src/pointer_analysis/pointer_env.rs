//! Pointer environment: maps SSA pointer names to (region, offset) pairs.
//!
//! `PointerEnv` is built by `adapter.rs` during Phase 2 of the CFG lowering
//! pipeline (`resolve_memory_effects`) and consumed by Phases 3–4 (return
//! summary application, memcpy expansion).
//!
//! The resolved bindings drive two downstream uses:
//! - **Region substitution** in callee summaries: `__ext_N` → caller region.
//! - **Load/Store rewriting**: `Load { src: ptr }` → `select(region, offset)`.

use std::collections::HashMap;

use crate::formula::Term;

/// Maps each pointer-typed SSA name to its resolved memory region and offset.
///
/// Built once during `resolve_memory_effects` and consulted by all subsequent
/// lowering phases.  A pointer not present in the env was unresolvable (e.g.
/// returned from an unanalyzed external call); callers handle `None`
/// conservatively by keeping the effect unresolved.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct PointerEnv {
    bindings: HashMap<String, PointerBinding>,
}

impl PointerEnv {
    /// Record that `pointer` points to `region` at integer `offset`.
    pub fn bind(&mut self, pointer: String, region: String, offset: Term) {
        self.bindings
            .insert(pointer, PointerBinding { region, offset });
    }

    /// Look up the resolved binding for `pointer`.
    /// Returns `None` if the pointer was never bound.
    pub fn get(&self, pointer: &str) -> Option<&PointerBinding> {
        self.bindings.get(pointer)
    }
}

/// A resolved pointer target: the memory region name and the offset term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointerBinding {
    /// Logical memory region name (e.g. `fn$stack0`, `fn$__ext_0`).
    pub region: String,
    /// Offset within the region as an integer term (constant or GEP expression).
    pub offset: Term,
}
