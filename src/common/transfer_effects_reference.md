# Transfer Effects Reference

The active abstract CFG models LLVM instruction semantics as a small sequence
of transfer effects on each node and edge.

- `Assign` substitutes scalar or Boolean SSA values.
- `Assume` constrains path reachability.
- `Obligation` records semantic facts required by assertion and summary reuse.
- `Alloca`, `GetElementPtr`, `PointerStore`, `PointerLoad`, and `PointerAlias`
  are pointer bookkeeping effects resolved by `resolve_memory_effects` before
  the analysis runs; they become `Nop` in the final CFG.
- `StructFieldGep` binds a struct-field pointer to a dedicated `$fN` sub-region.
- `MemoryStore` updates the integer-array memory model.
- `Call` records a direct call boundary and its memory effect (`PreservesMemory`
  or `HavocMemory`).
- `HavocRegions` conservatively drops constraints on a specific list of named
  memory regions.  Emitted when alias analysis identifies the target regions of
  an otherwise-unresolved pointer store; WP drops only conjuncts that mention
  the listed regions, preserving all unaffected constraints.
