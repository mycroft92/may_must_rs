# Transfer Effects Reference

The active abstract CFG models LLVM instruction semantics as a small sequence
of transfer effects on each node and edge.

- `Assign` substitutes scalar or Boolean SSA values.
- `Assume` constrains path reachability.
- `Obligation` records semantic facts required by assertion and summary reuse.
- `Alloca`, `GetElementPtr`, `PointerStore`, and `PointerLoad` are pointer
  bookkeeping effects.
- `MemoryStore` updates the integer-array memory model.
- `Call` records a direct call boundary and its memory effect.
