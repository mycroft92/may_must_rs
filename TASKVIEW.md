# TASKVIEW

## Phase

Current phase: abstract-CFG lowering plus backward checking with partial cyclic
support through loop invariants.

Implemented:

- raw LLVM `FunctionGraph` generation
- `may_assert` extraction as assertion obligations
- abstract CFG nodes, edges, transfer effects, and synthetic single-exit
  normalization
- integer/boolean lowering plus integer-array memory handling
- `phi` edge lowering and branch-guard lowering
- direct-call return-summary inference and reuse
- backward per-assertion checking on acyclic CFGs
- loop-invariant discovery/debugging for cyclic procedures
- best-effort CLI reporting across mixed supported/unsupported procedures
- smoke corpus execution through `make -C tests smoke`

Not wired or unsupported:

- cyclic return-summary inference for looping callees
- floating-point lowering
- source-coordinate reporting from LLVM debug info
- CLI use of assertion text translation
- stronger external/manual invariant plumbing

## Next Session Plan

1. Finish interprocedural support for cyclic callees so looped helpers can
   contribute return summaries.
2. Tighten loop invariant checking semantics around nested loops and
   normalization.
3. If floating point is next, extend `formula.rs`, `solver.rs`, and
   `adapter.rs` together so the supported surface stays consistent.
4. Revisit the driver/CLI split so best-effort unsupported handling lives in
   the driver instead of only in `main.rs`.
