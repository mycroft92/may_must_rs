# TASKVIEW

## Phase

Current phase: abstract-CFG lowering plus acyclic backward checking.

Implemented:

- raw LLVM `FunctionGraph` generation
- `may_assert` extraction as assertion obligations
- abstract CFG nodes, edges, transfer effects, and synthetic single-exit
  normalization
- integer/boolean lowering plus integer-array memory handling
- `phi` edge lowering and branch-guard lowering
- direct-call return-summary inference and reuse
- backward per-assertion checking on acyclic CFGs
- best-effort CLI reporting across mixed supported/unsupported procedures
- smoke corpus execution through `make -C tests smoke`

Not wired or unsupported:

- loop analysis beyond detecting that the CFG is cyclic
- floating-point lowering
- source-coordinate reporting from LLVM debug info
- CLI use of assertion text translation
- externally supplied loop invariants

## Next Session Plan

1. Choose the next unsupported slice to attack first: loops or floating point.
2. If loops are first, define the exact loop strategy before coding:
   invariant checking, summaries, or bounded exploration.
3. If floating point is first, extend `formula.rs`, `solver.rs`, and
   `adapter.rs` together so the supported surface stays consistent.
4. Revisit the driver/CLI split so best-effort unsupported handling lives in
   the driver instead of only in `main.rs`.
