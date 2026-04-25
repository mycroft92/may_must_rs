# TASKVIEW

## Phase

Current phase: pre-driver intraprocedural lowering plus solver-backed oracle.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- named paper rules
- backward `NOTMAY-PRE`
- forward `MUST-POST`
- loop handling

## Next Session Plan

1. Add the named rule layer so the implementation speaks the paper directly.
2. Wire backward `NOTMAY-PRE` using the current oracle queries.
3. Wire forward `MUST-POST` over the lowered CFG/effects.
4. Decide the smallest honest CLI integration point for assertion checking, then add `max_step`.
