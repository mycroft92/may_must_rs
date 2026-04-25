# TASKVIEW

## Phase

Current phase: pre-driver intraprocedural lowering.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- LLVM adapter lowering through `transfer.rs`
- synthetic single-exit normalization for multi-exit procedures
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- oracle queries
- forward propagation
- backward propagation
- loop handling

## Next Session Plan

1. Introduce the oracle abstraction without leaking solver policy into `cfg/state/transfer`.
2. Add forward propagation over the lowered CFG/effects.
3. Decide the smallest honest CLI integration point for assertion checking.
4. Only then add `max_step` for loops.
