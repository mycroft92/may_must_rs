# TASKVIEW

## Phase

Current phase: pre-driver paper rules plus solver-backed oracle.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- paper summary tables
- named paper rules from Figures 5-10
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- rule driver/orchestration
- effect-to-`Pre` / `Post` computation
- CLI rule execution
- loop handling

## Next Session Plan

1. Add `driver.rs` around the implemented Figure 5-10 rule modules.
2. Connect lowered effects to candidate `β` / `θ` computations for `NOTMAY-PRE` and `MUST-POST`.
3. Thread summary tables through actual call handling.
4. Decide the smallest honest CLI integration point for assertion checking, then add `max_step`.
