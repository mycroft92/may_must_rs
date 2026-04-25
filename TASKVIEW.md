# TASKVIEW

## Phase

Current phase: paper rules plus a temporary acyclic checker.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- paper summary tables
- named paper rules from Figures 5-10
- temporary acyclic intraprocedural driver
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- rule-driven orchestration
- effect-to-`Pre` / `Post` computation
- full CLI rule execution
- loop handling

## Next Session Plan

1. Replace the temporary acyclic checker in `driver.rs` with rule-driven scheduling.
2. Connect lowered effects to candidate `β` / `θ` computations for `NOTMAY-PRE` and `MUST-POST`.
3. Thread summary tables through actual call handling.
4. Decide the smallest honest CLI integration point for assertion checking, then add `max_step`.
