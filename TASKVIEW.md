# TASKVIEW

## Phase

Current phase: paper rules plus a temporary bounded checker.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- paper summary tables
- named paper rules from Figures 5-10
- temporary bounded intraprocedural driver with `max_step`
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- temporary loop support through per-edge `max_step` bounds
- integer-array memory handling plus conservative call-memory havoc
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- rule-driven orchestration
- effect-to-`Pre` / `Post` computation
- full CLI rule execution
- loop summaries / invariant generation

## Next Session Plan

1. Replace the temporary bounded checker in `driver.rs` with rule-driven scheduling.
2. Connect lowered effects to candidate `β` / `θ` computations for `NOTMAY-PRE` and `MUST-POST`.
3. Replace the current conservative call-memory handling with summary-driven call reasoning.
4. Replace the temporary `max_step` policy with loop summaries / invariants.
