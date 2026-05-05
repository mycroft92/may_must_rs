# TASKVIEW

## Phase

Current phase: local paper rule driving with default witnesses, plus a temporary bounded checker.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- paper summary tables
- named paper rules from Figures 5-10
- temporary bounded intraprocedural driver with `max_step`
- local Figure 5/6/7 rule-driven checker for acyclic procedures, including the current integer-array memory and impure-call-havoc slice
- on-demand witness/model replay for false results in that local rule-driven slice
- scalar `β` / `θ` generation from lowered `Assign` / `Assume` effects
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- temporary loop support through per-edge `max_step` bounds
- integer-array memory handling plus conservative call-memory havoc
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- summary-driven call orchestration
- richer instruction-aware effect-to-`Pre` / `Post` computation beyond the current integer-array memory and havoc slice
- full loop-aware CLI rule execution
- loop summaries / invariant generation

## Next Session Plan

1. Extend `--rule-check` from the current local acyclic scalar-plus-memory slice to summary-driven calls.
2. Broaden rule-driver instruction handling beyond the current integer-array memory and conservative havoc subset.
3. Replace the current conservative call-memory handling with Figure 8-10 summary reasoning.
4. Replace the temporary `max_step` policy with loop summaries / invariants.
