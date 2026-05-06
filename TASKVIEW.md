# TASKVIEW

## Phase

Current phase: interprocedural paper rule driving with default witnesses, plus a temporary bounded checker.

Implemented:

- `FunctionGraph` generation with `may_assert` removal and assertion-site metadata
- assertion translation into the paper formula language
- paper CFG/state/transfer modules
- paper summary tables
- named paper rules from Figures 5-10
- temporary bounded intraprocedural driver with `max_step`
- Figure 5-10 rule-driven checker for acyclic procedures, including the current scalar-return call slice plus integer-array memory and impure-call-havoc rewriting
- default witness/model replay for false results in that rule-driven slice
- scalar `β` / `θ` generation from lowered `Assign` / `Assume` effects
- summary provider/repository boundary plus module-level summary work queue
- call-site alpha-renaming and interface substitution for summary instantiation
- LLVM adapter lowering through `transfer.rs`
- paper oracle feasibility/implication queries
- synthetic single-exit normalization for multi-exit procedures
- temporary loop support through per-edge `max_step` bounds
- integer-array memory handling plus conservative call-memory havoc
- `tests/flow` fixture corpus and `make -C tests smoke`

Not wired:

- opt-in LLM candidate provider/injection layer for function summaries and loop invariants
- richer instruction-aware effect-to-`Pre` / `Post` computation beyond the current integer-array memory and havoc slice
- full loop-aware CLI rule execution
- loop summaries / invariant generation
- external trusted summary loading

## Next Session Plan

1. Add an opt-in LLM candidate-generation switch for loop/function summary candidates while keeping the default non-LLM route unchanged.
2. Add oracle-backed verification/adoption flow for LLM-proposed candidates.
3. Broaden `--rule-check` from the current scalar-return summary slice to richer interfaces, projections, and memory-aware summaries.
4. Replace the temporary `max_step` policy with loop summaries / invariants.
