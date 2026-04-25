# Analysis Design

## Current Phase

The active codebase has been reconstructed to the pre-driver milestone:

- implemented and CLI-active:
  - LLVM bitcode parsing
  - instruction-level `FunctionGraph` construction
  - DOT dumping for those graphs
  - C fixture compilation under `tests/flow/`
- implemented but not wired:
  - assertion-to-formula translation
  - paper formula language
  - paper state carriers
  - paper CFG with synthetic single-exit normalization
  - SMT oracle feasibility/implication queries
  - normalized transfer effects
  - LLVM-to-paper lowering in `llvm_adapter.rs`
- planned:
  - named paper rules and driver orchestration
  - backward `NOTMAY-PRE`
  - forward `MUST-POST`
  - `max_step`
  - loop summaries/invariants

## Module Mapping

```text
raw LLVM graph generation      -> src/llvm_utils/program_graph.rs
assertion frontend parsing     -> src/expressions/exp.rs
assertion frontend translation -> src/assertions/translation.rs
formula vocabulary             -> src/analysis/formula.rs
paper CFG (P, n, e, Gamma_e)   -> src/analysis/cfg.rs
paper state (Pi_n, Omega_n)    -> src/analysis/state.rs
oracle SAT/implication         -> src/analysis/oracle.rs
normalized local effects       -> src/analysis/transfer.rs
LLVM adapter lowering          -> src/analysis/llvm_adapter.rs
raw solver layer               -> src/smt/solver.rs
```

## Key Boundaries

- `cfg.rs` stores only edge-local guards and relations (`Gamma_e`).
- accumulated path predicates belong in `state.rs`.
- `oracle.rs` is the solver boundary for feasibility and implication queries.
- `transfer.rs` consumes normalized effects from `llvm_adapter.rs`; it does not
  inspect raw LLVM instructions.
- `llvm_adapter.rs` lowers one procedure into:
  - `Cfg`
  - `node_effects`
  - `edge_effects`
- `may_assert` is lowered as an obligation, not as a call summary.
- multi-exit procedures are normalized by creating one synthetic exit node and
  adding trivial `true` edges from each real exit to that node.
