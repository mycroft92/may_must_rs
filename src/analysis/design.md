# Analysis Design

## Current Phase

The active codebase has been reconstructed to the pre-driver milestone:

- implemented and CLI-active:
  - LLVM bitcode parsing
  - instruction-level `FunctionGraph` construction
  - DOT dumping for those graphs
  - C fixture compilation under `tests/flow/`
  - `--simple-check` for the current acyclic single-procedure checker
- implemented but not wired:
  - assertion-to-formula translation
  - paper formula language
  - paper state carriers
  - paper CFG with synthetic single-exit normalization
  - SMT oracle feasibility/implication queries
  - named paper rules from Figures 5-10
  - paper summary tables
  - normalized transfer effects
  - LLVM-to-paper lowering in `llvm_adapter.rs`
- planned:
  - full driver orchestration over the implemented rules
  - `Pre` / `Post` candidate generation from lowered effects
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
named paper rules             -> src/analysis/rules.rs
summary facts                 -> src/analysis/summaries.rs
temporary acyclic driver      -> src/analysis/driver.rs
normalized local effects       -> src/analysis/transfer.rs
LLVM adapter lowering          -> src/analysis/llvm_adapter.rs
raw solver layer               -> src/smt/solver.rs
```

## Key Boundaries

- `cfg.rs` stores only edge-local guards and relations (`Gamma_e`).
- accumulated path predicates belong in `state.rs`.
- `oracle.rs` is the solver boundary for feasibility and implication queries.
- `rules.rs` owns the named declarative rules and keeps their interfaces close
  to the paper.
- `summaries.rs` stores summary facts, but summary scheduling still belongs in
  the future driver.
- `driver.rs` is currently a temporary acyclic path explorer that wires the
  existing lowering, transfer, and oracle pieces into one end-to-end check.
- `transfer.rs` consumes normalized effects from `llvm_adapter.rs`; it does not
  inspect raw LLVM instructions.
- `llvm_adapter.rs` lowers one procedure into:
  - `Cfg`
  - `node_effects`
  - `edge_effects`
- `may_assert` is lowered as an obligation, not as a call summary.
- multi-exit procedures are normalized by creating one synthetic exit node and
  adding trivial `true` edges from each real exit to that node.

## Rule Layer

`rules.rs` is organized by paper figure instead of by internal engine phase.

- `figure5`
  holds `INIT_PI_NE`, `NOTMAY_PRE`, `IMPL_LEFT`, `IMPL_RIGHT`, and `VERIFIED`
- `figure6`
  holds `INIT_OMEGA`, `MUST_POST`, and `BUGFOUND`
- `figure7`
  holds the combined `MUST_POST` and `NOTMAY_PRE` rules that use both `Π_n`
  and `Ω_n`
- `figure8` and `figure9`
  hold the summary-creation and summary-reuse rules
- `figure10`
  holds the mixed may/must call rules

The main carrier used by the rule layer is `ProcedureFrame`, which stores:

- the normalized paper CFG `P`
- the current query `⟨ϕ1 ?⇒_P ϕ2⟩`
- `Π_n` as a list of formula regions per node
- `Ω_n` as one accumulated formula per node
- `N_e` as blocked `(ϕ1, ϕ2)` region pairs per edge

`summaries.rs` stores the two paper summary relations:

- `NotMaySummary` for `¬may ⇒ P`
- `MustSummary` for `must ⇒ P`

Those tables are intentionally simple keyed vectors at the current milestone.
Rule scheduling and summary selection still belong in the future driver.

## Current Simplifications

The current rule implementation stays close to the paper interface, but a few
representation choices are deliberately minimal:

- regions are plain `Formula` values
- `Π_n` is stored as a vector of regions; there is no separate partition object
- `Ω_n` is accumulated as one disjunction per node
- `N_e` stores exact blocked region pairs rather than a symbolic relation
- `β`, `θ`, and local-variable projection are explicit rule inputs; the rules do
  not derive them themselves
- the current `driver.rs` explores acyclic paths directly instead of scheduling
  the paper rules

The main conservative check is the abstract path search used by `VERIFIED` and
`CREATE_NOTMAYSUMMARY`:

- it explores `(node, partition-region)` states over the current CFG
- it treats an edge as blocked only when the exact blocked pair is present in
  `N_e`
- SMT `Unknown` during overlap checks is treated as "may overlap" so the result
  stays conservative
