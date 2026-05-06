# Analysis Design

## Current Phase

The active codebase now has one CLI-active interprocedural paper-rule driver:

- implemented and CLI-active:
  - LLVM bitcode parsing
  - instruction-level `FunctionGraph` construction
  - DOT dumping for those graphs
  - C fixture compilation under `tests/flow/`
  - default rule-check execution from the CLI
  - temporary `max_step` loop bounding in `analysis::driver`
  - query-specific assertion lowering plus Figure 5-10 scheduling in
    `analysis::driver`
  - integer-array memory modeling and conservative call-memory havoc
  - rule-query rewriting for the current acyclic memory/call-havoc slice
  - summary provider/repository boundary and module-level summary reuse
  - trait-based summary generation for loops/functions, including a Tokio/JSON
    adapter for external modules
  - visible memory ports in procedure/call summaries
  - SCC-based loop extraction and acyclic summary-structure condensation
- implemented but not wired:
  - broader instruction-aware rule candidate generation
  - loop invariant verification/adoption
- planned:
  - richer external candidate providers
  - loop summaries/invariants

## Module Mapping

```text
raw LLVM graph generation      -> src/llvm_utils/program_graph.rs
assertion frontend parsing     -> src/expressions/exp.rs
assertion frontend translation -> src/assertions/translation.rs
formula vocabulary             -> src/analysis/formula.rs
paper CFG (P, n, e, Gamma_e)   -> src/analysis/cfg.rs
loop regions / summary sites   -> src/analysis/loops.rs
paper state (Pi_n, Omega_n)    -> src/analysis/state.rs
oracle SAT/implication         -> src/analysis/oracle.rs
named paper rules             -> src/analysis/rules.rs
summary facts                 -> src/analysis/summaries.rs
bounded + rule driver         -> src/analysis/driver.rs
normalized local effects       -> src/analysis/transfer.rs
LLVM adapter lowering          -> src/analysis/llvm_adapter.rs
raw solver layer               -> src/smt/solver.rs
```

## Key Boundaries

- `cfg.rs` stores only edge-local guards and relations (`Gamma_e`).
- accumulated path predicates belong in `state.rs`.
- `oracle.rs` is the solver boundary for feasibility, implication, and
  on-demand model queries.
- `rules.rs` owns the named declarative rules and keeps their interfaces close
  to the paper.
- `summaries.rs` stores accepted summary facts and repository/provider reads.
- `loops.rs` stores loop regions, the condensation DAG, and the trait-based
  generation boundary for internal or external summary producers.
- `driver.rs` now contains:
  - the CLI-active rule scheduler for acyclic visible-memory procedures
  - a legacy bounded executor that remains only as internal scaffolding until
    loop summaries fully replace it
- the rule-driven slice rewrites each assertion into a synthetic violation-exit
  query and computes scalar `β` / `θ` candidates from normalized `Assign` /
  `Assume` effects plus `Gamma_e`.
- before scheduling the rules, the rule-driven slice now rewrites the current
  acyclic integer-array memory effects (`alloca` / `load` / `store` / `gep`)
  and impure-call havoc into a path-expanded scalar query.
- that same rule-driven slice also builds one reusable base procedure per
  function, records discovered `must` / `¬may` summaries, and instantiates
  them at supported call sites through alpha-renamed interface substitution
  over scalar arguments, returns, and visible memory ports.
- that same rule-driven slice now always attaches an internal
  Knaster-Tarski-style summary generator; external JSON-backed summary
  catalogs are optional and fall back to that internal route.
- that same rule-driven slice replays one feasible path through the assertion
  query CFG and attaches the final SMT model for the violating state.
- `loops.rs` exposes loop regions and an acyclic summary structure so loop
  invariants can later slot into the driver without re-deriving CFG structure.
- `state.rs` also carries current pointer bindings and per-region memory arrays
  for the active executable slice.
- `transfer.rs` consumes normalized effects from `llvm_adapter.rs`; it does not
  inspect raw LLVM instructions.
- `llvm_adapter.rs` lowers one procedure into:
  - `Cfg`
  - `SummaryStructure`
  - `node_effects`
  - `edge_effects`
- the current memory model is intentionally narrow: integer arrays only,
  pointer phis unsupported, and impure calls havoc all tracked regions.
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

`summaries.rs` stores the current reusable summary/invariant carriers:

- `NotMaySummary` for `¬may ⇒ P`
- `MustSummary` for `must ⇒ P`
- `LoopInvariantSummary` for future loop-header facts

Those tables are intentionally simple keyed vectors at the current milestone.
`SummaryRepository` is the current accepted-summary store, `SummaryProvider`
is the read seam for already adopted summaries, and `loops::SummaryGenerator`
is the generation seam for internal algorithms or external JSON-backed
producers.

## Current Simplifications

The current rule implementation stays close to the paper interface, but a few
representation choices are deliberately minimal:

- regions are plain `Formula` values
- `Π_n` is stored as a vector of regions; there is no separate partition object
- `Ω_n` is accumulated as one disjunction per node
- `N_e` stores exact blocked region pairs rather than a symbolic relation
- `β`, `θ`, and local-variable projection remain explicit rule inputs in
  `rules.rs`; the current `driver.rs` now computes only the scalar acyclic
  subset of those candidates
- the current `driver.rs` still uses a separate bounded path explorer for loops
  and for code outside the current interprocedural rule slice
- the current rule witnesses are postprocessed from the lowered query CFG
  rather than reconstructed from explicit must-rule provenance
- the current memory-aware rule rewrite is still path-expansion-oriented rather
  than a full paper summary abstraction
- summary projection currently relies on syntactic hidden-assignment
  elimination rather than a complete quantifier-elimination strategy

The main conservative check is the abstract path search used by `VERIFIED` and
`CREATE_NOTMAYSUMMARY`:

- it explores `(node, partition-region)` states over the current CFG
- it treats an edge as blocked only when the exact blocked pair is present in
  `N_e`
- SMT `Unknown` during overlap checks is treated as "may overlap" so the result
  stays conservative
