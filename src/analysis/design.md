# Analysis Design

## Current Phase

The active codebase now has both a temporary bounded explorer and an
interprocedural paper-rule driver:

- implemented and CLI-active:
  - LLVM bitcode parsing
  - instruction-level `FunctionGraph` construction
  - DOT dumping for those graphs
  - C fixture compilation under `tests/flow/`
  - `--simple-check` for the current bounded single-procedure checker
  - `--rule-check` for the current acyclic rule-driven checker
  - temporary `max_step` loop bounding in `analysis::driver`
  - query-specific assertion lowering plus Figure 5-10 scheduling in
    `analysis::driver`
  - integer-array memory modeling and conservative call-memory havoc
  - rule-query rewriting for the current acyclic memory/call-havoc slice
  - summary provider/repository boundary and module-level summary reuse
- implemented but not wired:
  - assertion-to-formula translation
  - paper formula language
  - paper state carriers
  - paper CFG with synthetic single-exit normalization
  - SMT oracle feasibility/implication queries
  - named paper rules from Figures 5-10
  - paper summary tables
  - broader instruction-aware rule candidate generation
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
- `summaries.rs` stores summary facts and the provider boundary, while summary
  scheduling belongs in `driver.rs`.
- `driver.rs` now contains two executable slices:
  - the broader temporary bounded path explorer
  - the narrower local rule scheduler for acyclic scalar-plus-memory procedures
- that bounded driver now produces an explicit per-assertion result and, for
  failing assertions, a symbolic evidence trace built from the explored
  state/edge formulas.
- the rule-driven slice rewrites each assertion into a synthetic violation-exit
  query and computes scalar `β` / `θ` candidates from normalized `Assign` /
  `Assume` effects plus `Gamma_e`.
- before scheduling the rules, the rule-driven slice now rewrites the current
  acyclic integer-array memory effects (`alloca` / `load` / `store` / `gep`)
  and impure-call havoc into a path-expanded scalar query.
- that same rule-driven slice also builds one reusable base procedure per
  function, records discovered `must` / `¬may` summaries, and instantiates
  them at supported call sites through alpha-renamed interface substitution.
- that same rule-driven slice replays one feasible path through the assertion
  query CFG and attaches the final SMT model for the violating state.
- the temporary loop policy is `APPROX_HEAVY`: each CFG edge may be visited at
  most `max_step` times on one explored path; budget exhaustion yields
  `Unknown`.
- `state.rs` also carries current pointer bindings and per-region memory arrays
  for the active executable slice.
- `transfer.rs` consumes normalized effects from `llvm_adapter.rs`; it does not
  inspect raw LLVM instructions.
- `llvm_adapter.rs` lowers one procedure into:
  - `Cfg`
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

`summaries.rs` stores the two paper summary relations:

- `NotMaySummary` for `¬may ⇒ P`
- `MustSummary` for `must ⇒ P`

Those tables are intentionally simple keyed vectors at the current milestone.
`SummaryRepository` is the current non-LLM source, and the `SummaryProvider`
trait is the stable seam for future imported or generated candidates.

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
