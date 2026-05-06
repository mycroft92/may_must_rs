Experimental LLVM may/must analysis work. MIT Licensed.

## Current Status

The repository now has two executable driver slices: a broader temporary
bounded checker and a narrower paper-shaped interprocedural rule driver.

Implemented and CLI-active:

- LLVM bitcode parsing
- instruction-level `FunctionGraph` construction
- DOT graph dumping
- fixture compilation under `tests/flow/`
- `--simple-check` for the current bounded single-procedure checker
- `--rule-check` for the current acyclic summary-driven rule checker
- paper formula / CFG / state / transfer / oracle / rules / summaries modules
  through that rule-driven slice
- integer-array memory modeling for `alloca` / `load` / `store` / `gep`
- conservative call handling with memory-preserving vs memory-havocing callees
- summary-driven calls over scalar/boolean actuals, one optional scalar
  return, and visible memory ports on pointer arguments
- module-level work-queue scheduling for Figures 5-10
- provider/repository boundary for discovered summaries and future loop
  invariants
- alpha-renaming and call-site substitution for summary instantiation
- SCC-based loop extraction plus acyclic summary-structure condensation

Implemented but not wired:

- assertion-to-formula translation
- opt-in external summary/invariant candidate providers
- loop invariant verification/adoption in `analysis::driver`
- loop summaries in `analysis::driver`

Planned:

- loop summaries and invariants
- external summary loading for missing/external procedures

## How To Run

Compile the fixture corpus and run the CLI graph generator over it:

```sh
make -C tests smoke
```

Generate LLVM IR/bitcode only:

```sh
make -C tests ir
```

Run the CLI on one bitcode file:

```sh
cargo run --bin main -- tests/out/straight_line_assert.bc
```

Run the current bounded checker:

```sh
cargo run --bin main -- --simple-check --no-dot tests/out/multi_exit.bc
```

Run the checker with the temporary loop bound set explicitly:

```sh
cargo run --bin main -- --simple-check --max-step 2 --no-dot tests/out/multi_exit.bc
```

Run the checker with per-step predicate tracing as debug logs:

```sh
cargo run --bin main -- --trace-predicates --max-step 2 --no-dot tests/out/multi_exit.bc
```

Run the current rule-driven checker:

```sh
cargo run --bin main -- --rule-check --no-dot <bitcode-file>
```

That flag is CLI-active today. It currently supports acyclic procedures with
branching, summary-driven calls over scalar/boolean actuals plus visible
integer-array memory ports, and the current integer-array memory slice
(`alloca` / `load` / `store` / `gep`) with conservative impure-call memory
havoc when no stronger summary exists. Loops, pointer phis, richer
projection/elimination, and verified loop invariants are still outside that
rule slice.

Run unit tests:

```sh
cargo test -- --test-threads=1
```

Format:

```sh
cargo fmt
```

## Current CLI Behavior

The binary currently stops at LLVM graph generation. It:

- parses one `.bc` file
- builds per-function `FunctionGraph`s
- optionally dumps DOT output under `graph_dot/<input-stem>/`
- prints a small per-function summary

With `--simple-check`, the CLI also runs the current bounded single-procedure
checker over each function and prints one clean summary block per procedure
after the run.

Those per-procedure summaries include:

- final judgement
- active `max_step`
- explored path count
- pruned path count
- bounded path count
- checked obligation count
- feasible obligation count
- one explicit `true` / `false` / `unknown` result per lowered assertion

If an assertion is reported `false`, the summary also prints a symbolic
evidence trace showing the node/edge formulas and the failing obligation query
that made the negated assertion feasible. This remains a driver-collected
symbolic trace rather than a reconstructed paper-rule witness.

With `--trace-predicates`, the checker emits debug logs on the dedicated
`analysis_trace` target for generated formulas after each ordinary node/edge
step. Repeated loop traversals are summarized once per loop edge visit instead
of dumping every repeated internal step. Those debug lines also show the
current per-region memory arrays after each step.

That checker is intentionally limited:

- loops use a temporary per-edge `max_step` cutoff and return `Unknown` when a
  path is cut off by that budget
- call results are conservative and summary-free: scalar returns stay
  unconstrained, and memory is havoced unless the callee is inferred to be
  memory-pure
- memory is modeled only as integer arrays; floating-point memory and pointer
  phis are still outside the active subset
- some C loop fixtures still lower to memory-heavy or intrinsic forms that are
  outside the current transfer subset, so bounded-loop behavior is covered most
  directly by the `analysis::driver` unit tests today
- it explores paths directly instead of scheduling the full paper rule engine

With `--rule-check`, the CLI runs the current acyclic Figure 5-10 scheduler
over one assertion query at a time and prints one summary block per procedure.

That rule-driven checker is intentionally narrower:

- it rewrites each assertion into a query-specific synthetic violation exit and
  computes scalar `β` / `θ` candidates from `Assign` / `Assume` effects plus
  `Gamma_e`
- it rewrites the current acyclic integer-array memory/call-havoc slice into a
  path-expanded scalar query before running the paper rules
- it builds one reusable base rule procedure per analyzed function, records
  discovered `must` / `¬may` summaries, and reuses them across supported call
  sites through a provider/repository boundary
- it alpha-renames callee interface variables, substitutes actual arguments and
  return targets plus visible memory ports at the caller site, and maps caller
  queries back to callee interfaces before enqueueing subqueries
- for false results, it replays one feasible path through that synthetic
  violation CFG and prints the final SMT model for the violating state
- it still requires an acyclic summary structure; loops are extracted and kept
  as explicit regions, but remain unsupported there until loop summaries /
  invariants exist
- it schedules the currently supported Figure 5/6/7 local rules plus the
  Figure 8/9/10 summary/call rules for the current interprocedural slice
- those witnesses currently exist only for that same acyclic interprocedural
  slice; loops, pointer phis, and richer memory shapes still do not produce
  rule-check results today

## Active Architecture

```text
src/llvm_utils/program_graph.rs -> raw instruction graph generation
src/assertions/translation.rs   -> parser AST -> paper formula
src/analysis/formula.rs         -> predicate vocabulary
src/analysis/state.rs           -> Pi_n / Omega_n / tracked facts
src/analysis/cfg.rs             -> P / n / e / Gamma_e
src/analysis/oracle.rs          -> SMT feasibility / implication boundary
src/analysis/rules.rs           -> named rules from Figures 5-10
src/analysis/summaries.rs       -> `¬may ⇒ P` / `must ⇒ P` tables
src/analysis/driver.rs          -> bounded explorer + interprocedural rule scheduler
src/analysis/transfer.rs        -> normalized local effects
src/analysis/llvm_adapter.rs    -> FunctionGraph -> cfg + node/edge effects
src/smt/solver.rs               -> raw Z3 lowering
```

Key boundaries:

- `cfg.rs` stores only edge-local guards/relations.
- `cfg.rs` also extracts loop SCCs and the acyclic condensation order used for
  future loop-summary scheduling.
- accumulated path predicates and current per-region memory arrays belong in
  `state.rs`.
- `oracle.rs` is the only paper module that answers solver-backed feasibility
  and implication queries.
- `rules.rs` keeps the rule names and premises close to the paper instead of
  hiding them behind a generic engine.
- `summaries.rs` now also exposes the provider/repository boundary used by the
  interprocedural driver for both function summaries and future loop
  invariants.
- `transfer.rs` interprets normalized effects produced by `llvm_adapter.rs`.
- `llvm_adapter.rs` lowers one procedure into `cfg + node_effects + edge_effects`.
- local memory is modeled as integer arrays, and impure calls havoc those
  arrays conservatively.
- `may_assert` becomes an obligation, not a summarized call edge.
- multi-exit procedures are normalized to one synthetic exit with trivial
  `true` edges from the real exits.

## Rule Layer Notes

The rule implementation in [src/analysis/rules.rs](/Users/mycroft/work/pl_projects/may_must/src/analysis/rules.rs:1) is organized by the paper figures rather than by an internal engine abstraction.

- `ProcedureFrame` stores `P`, `Π_n`, `Ω_n`, `N_e`, and the active query
- `figure5` through `figure10` expose the named rule entry points directly
- `SummaryTables` in [src/analysis/summaries.rs](/Users/mycroft/work/pl_projects/may_must/src/analysis/summaries.rs:1) stores `¬may ⇒ P` and `must ⇒ P` facts

The rules are now scheduled for the current interprocedural slice:

- `driver.rs` computes scalar `β` / `θ` candidates for the current acyclic
  `Assign` / `Assume` procedures and path-expands the current memory/havoc
  slice into scalar rule queries
- `driver.rs` schedules the currently supported Figure 5-10 rules per
  assertion query
- `driver.rs` also schedules the Figure 8/9/10 call and summary rules over the
  current visible-memory call interface, with module-level summary reuse

Still unwired:

- broader instruction-aware rule candidates beyond the current integer-array
  memory and havoc slice
- loop invariants / loop summaries
- external file-backed or LLM-backed candidate providers

## Next Milestone

1. Add oracle-backed loop invariant verification/adoption over the new loop regions and summary structure.
2. Broaden the current summary-driven call slice to richer interfaces, memory effects, and projections.
3. Add an opt-in LLM candidate-generation/provider layer for loop invariants and function summaries while keeping the default non-LLM route unchanged.
4. Add loop summaries / invariants to `--rule-check` and retire the temporary bounded loop explorer.
