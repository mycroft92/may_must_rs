Experimental LLVM may/must analysis work. MIT Licensed.

## Current Status

The repository has been reconstructed to the paper-shaped pre-driver milestone.

Implemented and CLI-active:

- LLVM bitcode parsing
- instruction-level `FunctionGraph` construction
- DOT graph dumping
- fixture compilation under `tests/flow/`

Implemented but not wired:

- assertion-to-formula translation
- paper formula vocabulary
- paper state carriers (`Pi_n`, `Omega_n`)
- paper CFG (`P`, `n`, `e`, `Gamma_e`)
- SMT oracle feasibility and implication queries over paper formulas/states
- named paper rules from Figures 5-10
- paper summary tables for `¬may ⇒ P` and `must ⇒ P`
- normalized transfer effects
- LLVM adapter lowering into `Cfg + node_effects + edge_effects`

Planned:

- driver orchestration over the named paper rules
- `max_step`
- summaries and loop invariants

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

The paper CFG/effect lowering is compiled and unit-tested, but not invoked by
the CLI yet.

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
src/analysis/transfer.rs        -> normalized local effects
src/analysis/llvm_adapter.rs    -> FunctionGraph -> cfg + node/edge effects
src/smt/solver.rs               -> raw Z3 lowering
```

Key boundaries:

- `cfg.rs` stores only edge-local guards/relations.
- accumulated path predicates belong in `state.rs`.
- `oracle.rs` is the only paper module that answers solver-backed feasibility
  and implication queries.
- `rules.rs` keeps the rule names and premises close to the paper instead of
  hiding them behind a generic engine.
- `transfer.rs` interprets normalized effects produced by `llvm_adapter.rs`.
- `llvm_adapter.rs` lowers one procedure into `cfg + node_effects + edge_effects`.
- `may_assert` becomes an obligation, not a summarized call edge.
- multi-exit procedures are normalized to one synthetic exit with trivial
  `true` edges from the real exits.

## Next Milestone

1. Add a driver skeleton that executes the named rule modules over lowered procedures.
2. Wire the current `rules.rs` over `Cfg + state + oracle + summaries`.
3. Add CLI assertion selection/query integration.
4. Add temporary `max_step` handling before loop summaries.
