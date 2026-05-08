Experimental LLVM assertion checker work. MIT licensed.

## Current Status

The active implementation is no longer the earlier `cfg/state/loops/transfer`
paper tree. The current CLI-active path is:

`LLVM bitcode -> FunctionGraph -> AbstractCfg -> backward safety check`

Implemented and CLI-active:

- LLVM bitcode parsing
- instruction-level `FunctionGraph` construction
- `may_assert` removal from the visible graph plus recorded assertion sites
- optional DOT dumping of raw function graphs
- lowering from `FunctionGraph` to `analysis::abstract_cfg::AbstractCfg`
- integer/boolean scalar reasoning
- integer-array memory modeling for `alloca` / `load` / `store` / `gep`
- `phi` lowering onto incoming edges
- ordinary branch guards on CFG edges
- `zext i1 -> i32` lowering through `bool_to_int`
- synthetic single-exit normalization for multi-exit procedures
- backward checking on acyclic CFGs
- simple interprocedural return-summary inference and reuse for direct calls
- best-effort CLI reporting: unsupported procedures return `UNKNOWN` instead of
  terminating the whole run
- curated smoke corpus under `tests/flow/`

Implemented but not CLI-active:

- assertion text translation in `src/assertions/translation.rs`
- manual/external summary provider seam in `src/analysis/providers.rs`
- summary tables in `src/analysis/summaries.rs`
- source-location carrier types; LLVM debug-location extraction is not wired

Unsupported and reported as `UNKNOWN`:

- loops / cyclic CFGs
- floating-point lowering
- richer casts and broader LLVM instruction coverage
- loop invariants and loop summaries
- precise source locations for assertion reports

## How To Run

Compile the fixture corpus and run the CLI on all curated flow fixtures:

```sh
make -C tests smoke
```

Generate LLVM IR and bitcode only:

```sh
make -C tests ir
```

Run the CLI on one bitcode file:

```sh
cargo run --bin main -- tests/out/straight_line_assert.bc
```

Skip DOT generation:

```sh
cargo run --bin main -- --no-dot tests/out/multi_exit.bc
```

Verification:

```sh
cargo fmt
cargo test
make -C tests smoke
```

## CLI Behavior

For each input module, the binary:

- parses the `.bc` file
- builds per-function raw instruction graphs
- optionally writes DOT files under `graph_dot/<input-stem>/`
- prints one brief graph summary per function
- lowers each procedure into the current abstract CFG
- runs the current backward checker where supported
- prints one procedure report with a final `SAFE`, `UNSAFE`, or `UNKNOWN`
  verdict

If one procedure is unsupported, the CLI still reports the remaining
procedures. Unsupported procedures are printed with `verdict: UNKNOWN`.

## Active Architecture

```text
src/llvm_utils/llvm_wrap.rs     -> LLVM C API wrapper boundary
src/llvm_utils/program_graph.rs -> raw instruction graph generation
src/assertions/translation.rs   -> assertion text -> internal formula
src/analysis/formula.rs         -> terms, predicates, rationals, SMT model type
src/analysis/abstract_cfg.rs    -> abstract CFG, transfer effects, WP/SP helpers
src/analysis/adapter.rs         -> FunctionGraph -> AdaptedProcedure lowering
src/analysis/node_summary.rs    -> per-node reach/state summaries
src/analysis/rules.rs           -> local propagation rules over the abstract CFG
src/analysis/backward.rs        -> acyclic backward assertion analysis
src/analysis/oracle.rs          -> SMT feasibility / implication boundary
src/analysis/providers.rs       -> external/manual candidate provider seam
src/analysis/summaries.rs       -> reusable summary table data structures
src/analysis/driver.rs          -> module orchestration and call-summary reuse
src/analysis/source.rs          -> source location value type
src/smt/solver.rs               -> raw Z3 lowering
```

## Loop Support

Loop support is currently structural only.

- The raw LLVM graph and abstract CFG preserve loops.
- The checker requires a topological order and rejects cyclic CFGs.
- In the CLI this becomes a per-assertion unsupported message and a procedure
  verdict of `UNKNOWN`.
- No loop invariant generation, loop summary generation, or bounded unrolling
  is active today.

Observed current behavior on `tests/out/loop_counter.bc`:

- `main` is `SAFE` because it has no assertions.
- `subject` is `UNKNOWN` with `CFG has a cycle; loops are not supported`.
