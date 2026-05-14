Experimental LLVM assertion checker work. MIT licensed.

## Current Status

The active implementation is no longer the earlier `cfg/state/loops/transfer`
paper tree. The current CLI-active path is:

`LLVM bitcode -> FunctionGraph -> AbstractCfg -> backward may/must safety check`

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
- cyclic-CFG checking when a loop invariant is accepted
- algorithmic loop-invariant discovery plus CHC/Houdini/template/LLM candidate
  plumbing
- simple interprocedural return-summary inference and reuse for direct calls
- cached loop invariants in summary tables
- best-effort CLI reporting: unsupported procedures return `UNKNOWN` instead of
  terminating the whole run
- curated smoke corpus under `tests/flow/`

Implemented but not CLI-active:

- assertion text translation in `src/assertions/translation.rs`
- manual/external summary provider seam in `src/may_must_analysis/providers.rs`
- source-location carrier types; LLVM debug-location extraction is not wired

Unsupported and reported as `UNKNOWN`:

- cyclic procedures where no invariant candidate is accepted
- floating-point lowering
- richer casts and broader LLVM instruction coverage
- loop summaries for cyclic return-summary inference
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

Show invariant debugging and cached summaries:

```sh
cargo run --bin main -- --debug-invariants --show-summaries --no-dot tests/out/loop_counter.bc
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
src/common/assertions/translation.rs -> assertion text -> internal formula
src/common/formula.rs                -> terms, predicates, rationals, SMT model type
src/common/abstract_cfg.rs           -> abstract CFG, transfer effects, WP/SP helpers
src/common/adapter.rs                -> FunctionGraph -> AdaptedProcedure lowering
src/may_must_analysis/node_summary.rs -> per-node reach/state summaries
src/may_must_analysis/rules.rs        -> local propagation rules
src/may_must_analysis/backward.rs     -> assertion checking + loop invariant search
src/common/oracle.rs                  -> SMT feasibility / implication boundary
src/may_must_analysis/providers.rs    -> external/manual candidate provider seam
src/may_must_analysis/summaries.rs    -> reusable summary table data structures
src/may_must_analysis/driver.rs       -> module orchestration and call-summary reuse
src/common/source.rs                  -> source location value type
src/smt/solver.rs               -> raw Z3 lowering
```

## Loop Support

Loop support is invariant-driven and still partial.

- The raw LLVM graph and abstract CFG preserve loops.
- The driver first precomputes algorithmic loop invariants for cyclic
  procedures.
- Per assertion, the checker can search algorithmic, CHC, Houdini, template,
  and optional LLM candidates.
- `--debug-invariants` logs generated candidates and accepted invariants.
- `--show-summaries` prints cached loop invariants alongside return summaries.
- If no invariant is accepted, the procedure remains `UNKNOWN`.

Observed current behavior on `tests/out/loop_counter.bc`:

- `main` is `SAFE` because it has no assertions.
- `subject` logs the generated loop candidates and currently reports `UNSAFE`.
