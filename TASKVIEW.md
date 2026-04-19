# Tomorrow Task View: SMT-Backed SMASH Path

This is the resume point for the next session. The project target remains the
SMASH paper by Godefroid, Nori, Rajamani, and Tetali:

<https://dl.acm.org/doi/10.1145/1706299.1706307>

## Current Working Baseline

- The default CLI path is still the legacy toy/reference analyzer:

```sh
cargo run --bin main -- <bitcode.bc>
```

- The experimental SMT path is available with:

```sh
cargo run --bin main -- <bitcode.bc> --engine smt
```

- The default analyzer is still `src/analysis/may_must.rs`.
- `may_must.rs` is intentionally still the toy/reference implementation:
  - string-backed symbolic values;
  - simple `HashMap<String, String>` memory;
  - syntactic path contradictions;
  - syntactic summary applicability;
  - bounded worklist search.
- The SMT-backed path is now wired behind `--engine smt` for direct embedded
  `may_assert` queries.
- The SMT path does not yet support command-line `--assert`, direct-call
  summary composition, `phi`, `switch`, casts, `getelementptr`, or full memory
  summaries.
- Current test status after adding the independent `analysis2` scaffold:

```sh
cargo test
# 37 passed
```

Smoke status:

```sh
make -C tests smoke
# legacy default passes

cargo run -- tests/out/smash_must.bc --engine smt
# SMT engine also reports the direct may_assert(false) bug

make -C tests smt-smoke
# SMT bug, safe/not-may, and branch-pruning smoke cases pass
```

## What Was Added In The SMT Scaffold

`src/analysis/predicates.rs`

- Defines solver-independent `IntTerm` and `Formula`.
- Encodes formulas into `StateEncoding`.
- Provides SMT-backed:
  - `is_satisfiable_in`;
  - `entails_in`;
  - `intersects_in`.

`src/analysis/smt_path.rs`

- Defines cloneable `SmtPathState`.
- Carries:
  - integer SSA bindings;
  - Boolean SSA bindings;
  - simple stack-memory integer bindings;
  - path conditions;
  - scalar return value;
  - trace strings.
- Important simplification: executable SMT memory is currently a
  `HashMap<pointer-key, IntTerm>`, not the final SMT-array/object memory model.
  It exists so unoptimized `alloca`/`store`/`load` test IR can reach assertions.
  It does not model aliasing, offsets, globals, heap objects, structs, arrays,
  or function-boundary memory summaries.
- Maps formal parameters to `SummaryPhase::Pre`.
- Builds scalar return relations against `SummaryPhase::Post`.
- Checks path feasibility with Z3.

`src/analysis/summary_store.rs`

- Defines typed `FunctionSummary`, `SummaryTarget`, `SummaryEvidence`, and
  `SmtQuery`.
- Stores only `Must` and `NotMay` summaries.
- Uses SMT-backed applicability checks.
- Does not store separate May summaries.

`src/analysis/smt_engine.rs`

- Defines `SmtAnalysisEngine` and `SmtEngineConfig`.
- Owns summary storage.
- Implements the SMASH summary lookup order:
  1. applicable `Must`;
  2. applicable `NotMay`;
  3. otherwise execute the supported intraprocedural subset.
- Owns the first SMT worklist for direct embedded `may_assert` queries.
- Records `Must` summaries on feasible assertion violations.
- Records `NotMay` summaries only when all supported paths complete.
- Returns `UNKNOWN` when an unsupported instruction blocks coverage.

`src/analysis/transfer.rs`

- Defines the first SMT forward transfer layer.
- Supports:
  - simple `alloca`;
  - simple `store`;
  - simple `load`;
  - scalar `add`;
  - scalar `sub`;
  - scalar `mul`;
  - `icmp`;
  - unconditional `br`;
  - conditional `br` with SMT pruning;
  - scalar `ret`.
- Unsupported instructions return explicit `TransferError`.

`src/analysis/may_must_rules.rs`

- Contains the first explicit named-rule layer that keeps the code close to the
  SMASH paper.
- It is a facade over `predicates.rs` and `summary_store.rs`, not a new solver
  or executor.
- It currently implements named summary applicability checks.

Section 2 target examples now present:

- `src/analysis/smt_engine.rs` has unit tests for Figure 1's not-may summary
  for `g` and Figure 2's must summary for `f`.
- `tests/paper_section2_fig1_not_may.c` is a future direct-call composition
  fixture for Figure 1.
- Figures 3 and 4 are intentionally not added yet because they rely on
  pre-existing/external `bar` summaries.

## What Was Added In The Paper-Shaped `analysis2` Scaffold

`src/analysis2` is a new development line for mapping the SMASH paper
one-to-one into code. It is intentionally independent from `src/analysis`:

```text
analysis  = current executable prototype and SMT-backed experiment
analysis2 = paper-vocabulary scaffold for explicit rules
```

The new tree currently contains:

- `src/analysis2/vocabulary.rs`: procedure, node, edge, and region IDs.
- `src/analysis2/formula.rs`: solver-independent predicates over state sets.
- `src/analysis2/oracle.rs`: abstract predicate and transition oracles.
- `src/analysis2/llvm_adapter.rs`: Option A bridge from `FunctionGraph` to
  paper edges plus external `EdgeId -> LlvmEdgeMetadata`.
- `src/analysis2/cfg.rs`: paper-shaped procedures, edges, and `Gamma_e`.
- `src/analysis2/state.rs`: `Pi_n`, `Omega_n`, regions, and may edges.
- `src/analysis2/summaries.rs`: paper-style reachability queries plus `Must`
  and `NotMay` summaries.
- `src/analysis2/transfer.rs`: LLVM-backed `TransitionOracle` and
  `LlvmEdgeTransfer` interface over adapter metadata.
- `src/analysis2/rules.rs`: explicit named rule functions:
  - `must_post_edge`;
  - `not_may_pre_edge`;
  - `must_post_use_summary`;
  - `not_may_pre_use_summary`;
  - `applicable_must_summary`;
  - `applicable_not_may_summary`;
  - `create_must_summary`;
  - `create_not_may_summary`.
- `src/analysis2/driver.rs`: deterministic summary-reuse order before
  intraprocedural analysis.
- `src/analysis2/design.md`: the paper-to-code map for the new tree.

The key difference from `src/analysis/may_must_rules.rs` is that
`analysis2::rules::must_post_edge` is the paper's transition rule:

```text
Omega_n1 + Gamma_e -> theta -> Omega_n2
```

It is not just a cached-summary postcondition applicability check.

## Important Design Decisions

Use one forward transfer layer.

Do not build separate pre-transfer and post-transfer implementations. Each
instruction transfer consumes one `SmtPathState` and returns the next
`SmtPathState`:

```text
state_before_instruction -> state_after_instruction
```

`SummaryPhase::Pre` and `SummaryPhase::Post` are function-boundary concepts,
not per-instruction transfer modes. A function summary relation is assembled at
return or violation boundaries, for example:

```text
Post.ret == term_built_from_Pre.params_and_path_constraints
```

Keep `src/analysis/may_must.rs` intact for now.

The current CLI is useful as executable documentation and regression coverage.
The SMT path should become independently tested before replacing or integrating
with the CLI path.

Do not add May summaries.

Persist only:

```text
Must   : there exists a witness path
NotMay : no supported path reaches the queried target
```

May analysis is an internal process that can produce a `NotMay` proof. A saved
May summary is not useful for answering the top-level query.

Use `analysis2` for paper-shaped rules before deepening the engine.

The goal is not to invent extra abstraction. The old SMT path can stay
executable while the new tree makes the paper mapping explicit:

```text
src/analysis        -> working prototype/SMT experiment
src/analysis2       -> paper-shaped rules and state
analysis2/rules.rs  -> named paper obligations
analysis2/state.rs  -> Pi_n, Omega_n, and may edges
analysis2/cfg.rs    -> Gamma_e and graph shape
analysis2/oracle.rs -> abstract set and transition queries
analysis2/llvm_adapter.rs -> FunctionGraph -> (PaperProcedure, metadata table)
analysis2/transfer.rs -> metadata-backed transition oracle
```

Current `analysis2` rule functions:

```text
must_post_edge
not_may_pre_edge
must_post_use_summary
not_may_pre_use_summary
applicable_must_summary
applicable_not_may_summary
```

Keep the summary-applicability directions marked for review until checked
against the SMASH paper.

## Commands To Re-Establish Context

Run Rust tests:

```sh
cargo test
```

Generate C test bitcode and readable LLVM IR:

```sh
make -C tests ir
```

Run the existing CLI smoke test:

```sh
make -C tests smoke
```

Use offline cargo if network is unavailable:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

Run the default legacy analyzer directly:

```sh
cargo run --bin main -- tests/out/short_assert.bc
```

Run the experimental SMT analyzer directly:

```sh
cargo run --bin main -- tests/out/short_assert.bc --engine smt
```

## Files To Start With Tomorrow

- `src/analysis2/design.md`: read this first for the new paper-shaped track.
- `src/analysis2/rules.rs`: continue making SMASH rules explicit.
- `src/analysis2/state.rs`: extend `Pi_n`, `Omega_n`, and region-splitting
  support.
- `src/analysis2/cfg.rs`: clarify local, branch, call, and return edge
  semantics in terms of `Gamma_e`.
- `src/analysis2/oracle.rs`: add the future SMT-backed oracle boundary.
- `src/analysis2/llvm_adapter.rs`: extend edge metadata and conversion from
  LLVM instruction graph.
- `src/analysis2/transfer.rs`: improve post/pre approximations beyond current
  syntactic guard/effect model.
- `src/analysis/smt_engine.rs`: extend the first worklist beyond direct
  intraprocedural assertions.
- `src/analysis/may_must_rules.rs`: review and extend explicit named rule
  functions before wiring deeper summary logic into the engine.
- `src/analysis/transfer.rs`: add missing LLVM instruction semantics only when
  the engine needs them.
- `src/analysis/smt_path.rs`: entry states, feasibility, branch states, return
  relations, and the current simple memory bindings.
- `src/analysis/memory_updates.md`: concrete plan to remove the temporary
  map-based SMT memory and route memory terms through `StateEncoding`.
- `src/analysis/summary_store.rs`: record and query `Must`/`NotMay` summaries.
- `src/analysis/predicates.rs`: extend formulas only if the scalar worklist
  needs a missing term or connective.
- `src/llvm_utils/program_graph.rs`: use `FunctionGraph::start`, `edges`, and
  `params`.
- `src/llvm_utils/llvm_wrap.rs`: use existing instruction wrappers; add new
  wrappers only when the SMT worklist really needs them.
- `src/analysis/may_must.rs`: reference behavior only; avoid changing it during
  the first SMT worklist pass.

## Tomorrow's Task List

1. Continue the paper-shaped `analysis2` track until the rules map cleanly.
   - Keep it independent from `src/analysis`.
   - Keep Option A split: `PaperEdge` LLVM-agnostic, metadata in external
     `EdgeId -> LlvmEdgeMetadata`.
   - Add the intraprocedural worklist over `Pi_n`, `Omega_n`, and `N_e`.
   - Apply `must_post_edge` to update `Omega_n2`.
   - Apply `not_may_pre_edge` to refine `Pi_n1`.
   - Add tests that name the paper symbols directly.

2. Start the memory migration described in `src/analysis/memory_updates.md`
   only after the `analysis2` rule shape is comfortable.
   - Add solver-independent `MemoryTerm` and `IntTerm::Load`.
   - Encode memory terms through `StateEncoding`.
   - Replace `SmtPathState`'s `HashMap<pointer-key, IntTerm>` memory with a
     current memory term.
   - Update `store`/`load` transfer to construct memory terms instead of using
     pointer-key map lookups.
   - Keep `cargo test` and `make -C tests smt-smoke` green.

3. Add the next focused regression coverage for the SMT CLI path.
   - Unsupported `phi`, `switch`, or non-`may_assert` call returns `UNKNOWN`.
   - Direct-call Figure 1 stays expected-unsupported until call summaries are
     implemented.

4. Review `src/analysis/may_must_rules.rs` against the SMASH paper.
   - Confirm or correct the current `must_pre` direction.
   - Confirm or correct the current `must_post` intersection check.
   - Confirm or correct the `not_may_pre` and `not_may_post` directions.
   - Keep the rule module as a facade over formulas and summaries only.
   - Do not add raw Z3 or LLVM transfer logic here.

5. Start direct-call summary composition in the SMT path.
   - Detect non-`may_assert` calls in `smt_engine.rs`.
   - Query the callee with actual/formal parameter binding.
   - Instantiate callee `Must` and `NotMay` summaries in the caller context.
   - Return `UNKNOWN` for recursion until a specific recursive strategy exists.

6. Decide how command-line assertions should enter the SMT path.
   - Either translate `expressions::Expr` into `Formula`.
   - Or keep `--assert` explicitly legacy-only until return-query summaries are
     implemented.

7. Keep existing regressions green.

```sh
cargo test
make -C tests smoke
```

## First Concrete Commit Tomorrow

Target a small commit that advances the paper-shaped scaffold without changing
the legacy default:

- add an `analysis2` intraprocedural driver skeleton over `Pi_n`, `Omega_n`,
  and `N_e`;
- add tests for `MUST-POST` and `NOTMAY-PRE` with explicit `Gamma_e`, `theta`,
  and `beta` names;
- keep `analysis2` independent from `src/analysis`;
- keep `cargo test` passing.

The follow-up commit can remove the temporary SMT memory map:

- implement `MemoryTerm` and `IntTerm::Load`;
- route `store`/`load` transfer through solver-independent memory terms;
- delete `SmtPathState`'s map-based memory helpers;
- add focused memory-term tests;
- review and adjust explicit named summary applicability rules if needed;
- keep `cargo test` passing.

Do not add direct-call composition, `phi`, or `switch` in that commit unless
the memory migration is already passing cleanly.

## Follow-On Work After The Scalar SMT Worklist

1. Create `docs/llvm-transfer-semantics.md`.
2. Add `getelementptr` or return `UNKNOWN` for it explicitly.
3. Finish direct-call summary composition:
   - actual/formal binding;
   - callee return to caller result;
   - assertion inside callee;
   - recursion returns `UNKNOWN`.
4. Consider making `--engine smt` the default only after direct calls,
   command-line assertions, and core memory behavior are tested.

## Design Guardrails

- Do not claim full SMASH until predicate abstraction, DART-style must
  generation, and full summary checks exist.
- Prefer `UNKNOWN` over unsound `SAFE`.
- Keep generated `.ll`, `.bc`, and DOT files ignored and reproducible.
- Keep test C inputs in `tests/`; generated files belong in `tests/out/`.
- Keep `may_must.rs` stable until the SMT engine has its own regression tests.
