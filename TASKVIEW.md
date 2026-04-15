# Tomorrow Task View: SMASH Implementation

This is the resume point for the next session. The project target is the SMASH
paper by Godefroid, Nori, Rajamani, and Tetali:

<https://dl.acm.org/doi/10.1145/1706299.1706307>

## Current Working Baseline

- The active implementation is `src/analysis/may_must.rs`.
- The active CLI path is `cargo run --bin main -- <bitcode.bc>`.
- The analyzer currently implements a SMASH-shaped control flow:
  - build a query `<pre ?=> function post>`;
  - check applicable must summaries first;
  - check applicable not-may summaries second;
  - otherwise run bounded symbolic execution;
  - create a must summary for a found violation trace;
  - create a not-may summary after complete bounded safe exploration.
- This is not yet the full paper algorithm:
  - may analysis is bounded symbolic execution, not predicate abstraction;
  - must analysis is symbolic trace search, not DART-style generated tests;
  - predicate implication/intersection is syntactic, not Z3-backed;
  - procedure-call composition only asks whether callees can reach embedded
    `may_assert`, and does not yet bind actual/formal parameters or returns.

## Commands To Re-Establish Context

Generate C test bitcode and readable LLVM IR:

```sh
make -C tests ir
```

Run the minimal SMASH smoke test:

```sh
make -C tests smoke
```

Use offline cargo if network is unavailable:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

Run the existing Rust tests:

```sh
cargo test
```

Run the analyzer directly on the simple known-safe example:

```sh
cargo run --bin main -- tests/out/short_assert.bc
```

## Files To Start With

- `src/analysis/may_must.rs`: active bounded SMASH-style analyzer.
- `src/analysis/domain.rs`: `Predicate`, `Query`, `Summary`, and
  `SummaryKind`.
- `src/analysis/state.rs`: SMT state vocabulary that is tested but not wired
  into `may_must.rs`.
- `src/smt/solver.rs`: low-level Z3 wrapper and symbol-owning
  `SmtEncodingContext`.
- `tests/smash_must.c`: smallest must-summary example.
- `tests/smash_smoke.sh`: CLI smoke test for the current analyzer.
- `tests/build_ir.sh`: C-to-LLVM utility.

## Tomorrow's Task List

1. Make test execution boring.
   - Keep `make -C tests smoke` green.
   - Add a matching not-may smoke test with `may_assert(1)`.
   - Add one `UNKNOWN` smoke test with a symbolic assertion argument.
   - Decide whether these stay shell tests or become Rust integration tests.

2. Add `src/analysis/transfer.rs` as a thin extraction from `may_must.rs`.
   - Move scalar arithmetic transfer first.
   - Move `icmp` transfer second.
   - Move `alloca`/`store`/`load` third.
   - Preserve the existing string-based behavior while extracting.
   - Keep `may_must.rs` responsible for worklist/search/summary logic.

3. Introduce a typed transfer result.
   - Define `TransferResult::{Continue, Return, Bug, Unknown}` or equivalent
     in the transfer layer.
   - Return `Unknown` explicitly for unsupported instructions instead of
     silently ignoring most opcodes.
   - Add tests for unsupported `phi`, `switch`, and indirect branch behavior.

4. Wire `StateEncoding` into one tiny path.
   - Start with straight-line integer arithmetic only.
   - Encode `%x = add ...` using `StateEncoding::bind_ssa_int`.
   - Use Z3 to prove a tiny branch/path condition is infeasible.
   - Do not attempt full memory or calls in this step.

5. Replace `with_condition` with Z3-backed feasibility.
   - Represent branch assumptions in `StateEncoding`.
   - Check `SAT(path & cond)` and `SAT(path & !cond)`.
   - Prune infeasible successors.
   - Return `UNKNOWN` only when condition encoding is unsupported.

6. Define real summary applicability checks.
   - Replace syntactic `Predicate::entails` with an SMT validity check:
     `UNSAT(a & !b)`.
   - Replace syntactic `Predicate::intersects` with an SMT satisfiability
     check: `SAT(a & b)`.
   - Re-check the must/not-may entailment directions against the SMASH rules
     before finalizing.

7. Improve procedure-call composition.
   - Bind caller actual arguments to callee formal parameters.
   - Bind callee return value to caller result.
   - Add a minimal direct-call test where the assertion is inside the callee.
   - Keep recursive calls returning `UNKNOWN` until a fixed-point strategy is
     chosen.

8. Document LLVM transfer semantics.
   - Create `docs/llvm-transfer-semantics.md`.
   - Cover scalar operations, comparisons, memory, branches, returns, calls,
     unsupported instructions, and soundness assumptions.
   - Treat this as the implementation contract for `transfer.rs`.

## First Concrete Commit Tomorrow

Target a small commit:

- add `src/analysis/transfer.rs`;
- move only arithmetic and `icmp` transfer out of `may_must.rs`;
- keep `make -C tests smoke` passing;
- keep `cargo test` passing.

That commit should not introduce SMT into the main analyzer yet. The goal is to
separate responsibilities before changing semantics.

## Design Guardrails

- Do not claim full SMASH until predicate abstraction, DART-style must
  generation, and SMT summary checks exist.
- Prefer `UNKNOWN` over unsound `SAFE`.
- Keep generated `.ll`, `.bc`, and DOT files ignored and reproducible.
- Keep test C inputs in `tests/`; generated files belong in `tests/out/`.
- Preserve current CLI behavior while refactoring internals.
