# may-must: Compositional May/Must Assertion Checker

An LLVM IR implementation of the compositional may/must analysis described in:

> **Compositional May-Must Program Analysis: Unleashing the Power of Alternation**  
> Patrice Godefroid, Aditya V. Nori, Sriram K. Rajamani, SaiDeep Tetali  
> POPL 2010 — https://dl.acm.org/doi/10.1145/1707801.1706307

Given an LLVM bitcode file, the tool either proves that each `may_assert`
condition always holds on reachable executions or reports a concrete
counterexample.

---

## Quick Start

### Prerequisites

- Rust (stable)
- LLVM 20/21 with `llvm-config` on `PATH` (the `llvm-sys` crate links against it)
- A C compiler (clang) for recompiling the test fixtures

### Build

```sh
cargo build --release
```

### Run on a single file

```sh
cargo run --bin main -- tests/out/array_max_5.bc
```

Skip DOT graph generation:

```sh
cargo run --bin main -- --no-dot tests/out/loop_counter.bc
```

Show loop invariants and cached summaries:

```sh
cargo run --bin main -- --debug-invariants --show-summaries --no-dot tests/out/loop_counter.bc
```

### Compile and smoke-test the full fixture corpus

```sh
make -C tests smoke
```

This recompiles every `.c` under `tests/flow/` with debug info (`-g`) and
runs the checker on each one, printing a `SAFE` / `UNSAFE` / `UNKNOWN` verdict.

---

## Annotating Your Own Code

Mark assertions with the `may_assert` sentinel (declare it `extern` — the
checker removes it from the visible graph and records the condition as an
obligation):

```c
extern void may_assert(_Bool condition);

int abs(int x) {
    int result = x < 0 ? -x : x;
    may_assert(result >= 0);
    return result;
}
```

Compile to bitcode:

```sh
clang -O0 -g -c -emit-llvm my_file.c -o my_file.bc
cargo run --bin main -- --no-dot my_file.bc
```

---

## Example Output

```
procedure main  [5 assertion(s), 30 instruction(s)]
  assertion #1  tests/flow/array_max_5.c:17:5
    judgement: Verified
  assertion #2  tests/flow/array_max_5.c:18:5
    judgement: Verified
  ...
  verdict: SAFE
```

On a failing assertion:

```
procedure subject  [1 assertion(s), 26 instruction(s)]
  assertion #1  tests/flow/bool_ops.c:12:5
    judgement: UNSAFE
    counterexample:
      [subject]
        %12 = false
        %8 = true
        stack2: all elements = 0
  verdict: UNSAFE
```

---

## How It Works

The tool implements a bidirectional may/must analysis over an abstract CFG
lowered from LLVM IR.

**Forward direction (must / reach):** loop invariants seed the `reach`
overapproximation at loop headers, capturing what states are reachable.

**Backward direction (may / state):** the weakest precondition of
`NOT obligation` is propagated backward through `state`, encoding conditions
under which the assertion could be violated.

**Combined check:** `reach AND state` is queried for SMT feasibility at the
function entry. Infeasible → `Verified`; feasible with a model → `UNSAFE`;
indeterminate → `UNKNOWN`.

Interprocedural reasoning uses summaries in both directions:
- `ReturnSummary`: relates return values to inputs, inferred by backward WP.
- `SummaryTables`: loop invariants cached per procedure and reused by callers.
- Cyclic callees (looping helpers) are handled via observer-invariant synthesis,
  which finds an inductive loop invariant of the form
  `counter ≤ k ∨ accumulator ≥ ext[k]` and verifies it with the full
  bidirectional check.

---

## Architecture

```
src/llvm_utils/llvm_wrap.rs        LLVM C API wrapper (debug info, opcodes, operands)
src/llvm_utils/program_graph.rs    raw instruction-level FunctionGraph
src/common/formula.rs              terms, predicates, memory arrays, SMT model types
src/common/abstract_cfg.rs         abstract CFG nodes/edges, transfer effects, WP
src/common/adapter.rs              FunctionGraph → AdaptedProcedure lowering
src/common/oracle.rs               SMT feasibility / implication (Z3 boundary)
src/may_must_analysis/node_summary.rs  per-node (reach, state) summaries
src/may_must_analysis/rules.rs         local propagation rules, RuleEngine
src/may_must_analysis/backward.rs      assertion checking, loop invariant search
src/may_must_analysis/loops.rs         loop detection, invariant checking
src/may_must_analysis/driver.rs        module orchestration, summary caching
src/may_must_analysis/providers.rs     external/manual summary provider seam
src/may_must_analysis/summaries.rs     summary table data structures
src/smt/solver.rs                  raw Z3 lowering
```

---

## What Is Supported

| Feature | Status |
|---|---|
| Integer and boolean scalar reasoning | ✅ |
| Integer-array memory (`alloca` / `load` / `store` / `gep`) | ✅ |
| `phi` lowering on incoming edges | ✅ |
| Branch-guard lowering | ✅ |
| Acyclic procedure verification | ✅ |
| Cyclic procedures with loop invariant synthesis | ✅ |
| Interprocedural return-summary inference (acyclic callees) | ✅ |
| Cyclic callee return-summary inference (observer-invariant) | ✅ |
| `llvm.memcpy` / `llvm.memset` unrolling | ✅ |
| Source locations in assertion reports (requires `-g`) | ✅ |
| Readable counterexamples grouped by function | ✅ |
| Floating-point lowering | ❌ |
| General cyclic callee summaries (non-observer patterns) | ❌ |
| Source-coordinate reporting without `-g` | ❌ |
| Broader cast / instruction coverage | partial |

Unsupported procedures return `UNKNOWN` rather than terminating the run.

---

## Verification

After code changes, always run:

```sh
cargo fmt
cargo test
make -C tests smoke
```
