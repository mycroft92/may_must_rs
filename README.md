# Smash-plus-ultra: Compositional May/Must Assertion Checker

[![Build](https://github.com/mycroft92/Smash-plus-ultra/actions/workflows/build.yml/badge.svg)](https://github.com/mycroft92/Smash-plus-ultra/actions/workflows/build.yml)
[![Tests](https://github.com/mycroft92/Smash-plus-ultra/actions/workflows/tests.yml/badge.svg)](https://github.com/mycroft92/Smash-plus-ultra/actions/workflows/tests.yml)

An LLVM IR implementation of the compositional may/must analysis described in:

> **Compositional May-Must Program Analysis: Unleashing the Power of Alternation**
> Patrice Godefroid, Aditya V. Nori, Sriram K. Rajamani, SaiDeep Tetali
> POPL 2010 — https://dl.acm.org/doi/10.1145/1707801.1706307

Given an LLVM bitcode file, the tool either proves that each assertion
condition always holds on reachable executions or reports a concrete
counterexample.

---

## Quick Start

### Prerequisites

- Rust (stable)
- LLVM 20 with `llvm-config` on `PATH` — including the Polly component:
  ```sh
  # Ubuntu/Debian (via apt.llvm.org)
  sudo apt-get install llvm-20 llvm-20-dev libclang-20-dev libpolly-20-dev clang-20

  # macOS (Homebrew)
  brew install llvm@20
  ```
- Z3 development libraries (used by the SMT oracle):
  ```sh
  # Ubuntu/Debian
  sudo apt-get install libz3-dev

  # macOS (Homebrew)
  brew install z3
  ```
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

Include `verification.h` (at the project root) and use `assert()` and
`assume()`.

```c
#include "verification.h"

int abs(int x) {
    int result = x < 0 ? -x : x;
    assert(result >= 0);
    return result;
}

void bounded(int x) {
    assume(x >= 0 && x < 100);  // prune infeasible paths
    assert(x * x < 10000);      // trivially discharged
}
```

Compile to bitcode and run the checker:

```sh
clang -O0 -g -c -emit-llvm my_file.c -o my_file.bc
cargo run --bin main -- --no-dot my_file.bc
```

Alternatively, pass the header via a compiler flag so existing code needs no
`#include` changes:

```sh
clang -O0 -g -include path/to/verification.h -c -emit-llvm my_file.c -o my_file.bc
```

### How `verification.h` works

The header declares two sentinel functions:
- `may_assert(_Bool)` — redefines `assert(cond)` to call it. The tool strips
  these from the visible CFG, records the condition as a verification
  obligation, and propagates `NOT condition` backward as the violation seed.
- `may_assume(_Bool)` — redefines `assume(cond)` to call it. The tool strips
  these from the visible CFG and injects `TransferEffect::Assume(cond)` on the
  nearest CFG node. In the backward violation analysis, the WP of `Assume(c)`
  is `c AND post`, ensuring that paths where `c` is false (which the assume
  would have pruned) are excluded from the violation precondition.

The tool also natively recognizes three error-termination sentinels without
requiring any header:
- `reach_error()` — SV-COMP unreach-call property marker.
- `__assert_fail(...)` — C standard library assert macro expansion.
- `__VERIFIER_error()` — older SV-COMP error sentinel.

Calls to any of these are treated as `may_assert(false)`: the call site is
stripped from the visible CFG and recorded as an obligation that must be
unreachable. The backward analysis propagates `True` from these sites, so
`reach AND True = reach`; if the path to the call is empty, the result is
`Verified`.

If `<assert.h>` is also included, `verification.h` shadows its `assert`
definition — include `verification.h` last (or first — it unconditionally
`#undef`s `assert`).

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
        cond = false
        flag = true
  verdict: UNSAFE
```

Source locations (`file:line:col`) and source variable names in
counterexamples and loop-invariant logs are reported when the bitcode was
compiled with `-g`.

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

**Loop invariant synthesis** is attempted in order:
1. Entry-safety candidates — mines `counter==init || safety` forms from
   concrete preheader store facts and the assertion postcondition.
2. ACHAR grammar-based ICE learning — enumerates candidates from a vocabulary
   of loop variables and select-terms; filters atoms with positive/negative
   example states from the SMT oracle; generates atoms, pairwise conjunctions,
   observer-style and ICE-guided disjunctions in priority order.

Every candidate must pass all three checks — initiation, inductiveness, and
exit closure against the real assertion postconditions — before reaching the
backward analysis. The `VerifiedLoopInvariant` type enforces this at compile
time. See [design_notes/LOOPS.md](design_notes/LOOPS.md) for how loop
invariants fit into the query-driven architecture, and
[design_notes/SMASH_FORWARD_MUST.md](design_notes/SMASH_FORWARD_MUST.md)
for the directional mapping that makes the soundness story explicit.

**Bounded model checking** (`--bmc-bound N`) unrolls each loop up to N
iterations and runs the backward analysis on the acyclic result. A `BugFound`
result is a real counterexample; absence of a bug within the bound is UNKNOWN.

**Interprocedural reasoning** uses summaries in both directions:
- `ReturnSummary`: relates return values to inputs, inferred by backward WP.
- `SummaryTables`: loop invariants cached per procedure and reused by callers.
- Cyclic callees (looping helpers) are handled via observer-invariant synthesis,
  which finds an inductive invariant `counter ≤ k ∨ accumulator ≥ ext[k]` and
  verifies it with the full bidirectional check.

---

## Architecture

```
src/frontend/llvm_wrap.rs              LLVM C API wrapper (types, opcodes, debug info,
                                        TargetData for struct layout)
src/frontend/program_graph.rs          raw instruction-level FunctionGraph builder
src/frontend/source.rs                 SourceLocation type (file, line, column)
src/frontend/assertions/               assertion/assume expression parser and translator
src/formula/mod.rs                     terms, predicates, memory arrays, SMT model types
src/formula/alpha_rename.rs            two-closure alpha-renaming (var_rename / region_rename)
src/pointer_analysis/andersen.rs       field-sensitive flow-insensitive Andersen alias analysis
src/pointer_analysis/pointer_env.rs    pointer → (region, offset) environment
src/cfg/abstract_cfg.rs                abstract CFG, TransferEffect variants, WP/SP helpers
src/cfg/adapter.rs                     FunctionGraph → AdaptedProcedure lowering
                                        (GEP offsets, per-field struct regions,
                                         vtable fn-ptr resolution, pointer environment,
                                         AA-assisted PointerStore/PointerLoad,
                                         return summary injection, memcpy unrolling)
src/cfg/flat_layout.rs                 flat struct/array layout for GEP offset computation
src/smt/solver.rs                      raw Z3 term/formula lowering
src/smt/oracle.rs                      SMT feasibility / implication (Z3 boundary)
src/analysis/backward/node_summary.rs  per-node (reach, state) summaries
src/analysis/backward/rules.rs         local forward MAY and backward NOT-MAY rules, RuleEngine
src/analysis/backward/mod.rs           assertion checking, loop invariant injection
src/analysis/loops/mod.rs              loop detection, VerifiedLoopInvariant, 3-check verification
src/analysis/invariants/mod.rs         ACHAR CEGIS — vocabulary, atom generation, ICE examples,
                                        tiered candidate search (11 tiers)
src/analysis/dart/mod.rs               forward MUST concrete path exploration (DART)
src/analysis/interproc/summaries.rs    SummaryTables, MaySummary, NotMaySummary
src/analysis/interproc/query.rs        ContextualSummaryTable, query types
src/analysis/interproc/providers.rs    external/manual summary provider seam
src/analysis/interproc/scheduler.rs    demand-driven query worklist
src/analysis/interproc/smash.rs        SMASH bidirectional orchestrator per assertion
src/analysis/interproc/driver.rs       module orchestration, summary inference, report generation
```

---

## What Is Supported

| Feature | Status |
|---|---|
| Integer and boolean scalar reasoning | ✅ |
| `assume(cond)` path-feasibility constraints | ✅ |
| Integer-array memory (`alloca` / `load` / `store` / `gep`) | ✅ |
| Struct field access — stack allocated (`alloca %Foo`) | ✅ |
| Struct field access — C++ stack objects via `*this` | ✅ |
| Type-aware GEP offsets (mixed-width structs, non-i32 arrays) | ✅ |
| `phi` lowering on incoming edges | ✅ |
| Branch-guard lowering | ✅ |
| Acyclic procedure verification | ✅ |
| Cyclic procedures with loop invariant synthesis | ✅ |
| Loop invariants via entry-safety candidates (full exit-closure check) | ✅ |
| Loop invariants via ACHAR grammar-based ICE learning | ✅ |
| Bounded model checking for bug finding (`--bmc-bound N`) | ✅ |
| Interprocedural return-summary inference (acyclic callees) | ✅ |
| Cyclic callee return-summary inference (observer-invariant) | ✅ |
| `llvm.memcpy` / `llvm.memset` unrolling | ✅ |
| Source locations in assertion reports (requires `-g`) | ✅ |
| Readable counterexamples grouped by function | ✅ |
| Source variable names in debug/counterexample output (requires `-g`) | ✅ |
| Floating-point lowering | ❌ |
| Heap-allocated struct reasoning (`malloc` / `new` / `calloc`) | ✅ (call-site abstraction; per-field regions) |
| General cyclic callee summaries (non-observer patterns) | ❌ |
| Alias analysis (flow-insensitive, field-sensitive Andersen) | ✅ |
| Virtual dispatch (same-function vtable resolution) | ✅ (infrastructure done; cross-function limited) |
| Broader cast / instruction coverage | partial |

Unsupported procedures return `UNKNOWN` rather than terminating the run.

See [design_notes/LOOPS.md](design_notes/LOOPS.md) for the loop invariant
checking design under the query-driven architecture,
[design_notes/QUERY_REFACTOR.md](design_notes/QUERY_REFACTOR.md) for the
main analysis architecture, and [REFERENCES.md](REFERENCES.md) for citations.

---

## Verification

After code changes, always run:

```sh
cargo fmt
cargo test
```

Also run when touching CLI behaviour, lowering, or smoke assumptions:

```sh
make -C tests smoke
```
