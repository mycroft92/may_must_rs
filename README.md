# may-must: Compositional May/Must Assertion Checker

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

Include `verification.h` (at the project root) and use the standard `assert()`
macro. The checker recognises `assert` calls, strips them from the visible CFG,
and records each condition as a formal verification obligation.

```c
#include "verification.h"

int abs(int x) {
    int result = x < 0 ? -x : x;
    assert(result >= 0);
    return result;
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

The header declares a sentinel function `may_assert(_Bool)` and redefines
`assert(cond)` to call it. The tool detects direct calls to `may_assert`,
extracts the asserted condition, and verifies it. If `<assert.h>` is also
included, `verification.h` shadows its `assert` definition — include
`verification.h` last (or first — it unconditionally `#undef`s `assert`).

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

Source locations (`file:line:col`) are reported when the bitcode was compiled
with `-g`.

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
1. Algorithmic pattern matching (counter bounds from back-edge guards).
2. Constrained Horn Clause (CHC) solving via Z3's SPACER engine.
3. Houdini weakening — a large template set is pruned to an inductive subset.
4. LLM-guided CEGIS (optional, when an LLM provider is configured).

**Interprocedural reasoning** uses summaries in both directions:
- `ReturnSummary`: relates return values to inputs, inferred by backward WP.
- `SummaryTables`: loop invariants cached per procedure and reused by callers.
- Cyclic callees (looping helpers) are handled via observer-invariant synthesis,
  which finds an inductive invariant `counter ≤ k ∨ accumulator ≥ ext[k]` and
  verifies it with the full bidirectional check.

---

## Architecture

```
src/common/llvm_utils/llvm_wrap.rs     LLVM C API wrapper (types, opcodes, debug info,
                                        TargetData for struct layout)
src/common/llvm_utils/program_graph.rs raw instruction-level FunctionGraph builder
src/common/source.rs                   SourceLocation type (file, line, column)
src/common/formula.rs                  terms, predicates, memory arrays, SMT model types
src/common/abstract_cfg.rs             abstract CFG, TransferEffect variants, WP/SP
src/common/adapter.rs                  FunctionGraph → AdaptedProcedure lowering
                                        (GEP offsets, per-field struct regions,
                                         pointer environment resolution,
                                         return summary injection, memcpy unrolling)
src/common/oracle.rs                   SMT feasibility / implication (Z3 boundary)
src/may_must_analysis/node_summary.rs  per-node (reach, state) summaries
src/may_must_analysis/rules.rs         local backward propagation rules, RuleEngine
src/may_must_analysis/loops.rs         loop detection, invariant checking (initiation,
                                        inductiveness, exit closure), Houdini candidates,
                                        CHC candidates, algorithmic candidates
src/may_must_analysis/chc.rs           Constrained Horn Clause encoding and Z3 SPACER
                                        solver integration for loop invariants
src/may_must_analysis/backward.rs      assertion checking, loop invariant synthesis
                                        (algorithmic → CHC → Houdini → LLM CEGIS)
src/may_must_analysis/driver.rs        module orchestration, bottom-up summary
                                        accumulation, observer-invariant synthesis
src/may_must_analysis/summaries.rs     SummaryTables and MustSummary data structures
src/may_must_analysis/providers.rs     external/manual summary provider seam
src/may_must_analysis/llm_provider.rs  LLM-guided CEGIS candidate generation
src/common/smt/solver.rs               raw Z3 term/formula lowering
```

---

## What Is Supported

| Feature | Status |
|---|---|
| Integer and boolean scalar reasoning | ✅ |
| Integer-array memory (`alloca` / `load` / `store` / `gep`) | ✅ |
| Struct field access — stack allocated (`alloca %Foo`) | ✅ |
| Struct field access — C++ stack objects via `*this` | ✅ |
| Type-aware GEP offsets (mixed-width structs, non-i32 arrays) | ✅ |
| `phi` lowering on incoming edges | ✅ |
| Branch-guard lowering | ✅ |
| Acyclic procedure verification | ✅ |
| Cyclic procedures with loop invariant synthesis | ✅ |
| Loop invariants via algorithmic pattern matching | ✅ |
| Loop invariants via CHC / Z3 SPACER | ✅ |
| Loop invariants via Houdini weakening | ✅ |
| Loop invariants via LLM-guided CEGIS | ✅ (requires LLM provider) |
| Interprocedural return-summary inference (acyclic callees) | ✅ |
| Cyclic callee return-summary inference (observer-invariant) | ✅ |
| `llvm.memcpy` / `llvm.memset` unrolling | ✅ |
| Source locations in assertion reports (requires `-g`) | ✅ |
| Readable counterexamples grouped by function | ✅ |
| Floating-point lowering | ❌ |
| Heap-allocated struct reasoning (`malloc` / `new`) | ❌ (Step 4) |
| General cyclic callee summaries (non-observer patterns) | ❌ |
| Alias analysis | ❌ (Step 4 prerequisite) |
| Virtual dispatch | ❌ (Step 5) |
| Broader cast / instruction coverage | partial |

Unsupported procedures return `UNKNOWN` rather than terminating the run.

See [MEMORY_MODEL.md](MEMORY_MODEL.md) for the full roadmap and [REFERENCES.md](REFERENCES.md) for citations.

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
