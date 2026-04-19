Experimental LLVM may-must analysis work. MIT Licensed.

## Current SMASH-Style Implementation

This repository now contains a first LLVM IR implementation of the core
structure from Godefroid, Nori, Rajamani, and Tetali's SMASH paper,
"Compositional May-Must Program Analysis: Unleashing the Power of
Alternation".

The implementation is intentionally a working scaffold, not yet the full
paper implementation. It keeps the paper's query and summary shape, but uses a
bounded symbolic executor over LLVM IR as the current intraprocedural engine.
That makes the system executable now and leaves clear extension points for
predicate abstraction, Z3-backed implication checks, and directed test
generation.

## How To Run

Generate LLVM IR and bitcode from the C test inputs:

```sh
make -C tests ir
```

This writes human-readable `.ll` files and analyzer-ready `.bc` files under
`tests/out/`.
Set `CLANG=/path/to/clang` if you need the generated bitcode to match a
specific LLVM reader version.

Run the minimal SMASH smoke test:

```sh
make -C tests smoke
```

If Cargo cannot access the network and the dependency cache is already present,
use:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

Check embedded `may_assert(...)` calls:

```sh
cargo run --bin main -- tests/out/short_assert.bc
```

Run the experimental SMT-backed path for embedded `may_assert(...)` calls:

```sh
cargo run --bin main -- tests/out/short_assert.bc --engine smt
```

Check a command-line postcondition at function return:

```sh
cargo run --bin main -- tests/out/short_assert.bc -a "main => %23 == 1"
```

Bound symbolic execution work per query:

```sh
cargo run --bin main -- tests/out/short_assert.bc --max-steps 50000
```

Every run writes debug DOT graphs to `graph_dot/<input-stem>/`, one file per
function.

## Results

The CLI prints a reachability query:

```text
Query <main: true => violate:any_may_assert>
```

Then it returns one of:

`SAFE (not-may summary)`: the bounded may side explored the relevant CFG and
did not find a feasible assertion violation.

`BUG reachable (must summary)`: the must side found a concrete symbolic trace
to a violation.

`UNKNOWN`: the current engine could not decide, usually because an assertion
argument stayed symbolic or an execution bound was reached.

## Recent Session Reports

Earlier workflow work made the current SMASH-style prototype easier to
reproduce, test, and resume.

Repository workflow updates:

- added `tests/build_ir.sh` to compile C inputs into human-readable `.ll` files
  and analyzer-ready `.bc` files;
- replaced the old ad hoc `tests/Makefile` targets with `ir`, `smoke`, and
  `clean`;
- added `tests/out/` to `.gitignore` so generated LLVM artifacts stay
  reproducible instead of checked in;
- added `tests/indirect_branch_example.c` so the indirect-branch example has a
  corresponding C source in `tests/`;
- added `TASKVIEW.md` as the resume document for the next implementation
  session against the SMASH paper.

Current smoke coverage:

- `tests/smash_must.c` is the smallest current must-summary example;
- `tests/smash_smoke.sh` builds that C file, runs the analyzer, and checks for:

```text
Query <main: true => violate:any_may_assert>
Result: BUG reachable (must summary)
Summaries: 1 must, 0 not-may
```

Run it with:

```sh
make -C tests smoke
```

The experimental SMT route has its own smoke target:

```sh
make -C tests smt-smoke
```

That target currently checks:

- `tests/smash_must.c`: direct `may_assert(false)` creates a `Must` summary;
- `tests/smt_assert_safe.c`: direct `may_assert(true)` creates a `NotMay`
  summary;
- `tests/smt_assert_branch_prune.c`: SMT branch/path reasoning prunes the
  infeasible assertion-violation path.

Use `CARGO_FLAGS=--offline make -C tests smoke` when the local dependency cache
is available but the network is not.

The April 19, 2026 SMT scaffolding and wiring sessions added a parallel typed
implementation path. The legacy analyzer remains the default, and
`--engine smt` selects the experimental SMT engine:

- added `src/analysis/predicates.rs` with solver-independent `IntTerm` and
  `Formula` types plus SMT-backed satisfiability, entailment, and intersection
  checks;
- added `src/analysis/smt_path.rs` with cloneable path-local state over typed
  formulas, simple stack-memory bindings, formal parameters mapped to
  `SummaryPhase::Pre`, and scalar return relations mapped to
  `SummaryPhase::Post`;
- added `src/analysis/summary_store.rs` with typed `Must` and `NotMay`
  function-boundary summaries, explicit `SummaryTarget`s, and SMT-backed
  applicability checks;
- added `src/analysis/smt_engine.rs` as the analysis coordinator that performs
  the SMASH summary lookup order, runs an intraprocedural worklist for direct
  embedded assertions, and records typed summaries;
- added `src/analysis/transfer.rs` with the first forward SMT transfer layer
  for simple stack `alloca`/`store`/`load`, scalar `add`, `sub`, `mul`,
  `icmp`, conditional/unconditional `br`, and `ret`;
- added Section 2 summary-level tests for Figure 1's not-may summary and
  Figure 2's must summary;
- added `tests/paper_section2_fig1_not_may.c` as a target fixture for future
  direct-call summary composition;
- kept `src/analysis/may_must.rs` intact as the executable toy/reference
  implementation;
- kept `cargo test` green with 35 unit tests.

## What Is Implemented

`src/llvm_utils/program_graph.rs` builds instruction-level CFGs per basic
block:

- adds every instruction as a vertex;
- records function parameters;
- records `may_assert` call instructions as assertion sites;
- adds sequential edges only within a basic block;
- adds terminator-to-successor edges using LLVM successor information;
- records DOT write errors.

`src/llvm_utils/llvm_wrap.rs` exposes the LLVM details needed by the analyzer:

- function parameters;
- instruction and value names;
- operands;
- branch conditions;
- integer constants;
- integer comparison predicates;
- branch, return, and terminator checks.

`src/analysis/domain.rs` defines the paper-level analysis objects:

- `Predicate`: lightweight pre/postcondition representation;
- `Query`: a reachability query `<pre ?=> function post>`;
- `SummaryKind`: `Must` or `NotMay`;
- `Summary`: cached procedure-level result.

`src/analysis/may_must.rs` implements the current SMASH-style engine:

- checks whether an applicable must summary already proves reachability;
- checks whether an applicable not-may summary already proves unreachability;
- otherwise runs bounded symbolic execution;
- creates a must summary when a violation trace is found;
- creates a not-may summary when the bounded exploration completes safely;
- uses summaries demand-driven across procedure calls that may transitively
  reach `may_assert`;
- tracks memory for simple `alloca`/`store`/`load` LLVM IR;
- folds integer arithmetic and comparisons when operands are concrete;
- follows concrete branches precisely and forks on unknown conditions;
- reports `UNKNOWN` instead of pretending safety when bounds or symbolic gaps
  prevent a decision.

`src/analysis/state.rs` and `src/smt/solver.rs` provide the next-stage SMT
building blocks:

- one SMT symbol per immutable LLVM SSA value;
- versioned memory arrays;
- accumulated path assumptions;
- explicit procedure-summary boundary symbols;
- unit-tested Z3 variable creation, assertions, satisfiability checks, and
  model extraction.

The typed SMT-side analysis scaffold is split across:

- `src/analysis/predicates.rs`: cloneable integer terms and Boolean formulas
  that encode into `StateEncoding`;
- `src/analysis/smt_path.rs`: cloneable path-local state, path assumptions,
  return binding, and feasibility checks;
- `src/analysis/summary_store.rs`: function-boundary `Must` and `NotMay`
  summary storage plus SMT-backed applicability checks;
- `src/analysis/smt_engine.rs`: summary-cache orchestration plus the first
  intraprocedural SMT worklist for direct embedded assertions;
- `src/analysis/transfer.rs`: first scalar and simple stack-memory forward
  transfer functions.

These SMT pieces are wired behind `--engine smt`. The default command still
runs `src/analysis/may_must.rs` so the old toy/reference implementation stays
usable while the SMT path is incomplete.

`src/main.rs` invokes the analyzer through the CLI:

- no `-a`: analyze embedded `may_assert(...)` calls;
- with `-a`: analyze the provided assertion at returns from the named function;
- `--engine legacy`: run the existing toy/reference analyzer;
- `--engine smt`: run the experimental SMT-backed analyzer for direct embedded
  assertions;
- always dumps DOT graphs into `graph_dot/<input-stem>/`;
- prints the query, result, trace when available, and summary counts.

## How The Pieces Map To The Paper

Section 2, "Overview", introduces the reachability query
`<phi1 ?=> P phi2>`, where the analysis asks whether some execution of
procedure `P` can start in `phi1` and terminate in `phi2`. That shape is
represented by `Query` in `src/analysis/domain.rs`. At the moment, the
precondition is usually `true`, and the postcondition is a violation predicate
such as `violate:any_may_assert`.

Section 2 also defines not-may summaries and must summaries. These are
represented by `SummaryKind::NotMay` and `SummaryKind::Must`. A must summary is
created when bounded symbolic execution finds a witness trace to the violation.
A not-may summary is created when the bounded may side exhausts all supported
paths without reaching the violation.

Sections 3 and 4 describe the may/must proof rules. This prototype does not yet
implement the paper's full predicate abstraction or DART-style test generation.
Instead, `execute_function` in `src/analysis/may_must.rs` is the current
intraprocedural engine. It evaluates supported LLVM IR instructions, forks on
unknown branch conditions, records path conditions syntactically, and returns
`UNKNOWN` when the supported semantics or configured bounds are insufficient.

Section 4.3, "SMASH: Compositional May-Must Analysis", is the key
correspondence for procedure calls. In this implementation, `transfer_call`
issues a demand-driven query when a callee can transitively reach an embedded
`may_assert`. A callee must summary can make the caller's must side succeed. A
callee not-may summary lets the caller continue without exploring an irrelevant
safe body.

Section 5.1 describes a deterministic implementation order:

1. If an applicable must summary exists, return yes.
2. If an applicable not-may summary exists, return no.
3. Otherwise analyze the procedure and create either a must summary or a
   not-may summary.

`analyze_query` follows that order.

## SMT Solver Status

The paper's Section 5.1 says the original SMASH implementation used Z3 for
predicates over linear arithmetic and uninterpreted functions, with theorem
prover queries deciding satisfiability and validity.

This repository has a Z3 layer in `src/smt/solver.rs`, plus a typed SMT
analysis path under `src/analysis/`. The default CLI analyzer still uses:

- concrete integer folding for LLVM arithmetic and comparisons;
- simple string-backed symbolic values when operands are not concrete;
- syntactic `Predicate::entails` and `Predicate::intersects` checks for summary
  applicability;
- `UNKNOWN` when those lightweight checks are insufficient.

The experimental `--engine smt` path invokes the typed SMT layer for direct
embedded assertions. The SMT layer is deliberately split:

- `Z3Interface` owns the raw Z3 `Solver` and low-level operations such as
  `assert`, `check`, `push`, `pop`, constants, and sorts.
- `SmtEncodingContext` owns analysis-level symbols and caches created Z3
  variables. That is where names such as `%7`, `%7_pre`, `%7_post`, or
  function-scoped symbols should live.
- `StateEncoding` gives transfer/summary code function-scoped SSA,
  memory-version, path-condition, and summary-boundary symbols.
- `predicates.rs` stores terms and formulas independent of a particular Z3
  solver instance.
- `smt_path.rs` carries cloneable symbolic path state and creates fresh SMT
  encodings only when feasibility needs to be checked.
- `summary_store.rs` owns typed procedure summaries and their SMT applicability
  checks.
- `smt_engine.rs` owns analysis-level orchestration. It is separate from
  `solver.rs` because `solver.rs` knows Z3 mechanics, while `smt_engine.rs`
  knows query and summary semantics.

The existing SMT call pattern is:

1. Construct `SmtEncodingContext::new()` for one query, path, or summary
   encoding.
2. Create variables such as `int_var("x")`, `bool_var("b")`, `bv_var("x", 32)`,
   or `array_var(...)` on that encoding context.
3. Build Z3 AST expressions with the `z3` crate methods.
4. Add constraints with `assert(&constraint)` on the encoding context.
5. Call `check()`.
6. If satisfiable, call `get_model()` for the raw Z3 model or
   `get_model_values()` for variables owned by that encoding context.

That pattern is exercised by unit tests in `src/smt/solver.rs`,
`src/analysis/state.rs`, and the SMT analysis modules. The first integration
point now uses `SmtPathState` and `TransferFunctions` from
`SmtAnalysisEngine`, then records `Must` or `NotMay` summaries in
`SummaryStore`.

## Current Limitations

This is not yet the full SMASH algorithm from the paper.

The legacy CLI may side is bounded symbolic execution, not predicate
abstraction. The legacy CLI must side is symbolic trace search, not full
DART-style generated tests. Predicate implication and intersection in the
legacy path are lightweight and mostly syntactic. SMT-backed predicate checks
are used by the experimental `--engine smt` path, but that path is still a
small intraprocedural subset.

Memory modeling is intentionally simplified in the executable SMT path:

- `StateEncoding` already has a versioned SMT-array memory vocabulary and unit
  tests for `store`/`load` composition.
- `SmtPathState`, which is what `--engine smt` currently executes, uses a
  temporary `HashMap<pointer-key, IntTerm>` instead.
- `alloca` is a no-op except that its SSA name can be used as a pointer key.
- `store` writes one integer term to that key.
- `load` reads that key, or creates an uninterpreted scalar `load(key)` term if
  no prior store is known on the path.

This simplification was added so unoptimized LLVM test IR with stack slots can
reach the assertion checks. It does not model aliasing, object identity,
offsets, byte layout, arrays, structs, globals, heap objects, `getelementptr`,
or function-boundary memory summaries.

Unsupported or undecidable cases return `UNKNOWN`. This is deliberate: a
bounded prototype should not report safety when it has only failed to explore
enough.

## Next Work

Use `TASKVIEW.md` as the live resume document for the next implementation
session. The immediate next engineering step is to extend the experimental SMT
engine beyond direct intraprocedural assertions:

1. add focused SMT-engine regression tests;
2. implement direct-call summary composition;
3. support command-line assertions or route them explicitly to legacy only;
4. replace the simple memory map with the planned SMT-array/object memory
   model;
5. add `phi`, `switch`, casts, division/remainder, and `getelementptr`.
