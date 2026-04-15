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

## What Was Wrong Before

The original codebase had useful LLVM wrappers and a graph dumper, but the
actual analysis modules were mostly empty.

The CFG builder had a correctness bug: it carried `prev` across basic-block
boundaries. That added fallthrough edges from a terminator in one block to the
first instruction of the next block in module order, even when LLVM control
flow did not allow that edge. Reachability analysis over that graph would be
unsound because it could explore paths that do not exist.

The builder also skipped `may_assert` calls and stored only the assertion
argument. That was enough to remember that an assertion existed, but not enough
to evaluate it at the correct program point with the correct symbolic state.

The LLVM wrapper methods for branch, return, and terminator checks treated the
result of `LLVMIsA*` as a constant integer. These APIs return a nullable LLVM
value reference. The correct test is only whether the pointer is null.

While verifying this implementation, one more LLVM API issue surfaced: calling
`LLVMGetCondition` on an unconditional branch exits abnormally. The analyzer now
checks the branch successor count first and asks LLVM for a condition only on
conditional branches.

LLVM unnamed temporaries such as `%23` do not always have a value name from
`LLVMGetValueName2`. The symbolic evaluator now falls back to parsing the
assignment name from the printed instruction, so operands that refer to unnamed
instructions can still resolve to values already computed in the symbolic
state.

## What Was Corrected

`src/llvm_utils/program_graph.rs` now builds instruction-level CFGs per basic
block:

- adds every instruction as a vertex;
- records function parameters;
- records `may_assert` call instructions as assertion sites;
- adds sequential edges only within a basic block;
- adds terminator-to-successor edges using LLVM successor information;
- reports DOT write errors instead of ignoring them.

`src/llvm_utils/llvm_wrap.rs` now exposes the LLVM details needed by the
analyzer:

- function parameters;
- instruction and value names;
- operands;
- branch conditions;
- integer constants;
- integer comparison predicates;
- corrected branch, return, and terminator tests.

`src/analysis/domain.rs` now defines the paper-level analysis objects:

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

`src/main.rs` now invokes the analyzer instead of only dumping graphs:

- no `-a`: analyze embedded `may_assert(...)` calls;
- with `-a`: analyze the provided assertion at returns from the named function;
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

This repository has a Z3 layer in `src/smt/solver.rs`, but the current
SMASH-style analyzer does not yet invoke it. The analyzer currently uses:

- concrete integer folding for LLVM arithmetic and comparisons;
- simple string-backed symbolic values when operands are not concrete;
- syntactic `Predicate::entails` and `Predicate::intersects` checks for summary
  applicability;
- `UNKNOWN` when those lightweight checks are insufficient.

The SMT layer is deliberately split:

- `Z3Interface` owns the raw Z3 `Solver` and low-level operations such as
  `assert`, `check`, `push`, `pop`, constants, and sorts.
- `SmtEncodingContext` owns analysis-level symbols and caches created Z3
  variables. That is where names such as `%7`, `%7_pre`, `%7_post`, or
  function-scoped symbols should live.

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

Today that pattern is exercised only by unit tests in `src/smt/solver.rs`.
The next integration point is to create an `SmtEncodingContext` from
`analysis::may_must` when deciding `Predicate::entails`,
`Predicate::intersects`, and path feasibility in `with_condition`.

## Current Limitations

This is not yet the full SMASH algorithm from the paper.

The current may side is bounded symbolic execution, not predicate abstraction.
The current must side is symbolic trace search, not full DART-style generated
tests. Predicate implication and intersection are lightweight and mostly
syntactic; the existing Z3 wrapper is not yet integrated into summary
applicability or path feasibility.

Memory modeling is intentionally simple. It handles common unoptimized LLVM IR
patterns with `alloca`, `store`, and `load`, but not full aliasing, heap objects,
struct fields, arrays, or pointer arithmetic.

Unsupported or undecidable cases return `UNKNOWN`. This is deliberate: a
bounded prototype should not report safety when it has only failed to explore
enough.

## Next Work

Use `TASKVIEW.md` as the live resume document for the next implementation
session. The immediate next engineering step is to extract LLVM instruction
semantics from `src/analysis/may_must.rs` into `src/analysis/transfer.rs`
without changing behavior. After that, the planned direction is to wire
`src/analysis/state.rs` and `src/smt/solver.rs` into path feasibility and
summary applicability.
