# TODO: Remaining SMASH Implementation Work

This file tracks what is still missing compared with the SMASH paper and what
needs to be implemented locally for LLVM IR. The paper describes the may/must
analysis framework, summary rules, and alternation strategy, but it does not
define concrete LLVM instruction transfer functions. That operational layer is
our responsibility.

## 1. Define A Real Predicate Domain

Current state: the default CLI still uses the syntactic `Predicate` in
`src/analysis/domain.rs`. The experimental `--engine smt` path uses the new
solver-independent predicate layer in `src/analysis/predicates.rs`:

- `IntTerm` represents scalar integer terms, including SSA values and
  summary-boundary parameters/returns;
- `Formula` represents Boolean formulas over integer terms and Boolean SSA
  values;
- formulas encode into `StateEncoding`;
- `Formula::is_satisfiable_in`, `Formula::entails_in`, and
  `Formula::intersects_in` use Z3-backed checks.

Needed:

- Extend predicates beyond scalar integers to memory, globals, heap objects,
  arrays, structs, bitvectors, and pointer/object terms.
- Encode LLVM values, memory, globals, parameters, return values, and path
  conditions as SMT terms.
- Track pre-state and post-state memory versions explicitly.
- Broaden the typed predicate layer beyond the first `--engine smt`
  intraprocedural assertion path.
- Replace syntactic `Predicate::entails` in the legacy/default CLI with SMT
  validity checks if the legacy path is kept long term, or retire the old
  syntactic `Predicate` from the SMT path.
- Replace syntactic `Predicate::intersects` in the legacy/default CLI with SMT
  satisfiability checks if the legacy path is kept long term, or retire the
  old syntactic `Predicate` from the SMT path.
- Use `SmtEncodingContext` as the owner of analysis symbols for each query,
  path, or summary encoding.

Example checks:

```text
entails(a, b)        := UNSAT(a & !b)
intersects(a, b)     := SAT(a & b)
path_feasible(path)  := SAT(path_condition)
```

## 2. Add A Typed Symbolic State

Current state: the default CLI still uses `SymbolicState` in
`src/analysis/may_must.rs`, which is a `HashMap<String, String>` plus simple
memory. The SMT side now has:

- `src/analysis/state.rs`: `StateEncoding`, summary-boundary symbols, path
  conditions, and versioned SMT memory arrays;
- `src/analysis/smt_path.rs`: cloneable `SmtPathState` with integer bindings,
  Boolean bindings, simple stack-memory bindings, path conditions, return
  binding, trace, and feasibility checks.

Needed:

- Follow `src/analysis/memory_updates.md` and replace the first simple
  `SmtPathState` memory map with solver-independent memory terms that encode
  through `StateEncoding`.
- Track value versions across instruction transfer.
- Distinguish:
  - function parameters;
  - local SSA values;
  - stack objects;
  - globals;
  - heap objects;
  - return values;
  - pre-state values;
  - post-state values.

Possible sketch:

```rust
pub struct ProgramState {
    pub scalars: HashMap<ValueId, SmtValue>,
    pub memory: MemoryValue,
    pub path_condition: Bool,
}

pub enum StatePhase {
    Pre,
    Post,
    Path,
}

pub struct SymbolId {
    pub function: String,
    pub name: String,
    pub version: usize,
    pub phase: StatePhase,
}
```

## 3. Implement LLVM Transfer Functions

Current state: `analysis::may_must` still implements the default toy
concrete/symbolic subset inline. `src/analysis/transfer.rs` exists for the SMT
path and currently supports:

- simple `alloca`;
- simple `store`;
- simple `load`;
- scalar `add`;
- scalar `sub`;
- scalar `mul`;
- `icmp` predicates exposed by `llvm_wrap`;
- unconditional `br`;
- conditional `br` with SMT feasibility pruning;
- scalar `ret`.

Unsupported instructions return explicit `TransferError::UnsupportedOpcode`.

Needed:

- Decide whether the old toy analyzer should stay intact permanently as a
  reference or whether shared transfer helpers should eventually be factored.
- Define each transfer as a relation between pre-state and post-state.
- Replace simple stack-memory transfer with `MemoryTerm::Store` and
  `IntTerm::Load`, then add summary-boundary memory relations and
  `getelementptr`.
- Add bitvector/bit-operation transfer or decide to keep integer arithmetic
  only for the first SMASH milestone.
- Add casts/conversions.
- Add calls, actual/formal binding, return binding, and memory side effects.
- Add `phi`, `switch`, and predecessor-sensitive edge handling.

General form:

```text
T_inst(pre_state, post_state)
```

Examples:

```llvm
%3 = add i32 %1, %2
```

```text
%3_post = %1_pre + %2_pre
unchanged(other values)
mem_post = mem_pre
```

```llvm
store i32 %v, ptr %p
```

```text
mem_post = store(mem_pre, p_pre, v_pre)
```

```llvm
%v = load i32, ptr %p
```

```text
%v_post = select(mem_pre, p_pre)
mem_post = mem_pre
```

## 4. Instruction Coverage Checklist

Scalar arithmetic:

- `add` - implemented for SMT scalar path
- `sub` - implemented for SMT scalar path
- `mul` - implemented for SMT scalar path
- `sdiv`
- `udiv`
- `srem`
- `urem`

Bit operations:

- `and`
- `or`
- `xor`
- `shl`
- `lshr`
- `ashr`

Comparisons:

- `icmp eq` - implemented through LLVM predicate wrapper
- `icmp ne` - implemented through LLVM predicate wrapper
- signed predicates: `sgt`, `sge`, `slt`, `sle` - currently normalized by
  `llvm_wrap` to `>`, `>=`, `<`, `<=`
- unsigned predicates: `ugt`, `uge`, `ult`, `ule` - currently normalized by
  `llvm_wrap` to `>`, `>=`, `<`, `<=`; signedness is not yet modeled

Memory:

- `alloca` - implemented as a simple stack-memory operation in the SMT path
- `load` - implemented as a simple stack-memory operation in the SMT path
- `store` - implemented as a simple stack-memory operation in the SMT path
- `getelementptr`
- globals
- heap objects
- arrays
- structs

Casts and conversions:

- `trunc`
- `zext`
- `sext`
- `bitcast`
- `ptrtoint`
- `inttoptr`

Terminators:

- unconditional `br` - implemented as `Continue`
- conditional `br` - implemented with true/false SMT feasibility pruning
- `switch`
- `ret` - implemented for scalar return values
- `unreachable`

SSA joins:

- `phi`
- predecessor-sensitive phi selection

Calls:

- direct internal calls
- external calls
- recursive calls
- return value binding
- memory side effects
- actual/formal parameter binding

## 5. Implement Z3-Backed Path Feasibility

Current state: the default CLI still uses concrete folding plus syntactic
contradiction checks. The experimental SMT path has feasibility support:

- `SmtPathState::is_feasible` checks `SAT(path_condition)`;
- `SmtPathState::fork_with_assumption` prunes infeasible forks;
- `transfer::fork_branch_states` checks both `cond` and `!cond`.

Needed:

- Add regression tests for SMT branch pruning through the CLI or direct engine
  fixtures.
- Return `Unknown` only when encoding is unsupported, not when a path is simply
  infeasible.

Old CLI target code path, if the toy analyzer is upgraded instead of replaced:

- Replace `with_condition` in `analysis::may_must`.
- Use `SAT(path_condition & branch_condition)`.
- Use `SAT(path_condition & !branch_condition)`.

## 6. Implement Z3-Backed Summary Applicability

Current state: the default CLI summary matching uses simple syntactic
`entails` and `intersects`. The SMT path has `src/analysis/summary_store.rs`:

- `FunctionSummary` stores `Must` and `NotMay` summaries over typed formulas;
- `SummaryTarget` distinguishes returns from assertion violations;
- `SmtQuery` stores typed pre/post query formulas;
- `SummaryStore::find_applicable_must` and
  `SummaryStore::find_applicable_not_may` use SMT-backed formula checks.

Needed:

- Re-check the exact must/not-may entailment directions against the SMASH
  rules before freezing the API.
- Extend `SummaryStore` use beyond direct intraprocedural assertion summaries.
- Add summary instantiation/substitution for caller/callee contexts.
- Must summary applicability:

```text
query.pre entails summary.pre
summary.post intersects query.post
```

- Not-may summary applicability:

```text
query.pre entails summary.pre
query.post entails summary.post
```

The exact entailment direction still needs review against the paper's summary
rules before finalizing.

## 6.25 Add Explicit Named Paper Rules

Current state: `src/analysis/may_must_rules.rs` contains the first explicit
named summary-applicability rule checks. `summary_store.rs` now delegates
summary applicability to this rule module.

Design goal: keep the implementation close to the SMASH paper by giving the
named proof obligations explicit functions, while using the existing typed
predicate and summary infrastructure.

Needed:

- Continue using `src/analysis/may_must_rules.rs` as a thin named-rule facade.
- Do not put raw Z3 operations or LLVM transfer semantics in this module.
- Rule functions should call into `Formula::entails_in`,
  `Formula::intersects_in`, and summary/query types from `summary_store.rs`.
- Current summary applicability rules:
  - `must_pre`;
  - `must_post`;
  - `not_may_pre`;
  - `not_may_post`;
  - `applicable_must_summary`;
  - `applicable_not_may_summary`.
- Structured rule-check results currently contain rule name, Boolean result,
  and a short explanation.
- Add more rule-specific tests as more paper obligations are implemented.
- Keep exact entailment directions marked for review until checked against the
  paper.

Suggested module boundary:

```text
may_must_rules.rs -> names and composes paper proof obligations
summary_store.rs  -> searches cached summaries
smt_engine.rs     -> decides when to apply/create summaries
predicates.rs     -> discharges SMT formula checks
transfer.rs       -> models LLVM instructions only
```

## 6.5 Extend The SMT Analysis Engine Worklist

Current state: `src/analysis/smt_engine.rs` owns config, summary storage, the
SMASH summary lookup order, and a first intraprocedural worklist for direct
embedded assertions:

1. applicable `Must` summary;
2. applicable `NotMay` summary;
3. otherwise execute the function body for the supported subset.

Needed next:

- Add direct tests for the SMT engine worklist.
- Convert `TransferOutcome::Return` into scalar return summaries for return
  queries.
- Add command-line assertion support or keep it explicitly legacy-only.
- Add direct-call summary composition.
- Return `UNKNOWN` for unsupported calls, `phi`, `switch`, casts,
  `getelementptr`, and undecidable solver results.
- Keep `src/analysis/may_must.rs` untouched until this SMT engine has its own
  tests.

## 7. Replace Bounded Path Search With Real May Analysis

Current state: the may side is bounded symbolic execution.

Paper target: over-approximate predicate abstraction, similar to SLAM.

Needed:

- Maintain a set of abstraction predicates.
- Compute abstract successors.
- Detect spurious counterexamples.
- Refine the predicate set.
- Create not-may summaries only after an over-approximate proof succeeds.

## 8. Strengthen Must Analysis

Current state: the must side is symbolic trace search over simple expressions.

Paper target: under-approximate dynamic test generation, similar to DART.

Needed:

- Generate path constraints.
- Query Z3 for concrete models.
- Convert models into concrete inputs.
- Execute or simulate the program on those inputs.
- Confirm real witness traces.
- Cache must summaries with witness conditions.

## 9. Implement Procedure Summary Composition

Current state: the legacy path queries whether a callee can transitively reach
an embedded `may_assert`; the SMT path treats non-`may_assert` calls as
`UNKNOWN`.

Needed:

- Instantiate callee summaries in the caller context.
- Bind caller actual arguments to callee formal parameters.
- Bind callee return value to caller assignment.
- Model memory side effects through the call.
- Support external function summaries.
- Support recursive calls with a sound strategy:
  - recursion depth bound;
  - fixed-point summaries;
  - widening;
  - or explicit `Unknown`.

## 10. Improve Memory Modeling

Current state: memory is simplified in both executable paths:

- Legacy path: `HashMap<String, String>` from symbolic pointer names to string
  values.
- Executable SMT path: `SmtPathState` has `HashMap<String, IntTerm>` from a
  syntactic pointer key to a scalar integer term.
- `StateEncoding` has versioned SMT arrays, but those arrays are not yet used
  by the `--engine smt` worklist.
- `alloca` is a no-op in `transfer.rs`; it only provides a named stack slot for
  later `store`/`load` map entries.
- Unknown `load` creates an uninterpreted scalar `load(ptr)` term.

This was a deliberate first-pass simplification to let unoptimized LLVM stack
traffic pass through the SMT smoke tests. It is not alias-aware and should not
be treated as the final memory semantics.

Needed:

- Model pointers as symbolic addresses or object/offset pairs.
- `alloca` creates fresh object IDs.
- `load` and `store` use SMT arrays or an object-field model.
- `getelementptr` computes object offsets.
- Support aliasing.
- Support arrays and structs.
- Support globals.
- Support heap allocation (`malloc`, `free`) through external summaries.

Early practical option:

- First migrate to the `MemoryTerm` plan in
  `src/analysis/memory_updates.md`, so the executable worklist no longer has a
  separate toy memory map.
- Then use an object/field model rather than byte-accurate memory if arrays are
  too broad for the next milestone.
- Treat unsupported aliasing as `Unknown`.

## 11. Improve CFG And Path Semantics

Current state: the CFG builder now avoids bogus cross-basic-block fallthroughs.

Needed:

- Assign stable instruction IDs.
- Preserve basic block labels.
- Track predecessor edge in symbolic states for phi nodes.
- Represent edge conditions explicitly.
- Add support for `switch`.
- Add loop handling beyond visit limits.

## 12. Clarify Assertion Target Semantics

Current state: `may_assert(e)` is treated as a bug when `e` is definitely false.

Needed:

- Normalize every assertion into an explicit violation target:

```text
postcondition := assertion_violation(assert_id)
edge condition := e == false
```

- Store assertion IDs and source locations when available.
- Report traces to assertion sites.
- Support command-line assertions and embedded assertions through the same
  internal representation.

## 13. Add Transfer Semantics Documentation

The paper does not explain LLVM transfer functions. Add local documentation:

```text
docs/llvm-transfer-semantics.md
```

Suggested sections:

- State model
- Notation
- Scalar instructions
- Memory instructions
- Terminators
- Phi nodes
- Calls and summaries
- External functions
- Unsupported instructions
- Soundness assumptions
- Z3 encoding plan

This document should become the implementation contract for
`src/analysis/transfer.rs`.

## 14. Suggested Implementation Order

1. Keep `make -C tests smoke` green as the minimal current SMASH regression.
2. Keep `cargo test` green; current count after the SMT test additions is 35
   tests.
3. Review the exact entailment directions in `src/analysis/may_must_rules.rs`
   against the SMASH paper before relying on the SMT path for CLI results.
4. Add one test showing unsupported `phi`, `switch`, or unsupported call
   returns `UNKNOWN`.
5. Add `docs/llvm-transfer-semantics.md`.
6. Replace simple stack memory with the `MemoryTerm`/`StateEncoding` plan in
   `src/analysis/memory_updates.md`.
7. Add `getelementptr` or return `UNKNOWN` for it explicitly.
8. Implement actual/formal and return binding for direct calls.
9. Enable `tests/paper_section2_fig1_not_may.c` as an executable regression
   once direct-call composition exists.
10. Add external summaries for common functions.
11. Start predicate abstraction/refinement for the may side.
12. Start DART-style model-to-input generation for the must side.

## 15. Near-Term Test Plan

Add focused LLVM/C tests for:

- straight-line arithmetic assertion safe/bug cases;
- conditional branches with feasible and infeasible paths;
- loops with small concrete bounds;
- `phi` nodes;
- stack load/store;
- simple function calls with return values;
- function calls with pointer arguments;
- one external function treated as an uninterpreted summary;
- assertion inside a callee;
- recursive call returning `Unknown`.
