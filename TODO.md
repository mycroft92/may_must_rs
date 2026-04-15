# TODO: Remaining SMASH Implementation Work

This file tracks what is still missing compared with the SMASH paper and what
needs to be implemented locally for LLVM IR. The paper describes the may/must
analysis framework, summary rules, and alternation strategy, but it does not
define concrete LLVM instruction transfer functions. That operational layer is
our responsibility.

## 1. Define A Real Predicate Domain

Current state: `Predicate` is mostly syntactic.

Needed:

- Represent predicates over actual program states, not just strings.
- Encode LLVM values, memory, globals, parameters, return values, and path
  conditions as SMT terms.
- Track pre-state and post-state versions explicitly.
- Replace syntactic `Predicate::entails` with SMT validity checks.
- Replace syntactic `Predicate::intersects` with SMT satisfiability checks.
- Use `SmtEncodingContext` as the owner of analysis symbols for each query,
  path, or summary encoding.

Example checks:

```text
entails(a, b)        := UNSAT(a & !b)
intersects(a, b)     := SAT(a & b)
path_feasible(path)  := SAT(path_condition)
```

## 2. Add A Typed Symbolic State

Current state: `SymbolicState` is a `HashMap<String, String>` plus simple
memory.

Needed:

- Add `src/analysis/state.rs`.
- Represent scalar LLVM values as typed symbolic expressions.
- Represent memory as an SMT array or a custom object model.
- Track path condition as a Boolean expression.
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

Current state: `analysis::may_must` implements a small concrete/symbolic subset
inline.

Needed:

- Add `src/analysis/transfer.rs`.
- Move all per-instruction semantics out of `may_must.rs`.
- Define each transfer as a relation between pre-state and post-state.
- Use SMT terms instead of string expressions.
- Return `Unsupported` or `Unknown` explicitly for instructions not yet modeled.

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

- `add`
- `sub`
- `mul`
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

- `icmp eq`
- `icmp ne`
- signed predicates: `sgt`, `sge`, `slt`, `sle`
- unsigned predicates: `ugt`, `uge`, `ult`, `ule`

Memory:

- `alloca`
- `load`
- `store`
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

- unconditional `br`
- conditional `br`
- `switch`
- `ret`
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

Current state: branch feasibility is mostly concrete folding plus syntactic
contradiction checks.

Needed:

- Encode branch conditions into `SmtEncodingContext`.
- Check feasibility before adding a successor state.
- Prune infeasible paths.
- Return `Unknown` only when encoding is unsupported, not when a path is simply
  infeasible.

Target code path:

- Replace `with_condition` in `analysis::may_must`.
- Use `SAT(path_condition & branch_condition)`.
- Use `SAT(path_condition & !branch_condition)`.

## 6. Implement Z3-Backed Summary Applicability

Current state: summary matching uses simple syntactic `entails` and
`intersects`.

Needed:

- Encode query pre/post predicates into SMT.
- Encode summary pre/post predicates into SMT.
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

The exact entailment direction should be reviewed against the paper's summary
rules before finalizing.

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

Current state: calls only query whether a callee can transitively reach an
embedded `may_assert`.

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

Current state: memory is a simple map from symbolic pointer names to symbolic
values.

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

- Use an object/field model rather than byte-accurate memory.
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
2. Add a safe not-may smoke test and an `UNKNOWN` smoke test.
3. Add `analysis/transfer.rs` with a small supported LLVM subset:
   - integer arithmetic;
   - `icmp`;
   - `alloca`;
   - `load`;
   - `store`;
   - conditional/unconditional `br`;
   - `ret`.
4. Move current string-based transfer behavior out of `may_must.rs` before
   changing semantics.
5. Use `SmtEncodingContext` for symbolic values.
6. Replace string-based `SymbolicState` in `may_must.rs`.
7. Add `docs/llvm-transfer-semantics.md`.
8. Add Z3-backed path feasibility.
9. Add Z3-backed summary applicability.
10. Implement actual/formal and return binding for direct calls.
11. Add external summaries for common functions.
12. Start predicate abstraction/refinement for the may side.
13. Start DART-style model-to-input generation for the must side.

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
