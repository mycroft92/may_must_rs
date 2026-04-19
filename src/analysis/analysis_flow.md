# Analysis Flow: Paper-To-Code Mapping

This note explains how the SMASH paper concepts map to this repository's code,
where each paper-level rule should live, and how the top-level analyzer should
call those rules.

The important split is:

```text
paper proof rules       -> may_must_rules.rs
summary storage/search  -> summary_store.rs
query orchestration     -> smt_engine.rs
LLVM instruction meaning -> transfer.rs
path state              -> smt_path.rs
formula vocabulary      -> predicates.rs
SMT symbol encoding     -> state.rs
raw Z3 operations       -> smt/solver.rs
```

The default CLI still runs `may_must.rs`. The SMT-backed path described here is
available behind `--engine smt` for direct embedded `may_assert` queries and is
still being built beside the legacy implementation.

## Paper Concepts

### Reachability Query

Paper shape:

```text
<phi1 ?=> P phi2>
```

Meaning:

```text
Can procedure P start in a state satisfying phi1
and reach a target/final state satisfying phi2?
```

Code mapping:

```rust
SmtQuery {
    function,
    target,
    pre,
    post,
}
```

Location:

```text
src/analysis/summary_store.rs
```

`pre` corresponds to `phi1`.

`post` corresponds to `phi2`.

`function` corresponds to `P`.

`target` is an implementation-level clarification that distinguishes endpoint
classes:

```text
Return
AssertionViolation(assert_id)
```

The target is not a Z3 formula today. It is matched structurally in Rust.

### Must Summary

Paper idea:

```text
<phi1 must=> P phi2>
```

Meaning:

```text
There exists a real execution of P from phi1 to phi2.
```

Code mapping:

```rust
FunctionSummary {
    kind: SummaryKind::Must,
    pre,
    post,
    relation,
    evidence: SummaryEvidence::WitnessTrace(...),
    ...
}
```

Location:

```text
src/analysis/summary_store.rs
```

Creation site:

```text
smt_engine.rs
```

The engine should create a `Must` summary when the intraprocedural analysis
finds a feasible witness path to the queried target. For assertion targets, the
witness condition is:

```text
path_condition & !assert_arg & query.post
```

For return targets, the witness condition is:

```text
path_condition & return_relation & query.post
```

### NotMay Summary

Paper idea:

```text
<phi1 not-may=> P phi2>
```

Meaning:

```text
No execution of P from phi1 can reach phi2.
```

Code mapping:

```rust
FunctionSummary {
    kind: SummaryKind::NotMay,
    pre,
    post,
    relation: Formula::True,
    evidence: SummaryEvidence::NotMayProof { ... },
    ...
}
```

Location:

```text
src/analysis/summary_store.rs
```

Creation site:

```text
smt_engine.rs
```

The engine should create a `NotMay` summary only when all supported paths have
been explored and no feasible target state was found. Unsupported instructions
must produce `UNKNOWN`, not `NotMay`.

### May Summary

The current design does not persist May summaries.

Reason:

```text
Must   -> can prove BUG
NotMay -> can prove SAFE
May    -> usually too weak to answer the top-level query
```

May analysis is an internal process that can eventually produce a `NotMay`
proof. It is not stored as a procedure summary.

## Rule Locations

### Named Paper Rules

The paper's named proof obligations should be represented explicitly in:

```text
src/analysis/may_must_rules.rs
```

That module should be a facade over the existing typed infrastructure.

It should not:

- own raw Z3 solver operations;
- inspect LLVM instructions directly;
- run worklists;
- store summaries.

It should:

- name each paper-level obligation;
- compose formula checks;
- return structured rule-check results;
- be easy to compare against the paper.

Planned initial functions:

```rust
must_pre(summary, query)
must_post(summary, query)
not_may_pre(summary, query)
not_may_post(summary, query)
applicable_must_summary(summary, query)
applicable_not_may_summary(summary, query)
```

Suggested result shape:

```rust
pub enum RuleName {
    MustPre,
    MustPost,
    NotMayPre,
    NotMayPost,
    ApplicableMustSummary,
    ApplicableNotMaySummary,
}

pub struct RuleCheck {
    pub rule: RuleName,
    pub holds: bool,
    pub detail: String,
}
```

Exact API can change, but the intent is that the code says the same thing as
the paper rule being implemented.

### Summary Applicability Rules

Current direct implementation:

```text
src/analysis/summary_store.rs
```

Current methods:

```rust
SummaryStore::find_applicable_must
SummaryStore::find_applicable_not_may
```

Target implementation:

```text
SummaryStore searches summaries.
may_must_rules.rs checks whether a candidate summary applies.
```

Target call shape:

```rust
for summary in summaries.must() {
    if applicable_must_summary(summary, query)?.holds {
        return Ok(Some(summary));
    }
}
```

and:

```rust
for summary in summaries.not_may() {
    if applicable_not_may_summary(summary, query)?.holds {
        return Ok(Some(summary));
    }
}
```

The current entailment directions are intentionally documented as a caveat and
must be reviewed against the paper before the SMT engine becomes user-visible.

Current must applicability checks:

```text
summary.pre entails query.pre
summary.post intersects query.post
```

Current not-may applicability checks:

```text
query.pre entails summary.pre
query.post entails summary.post
```

The mechanics of those checks are implemented by `Formula`:

```text
entails(a, b)    := UNSAT(a & !b)
intersects(a, b) := SAT(a & b)
```

Location:

```text
src/analysis/predicates.rs
```

## Top-Level Analysis Flow

The intended top-level SMT flow is:

```text
analyze_query(graph, query)
  1. ask SummaryStore for applicable Must summary
  2. ask SummaryStore for applicable NotMay summary
  3. if neither applies, execute the function body
  4. if a feasible target is found, create Must summary
  5. if all supported paths finish without target, create NotMay summary
  6. if unsupported/undecidable, return Unknown
```

Code location:

```text
src/analysis/smt_engine.rs
```

Current implementation status:

```text
Summary lookup order exists.
CFG worklist execution is not implemented yet.
```

Current method:

```rust
SmtAnalysisEngine::answer_from_summaries
```

Future method shape:

```rust
SmtAnalysisEngine::analyze_query(graph: &FunctionGraph, query: SmtQuery)
```

Expected internal flow:

```text
analyze_query
  -> answer_from_summaries
       -> SummaryStore::find_applicable_must
            -> may_must_rules::applicable_must_summary
       -> SummaryStore::find_applicable_not_may
            -> may_must_rules::applicable_not_may_summary
  -> execute_function if no cached answer
       -> TransferFunctions::transfer for instruction semantics
       -> SummaryStore::add_must or add_not_may for new summaries
```

## Intraprocedural Execution Flow

The paper leaves concrete LLVM transfer semantics to the implementation.

This repository handles that in:

```text
src/analysis/transfer.rs
```

Current supported SMT transfer subset:

```text
add
sub
mul
icmp
unconditional br
conditional br with SMT pruning
scalar ret
```

The transfer layer works over:

```text
src/analysis/smt_path.rs
```

Worklist item shape should be:

```rust
(Instruction, SmtPathState)
```

Execution sketch:

```text
entry:
  state = SmtPathState::with_formal_params(function, graph.params)
  enqueue(graph.start, state)

loop:
  pop (instruction, state)
  append instruction to trace
  if instruction is may_assert:
      handle assertion target
  else:
      outcome = TransferFunctions::transfer(instruction, state)
      enqueue successors based on outcome
```

Outcome handling:

```text
Continue(state)
  -> enqueue normal CFG successors

Branch { true_state, false_state }
  -> enqueue true successor if true_state is Some
  -> enqueue false successor if false_state is Some

Return(state)
  -> check return target/query.post
  -> possibly record Must or complete path

TransferError::UnsupportedOpcode
  -> return Unknown
```

## Assertion Target Flow

Embedded `may_assert(e)` should be normalized into a target query:

```text
target = AssertionViolation(assert_id)
violation condition = !e
```

In the SMT engine:

```text
if current instruction is may_assert(e):
    check SAT(path_condition & !e & query.post)
```

Outcomes:

```text
SAT:
  found witness target
  record Must summary

UNSAT:
  this path cannot violate the assertion
  continue if the call has a successor

UNKNOWN or unsupported assertion expression:
  return Unknown
```

The assertion check itself is not a transfer function. It is query-target
logic, so it belongs in `smt_engine.rs`, using formula operations from
`predicates.rs`.

## Return Target Flow

For return queries:

```text
target = Return
```

A `ret %x` transfer binds a scalar return value in `SmtPathState`.

Location:

```text
src/analysis/transfer.rs
```

Then the engine builds the boundary relation:

```text
Post.ret == returned_term
```

Location:

```text
src/analysis/smt_path.rs
SmtPathState::return_summary_relation
```

The engine checks:

```text
SAT(path_condition & return_relation & query.post)
```

If SAT, the return target is reachable under the query.

If all supported return paths fail the target check, the engine may record
`NotMay`.

## Call Rule Flow

Compositional call handling is not implemented in the SMT path yet.

Paper idea:

```text
Calls are the point where the analyzer alternates between the caller query and
callee summaries/queries.
```

Target implementation location:

```text
src/analysis/smt_engine.rs
```

The engine should:

```text
1. Detect direct internal calls.
2. Build a callee SmtQuery.
3. Ask SummaryStore whether a callee summary applies.
4. If no summary applies, recursively analyze the callee.
5. Instantiate callee summary boundary symbols into caller terms.
6. Bind callee return to caller assignment.
7. Model memory side effects or return Unknown until memory summaries exist.
```

The named call-related paper rules can be added to `may_must_rules.rs` when this
stage begins. Do not add speculative call rules before the scalar intraprocedural
path works.

## Module Responsibilities

### `predicates.rs`

Owns solver-independent formula vocabulary:

```text
IntTerm
Formula
```

Discharges formula checks by encoding into `StateEncoding`:

```text
SAT
UNSAT
entailment
intersection
```

Does not know about CFGs, LLVM instructions, or summary storage.

### `state.rs`

Owns analysis-to-Z3 symbol encoding:

```text
SSA symbols
summary pre/post symbols
memory versions
path assumptions
```

Does not decide paper rules.

### `smt/solver.rs`

Owns raw Z3 mechanics:

```text
variables
sorts
arrays
assert
check
push/pop
models
```

Does not know SMASH concepts.

### `smt_path.rs`

Owns cloneable per-path symbolic state:

```text
int bindings
bool bindings
path conditions
return value
trace
```

Creates fresh SMT encodings only for feasibility checks.

### `transfer.rs`

Owns LLVM instruction semantics.

Does not know:

```text
Must summaries
NotMay summaries
paper rules
query cache lookup
```

### `summary_store.rs`

Owns cached procedure summaries and summary lookup.

Should call named rules from `may_must_rules.rs` rather than embedding rule logic
directly.

### `may_must_rules.rs`

Should own named paper proof obligations.

Initial scope:

```text
must_pre
must_post
not_may_pre
not_may_post
applicable_must_summary
applicable_not_may_summary
```

Later scope:

```text
call composition rules
summary creation obligations
predicate-abstraction may proof rules
must witness validation rules
```

### `smt_engine.rs`

Owns top-level SMT-backed analysis orchestration.

Calls:

```text
SummaryStore for cached answers
may_must_rules through SummaryStore
TransferFunctions for instruction semantics
SummaryStore again to record new summaries
```

## Current Versus Target State

Current state:

```text
may_must.rs is the default CLI implementation.
--engine smt runs the first direct embedded-assertion SMT path.
summary lookup order and summary creation exist in smt_engine.rs.
transfer.rs has scalar and simple stack-memory transfer helpers.
may_must_rules.rs contains the first named summary applicability rules.
```

Immediate target:

```text
1. Add focused tests for the SMT CLI/engine path.
2. Review may_must_rules.rs against the paper and adjust directions if needed.
3. Keep summary_store.rs delegating applicability to may_must_rules.rs.
4. Add direct-call summary composition to smt_engine.rs.
5. Keep unsupported instructions returning Unknown.
6. Keep may_must.rs as the legacy reference while the SMT path matures.
```

Longer-term target:

```text
1. Replace simple memory with SMT-array/object memory.
2. Finish call composition.
3. Add predicate abstraction for real NotMay proofs.
4. Add DART-style/model-backed witness generation for Must.
5. Make the SMT engine the default only after it beats the toy analyzer on core coverage.
```
