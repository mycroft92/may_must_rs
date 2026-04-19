# Summary Store Design Notes

Archived note: this document describes the old `obsolete/src/analysis`
summary/query design. It is preserved for reference only. The active analysis
path now lives under `src/analysis`.

This note documents the current design intent for `summary_store.rs` and its
relationship to `predicates.rs`, `smt_engine.rs`, and `smt_path.rs`.

The key point: `SmtQuery` is an analysis-level question, not itself a raw Z3
query.

## Concepts

`SmtQuery` has four fields:

```rust
pub struct SmtQuery {
    pub function: String,
    pub target: SummaryTarget,
    pub pre: Formula,
    pub post: Formula,
}
```

It represents the SMASH query shape:

```text
<pre ?=> function post>
```

with an additional explicit endpoint target:

```text
Can function P start in states satisfying `pre`
and reach target T in a final/error state satisfying `post`?
```

The fields have distinct roles:

```text
function : which procedure is being queried
target   : what endpoint class is being queried
pre      : allowed function-entry states
post     : required state at the queried endpoint
```

`target` is not just another formula. It distinguishes endpoint classes that
could otherwise all have `post = true`.

Examples:

```text
Can main violate any embedded may_assert?
Can foo return with ret == 0?
Can bar reach unreachable?
```

Those are different queries even if their postcondition formula is `true`.

## Example Queries

Embedded assertion reachability:

```rust
SmtQuery {
    function: "main".to_string(),
    target: SummaryTarget::AssertionViolation("any_may_assert".to_string()),
    pre: Formula::True,
    post: Formula::True,
}
```

Meaning:

```text
Can main, from any entry state, reach any may_assert violation?
```

Scalar return relation:

```rust
SmtQuery {
    function: "inc".to_string(),
    target: SummaryTarget::Return,
    pre: Formula::True,
    post: Formula::eq(
        IntTerm::summary_return(SummaryPhase::Post),
        IntTerm::add(
            IntTerm::summary_param(SummaryPhase::Pre, 0),
            IntTerm::int(1),
        ),
    ),
}
```

Meaning:

```text
Can inc return with Post.ret == Pre.param_0 + 1?
```

## Where SMT Encoding Happens

`SmtQuery` is not converted wholesale into one Z3 AST.

The formulas inside the query are encoded by `Formula` methods from
`predicates.rs`.

For summary applicability, `summary_store.rs` currently calls:

```rust
summary.pre.entails_in(&query.pre, &query.function)?
summary.post.intersects_in(&query.post, &query.function)?
```

and:

```rust
query.pre.entails_in(&summary.pre, &query.function)?
query.post.entails_in(&summary.post, &query.function)?
```

The `Formula` methods create a fresh `StateEncoding`, encode the formula into
Z3 terms, assert constraints, and call the solver.

The relevant logical encodings are:

```text
entails(a, b)    := UNSAT(a & !b)
intersects(a, b) := SAT(a & b)
```

`SummaryTarget` is matched structurally in Rust. It is not currently encoded
into Z3.

## Query Versus Summary

Mental model:

```text
SmtQuery        = analysis question
FunctionSummary = cached answer/proof/witness
Formula         = object that actually encodes into Z3
SummaryTarget   = endpoint kind, matched structurally
```

The named paper-rule layer lives in `may_must_rules.rs`. It makes the
relationship between queries and summaries explicit without owning storage,
execution, or raw SMT mechanics.

Suggested ownership:

```text
may_must_rules.rs = named proof obligations from the paper
summary_store.rs  = searches cached summaries
smt_engine.rs     = applies/creates summaries while solving queries
predicates.rs     = encodes/discharges formula checks
transfer.rs       = LLVM instruction transfer only
```

`FunctionSummary` stores:

```rust
pub struct FunctionSummary {
    pub function: String,
    pub kind: SummaryKind,
    pub target: SummaryTarget,
    pub pre: Formula,
    pub post: Formula,
    pub relation: Formula,
    pub evidence: SummaryEvidence,
}
```

The summary is intentionally expressed in function-boundary vocabulary, such as:

```text
Pre.param_0
Post.ret
Pre.mem
Post.mem
```

It should not depend on local temporary SSA names except as an implementation
detail while constructing the summary.

## Must And NotMay

The store persists only two useful summary kinds:

```text
Must   : there exists a witness execution from pre to post/target
NotMay : no execution from pre reaches post/target
```

It deliberately does not persist May summaries. May analysis is an internal
process that can produce a NotMay proof. A saved May fact is usually too weak
to answer the top-level query.

## Applicability Direction Caveat

The current code mirrors the older toy implementation's summary lookup shape,
but the exact SMT entailment directions should be reviewed against the SMASH
rules before freezing the API.

Current must lookup:

```rust
summary.pre.entails_in(&query.pre, &query.function)?
summary.post.intersects_in(&query.post, &query.function)?
```

In a named-rules module, this should appear as:

```rust
must_pre(summary, query)
must_post(summary, query)
applicable_must_summary(summary, query)
```

This asks whether the summary witness precondition is inside the query's
allowed precondition, and whether the summary post can overlap the queried post.
That is plausible for witness reuse, but it should be checked against the
paper's formal rule and the final meaning of stored `Must.pre`.

Possible must intuitions:

```text
summary.pre => query.pre
```

or, if stored witness conditions are not exact:

```text
summary.pre intersects query.pre
```

Current not-may lookup:

```rust
query.pre.entails_in(&summary.pre, &query.function)?
query.post.entails_in(&summary.post, &query.function)?
```

In a named-rules module, this should appear as:

```rust
not_may_pre(summary, query)
not_may_post(summary, query)
applicable_not_may_summary(summary, query)
```

This matches the usual intuition:

```text
If a NotMay summary proves no target for a broader input/target region,
then it can prove a narrower query safe.
```

This direction is still marked for review before the SMT engine depends on it
for user-visible CLI results.

## How The Future Engine Should Use SmtQuery

When `SmtAnalysisEngine` grows a real worklist, `SmtQuery` should drive
execution like this:

```text
1. Check SummaryStore for an applicable Must summary.
2. Check SummaryStore for an applicable NotMay summary.
3. Build an entry SmtPathState from query.pre and function parameters.
4. Symbolically execute the function with TransferFunctions.
5. At target sites, check whether path_condition & query.post is SAT.
6. If SAT at a violation target, record a Must summary.
7. If all supported paths complete without reaching a SAT target, record NotMay.
8. If an unsupported instruction or unknown SMT result is encountered, return Unknown.
```

For embedded assertions:

```text
target = AssertionViolation(assert_id)
bug condition = path_condition & !assert_arg & query.post
```

For return queries:

```text
target = Return
success condition = path_condition & return_relation & query.post
```

## Boundary Symbols

`SummaryPhase::Pre` and `SummaryPhase::Post` are function-boundary concepts.
They are not separate transfer modes.

Instruction transfer should be one forward relation:

```text
state_before_instruction -> state_after_instruction
```

At function boundaries, the resulting path facts are converted into formulas
over summary symbols:

```text
Post.ret == term_built_from_Pre.params_and_path_constraints
```

This keeps transfer functions local and summary construction centralized in the
engine/store layer.
