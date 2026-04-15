# State Model

This document explains the symbolic state model we will use before adding the
LLVM transfer-function module.

## Goal

The paper describes may/must summaries and query composition, but it does not
define LLVM instruction semantics. We need a local state model that supports
both:

- forward-looking implementation code; and
- relational SMT formulas for paths and summaries.

The key compromise is:

- LLVM SSA values get one SMT symbol each.
- Memory is versioned.
- Path conditions accumulate.
- Procedure summaries use explicit input/output boundary symbols.

This avoids creating `%x_pre` and `%x_post` for every immutable SSA value at
every instruction, while still giving us relational composition for mutable
state and summaries.

## Why Not Version Every SSA Value?

For a pure LLVM SSA instruction:

```llvm
%3 = add i32 %1, %2
```

LLVM already guarantees `%3` is assigned once. The relational constraint can be:

```text
%3 = %1 + %2
```

We do not need:

```text
%3_post = %1_pre + %2_pre
%1_post = %1_pre
%2_post = %2_pre
```

That fully pre/post style is valid, but noisy. It also creates many frame
conditions for values that LLVM already treats as immutable.

## Where Versioning Is Needed

Memory changes over time.

Example:

```llvm
store i32 1, ptr %p
%a = load i32, ptr %p
store i32 2, ptr %p
%b = load i32, ptr %p
```

The SSA value `%p` is immutable, but the contents of memory at `%p` are not.
So we need memory versions:

```text
mem1 = store(mem0, %p, 1)
%a = select(mem1, %p)
mem2 = store(mem1, %p, 2)
%b = select(mem2, %p)
```

This is the main reason the state model is not just one map from program
variables to expressions.

## Relational Composition

A path or block is a conjunction of constraints.

LLVM:

```llvm
%3 = add i32 %1, %2
%4 = mul i32 %3, 10
store i32 %4, ptr %p
%5 = load i32, ptr %p
```

Relational constraints:

```text
%3 = %1 + %2
%4 = %3 * 10
mem1 = store(mem0, %p, %4)
%5 = select(mem1, %p)
```

Composition is just conjunction. Intermediate values such as `%3`, `%4`, and
`mem1` connect one instruction's relation to the next.

If we later want a relation from path entry to path exit, we can existentially
hide intermediate SSA values and memory versions:

```text
exists %3, %4, mem1.
  %3 = %1 + %2
  & %4 = %3 * 10
  & mem1 = store(mem0, %p, %4)
  & %5 = select(mem1, %p)
```

Operationally, the encoder can still run forward. It appends constraints and
advances the current memory version when memory changes.

## Branches

For a conditional branch:

```llvm
br i1 %cond, label %then, label %else
```

The path to `then` adds:

```text
%cond = true
```

The path to `else` adds:

```text
%cond = false
```

Path feasibility is:

```text
SAT(path_constraints)
```

## Phi Nodes

Phi nodes are predecessor-sensitive.

```llvm
%x = phi i32 [ %a, %then ], [ %b, %else ]
```

When entering from `%then`:

```text
%x = %a
```

When entering from `%else`:

```text
%x = %b
```

The future transfer module must know the incoming CFG edge when encoding phi
nodes.

## Procedure Summaries

Summaries need input/output boundary symbols even though ordinary SSA values do
not need per-instruction pre/post versions.

A summary may relate:

```text
param0_in
mem_in
ret_out
mem_out
```

Example callee summary:

```text
pre:  x_in > 0
post: ret_out = x_in + 1 & mem_out = mem_in
```

Caller composition for:

```llvm
%r = call i32 @foo(i32 %a)
```

instantiates:

```text
x_in := %a
ret_out := %r
mem_in := caller_mem_before
mem_out := caller_mem_after
```

and adds:

```text
%a > 0
%r = %a + 1
caller_mem_after = caller_mem_before
```

## Rust Module Contract

`src/analysis/state.rs` implements only this state-to-Z3 encoding layer.

It should know how to:

- create one SMT symbol per SSA value;
- create versioned memory arrays;
- advance memory versions on stores;
- read from the current memory version;
- record path assumptions;
- create summary boundary symbols.

It should not know LLVM instruction semantics. Per-instruction transfer
functions belong in a separate module, likely `src/analysis/transfer.rs`.

