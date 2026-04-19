# Memory Updates: Moving Executable SMT Memory To StateEncoding

This note records the current memory state and the next migration plan. It is
intentionally explicit because the current executable SMT path has a temporary
memory simplification that should not become the long-term design.

## Current State

There are currently two memory representations:

1. `StateEncoding` in `src/analysis/state.rs`

   This is the intended SMT-level memory vocabulary. It already has versioned
   SMT arrays:

   ```text
   mem_0, mem_1, ...
   ```

   It supports:

   ```text
   mem_next = store(mem_current, ptr, value)
   value    = select(mem_current, ptr)
   ```

   It also has summary-boundary memory symbols through
   `summary_memory(SummaryPhase::Pre)` and
   `summary_memory(SummaryPhase::Post)`.

2. `SmtPathState` in `src/analysis/smt_path.rs`

   This is what `--engine smt` currently executes in the worklist. Its memory
   is a temporary:

   ```rust
   HashMap<String, IntTerm>
   ```

   The key is a syntactic pointer key, usually an LLVM SSA name such as `%1`.

## Current Simplifications

The executable SMT memory map was added to let unoptimized LLVM IR reach
assertion checks. Clang `-O0` commonly emits stack traffic even for tiny tests:

```llvm
%1 = alloca i32
store i32 0, ptr %1
call void @may_assert(...)
```

Without minimal `alloca`/`store`/`load` handling, the first SMT smoke tests
would stop before the assertion site.

The simplifications are:

- `alloca` is a no-op in `transfer.rs`.
- `alloca` does not create an SMT object, object id, address, or allocation
  summary.
- `store` writes one scalar `IntTerm` into the per-path map.
- `load` reads one scalar `IntTerm` from the per-path map.
- an unknown `load` becomes an uninterpreted scalar term such as
  `load(%ptr)`.
- pointer identity is a string key, not a symbolic address term.
- no aliasing is modeled.
- no offsets are modeled.
- no byte layout is modeled.
- no arrays, structs, globals, or heap objects are modeled.
- `getelementptr` is not modeled.
- function-boundary memory summaries are not modeled in the executable SMT
  path.

This map is therefore a test-enabling bridge, not the final memory semantics.

## Target Direction

The goal is to make `StateEncoding` the only SMT encoder/checker for memory.

However, `StateEncoding` owns a concrete Z3 solver and Z3 ASTs, so it should
not be placed directly inside every worklist state. Worklist states need cheap
branch forks. The right division is:

```text
SmtPathState   = cloneable solver-independent semantic terms
StateEncoding  = materializes those terms into Z3 for SAT/validity checks
```

So the migration should remove the ad hoc memory map while keeping
`SmtPathState` cloneable.

## Required Predicate Changes

Add solver-independent memory terms in `src/analysis/predicates.rs`.

Sketch:

```rust
pub enum IntTerm {
    ...
    Load {
        memory: MemoryTerm,
        ptr: Box<IntTerm>,
    },
}

pub enum MemoryTerm {
    PathMemory { version: usize },
    SummaryMemory { phase: SummaryPhase },
    Store {
        memory: Box<MemoryTerm>,
        ptr: Box<IntTerm>,
        value: Box<IntTerm>,
    },
}
```

Then encoding should work like this:

```text
MemoryTerm::PathMemory(v)       -> StateEncoding::memory_at(v)
MemoryTerm::SummaryMemory(pre)  -> StateEncoding::summary_memory(pre)
MemoryTerm::Store(m, p, v)      -> store(encode(m), encode(p), encode(v))
IntTerm::Load { memory, ptr }   -> select(encode(memory), encode(ptr))
```

## Required Path-State Changes

Replace:

```rust
memory_bindings: HashMap<String, IntTerm>
```

with:

```rust
current_memory: MemoryTerm
```

Entry state should start with either:

```text
MemoryTerm::PathMemory { version: 0 }
```

or, once function summaries need memory:

```text
MemoryTerm::SummaryMemory { phase: SummaryPhase::Pre }
```

## Required Transfer Changes

`store` should become a memory-term update:

```text
state.current_memory =
  Store(state.current_memory, ptr_term, value_term)
```

`load` should become a scalar term binding:

```text
target = Load(state.current_memory, ptr_term)
```

After this, delete the temporary helpers:

```text
SmtPathState::bind_memory_int
SmtPathState::memory_int_value
transfer::pointer_key
```

Unknown loads should no longer need a special fallback. A load from unknown
memory is simply:

```text
select(mem, ptr)
```

## Pointer Representation

The first migration can model pointers as integer terms:

```text
IntTerm::Ssa("%ptr")
```

That is still not a complete pointer model, but it is already better than a
string-key map because aliasing questions become SMT questions:

```text
ptr_a == ptr_b
```

Later, pointer terms can become object/offset pairs or bitvectors.

## Summary Boundary Memory

Procedure summaries eventually need memory boundary vocabulary:

```text
Pre.mem
Post.mem
```

Examples:

```text
Post.ret == select(Pre.mem, Pre.param_0)
Post.mem == store(Pre.mem, ptr, value)
```

For direct assertion summaries, `Post.mem` may not be needed immediately. For
call composition, memory side effects must be represented.

## Implementation Order

1. Add `MemoryTerm` and `IntTerm::Load` to `predicates.rs`.
2. Implement `MemoryTerm::encode(&mut StateEncoding) -> Array`.
3. Extend `IntTerm::encode` to handle `Load`.
4. Replace `SmtPathState.memory_bindings` with `current_memory: MemoryTerm`.
5. Update `transfer_store` to build `MemoryTerm::Store`.
6. Update `transfer_load` to bind `IntTerm::Load`.
7. Delete the map-based memory helpers.
8. Add tests:
   - store then load from the same pointer entails equality;
   - store to one pointer does not imply load from another pointer;
   - branch feasibility still works with memory-derived formulas;
   - `make -C tests smt-smoke` remains green.

## Guardrail

Do not put a live `StateEncoding` inside `SmtPathState` unless there is a very
specific reason. That would make branch forking and worklist states harder to
reason about. The cleaner model is:

```text
cloneable symbolic terms now, Z3 encoding only when checking
```
