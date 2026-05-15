# Memory Model Design

This document describes the current stack memory model, the planned heap memory
model, and how they interact with the bidirectional may/must analysis.

---

## Stack Memory Model (implemented)

### Regions

Each local `alloca` in a function is assigned a distinct named array region
during lowering (`adapter.rs`):

```
alloca i32           → region  fn$stack0
alloca [5 x i32]     → region  fn$stack1
alloca %Foo          → region  fn$stack2   (one region per alloca, pre-Step 2)
```

Each region is an abstract integer array `Memory` in the SMT encoding.
Reads and writes become `select` / `store` operations on the named array.

Pointer parameters to the function are treated as external regions:

```
fn(int *p, int *q)  → ext regions  fn$__ext_0,  fn$__ext_1
```

The caller may pass the same underlying allocation for both; the abstract model
treats them as distinct unless a callee summary proves otherwise
(currently approximated: aliased pointer parameters → UNKNOWN).

### Pointer environment (`PointerEnv`)

After node-transfer lowering, `resolve_memory_effects` performs a forward
dataflow pass to build a `PointerEnv` that maps every SSA pointer value to
a `(region, offset)` pair.  All abstract `Load`/`Store` effects are then
rewritten to `select`/`MemoryStore` on concrete named regions.

```
%ptr = alloca [5 x i32]          → PointerEnv[%ptr] = (fn$stack0, 0)
%gep = getelementptr %ptr, 0, 2  → PointerEnv[%gep] = (fn$stack0, 2)
%v   = load i32, %gep            → select(fn$stack0, 2)
store i32 42, %gep               → MemoryStore { region: fn$stack0, offset: 2, value: 42 }
```

### GEP offset calculation (Step 1 — completed)

`lower_gep_offset` in `adapter.rs` walks the GEP type chain using
`LLVMGetGEPSourceElementType` and `TargetData`:

- **Pointer dereference** (first index): `index × store_size(pointee) / 4`
- **Array element** (`[N × T]`): `index × store_size(T) / 4`
- **Struct field** (constant index into struct): `offset_of_element(struct, idx) / 4`

All offsets are normalized to i32 units (divide byte offset by 4) so the
existing integer-array tests continue to work with element indices 0, 1, 2, …

The `TargetData` is built once per module from the module's data-layout string
(stored in `FunctionGraph::data_layout_str`) and threaded through the lowering
pipeline.

### Per-field struct regions (Step 2 — done)

Currently a struct `alloca` maps to a single integer-array region.  To reason
about individual fields without array-theory, each struct alloca will be split
into one region per field:

```
alloca %Foo   →   fn$s$x  (for field x: i32)
              →   fn$s$y  (for field y: i64)
```

A store to `s.x` becomes:

```
MemoryStore { region: "fn$s$x", offset: 0, value: v }
```

leaving `fn$s$y` completely untouched.  This removes the need for array-theory
reasoning when verifying field-level invariants.

**Changes required:** `resolve_memory_effects` in `adapter.rs`, the `PointerEnv`
binding structure (track field splits per alloca), and `abstract_cfg.rs` WP rules.

---

## Heap Memory Model (planned — Step 4)

### Problem

`malloc` / `new` return opaque pointers at runtime.  The current model only
tracks stack allocas (whose addresses are statically known).  Heap objects
require a different treatment because:

1. Multiple call sites may alias the same underlying allocation.
2. Allocation size is often dynamic (unknown at analysis time).
3. Deallocation (`free` / `delete`) may invalidate a region mid-execution.

### Proposed model

**Call-site regions.** Each `malloc` / `new` call site in the source is treated
as a distinct named region `heap$N` where `N` is a stable identifier (e.g. the
LLVM instruction counter or source location hash):

```
%p = call i8* @malloc(...)   →  heap$call42   (fresh region per call site)
%q = call i8* @malloc(...)   →  heap$call87
```

This is a standard **allocation-site abstraction**: all runtime objects
allocated at the same call site share a single abstract region.  It is sound
for programs that do not mix results from different call sites.

**Pointer tracking.** The `PointerEnv` is extended to map heap pointer SSA
values to `(heap$N, offset)` pairs using the same machinery as stack pointers.
GEP offsets on heap pointers use the same type-aware `lower_gep_offset` logic.

**Aliasing over-approximation.** When a pointer of unknown provenance is stored
into memory (a `PointerStore` whose region cannot be resolved), all heap regions
are havoced — their contents become unconstrained.  This is sound but may
produce `UNKNOWN` for programs with complex aliasing.

**Free / delete.** `free(p)` havoces the region that `p` points to.  No
use-after-free reasoning is attempted; the model assumes well-typed programs.

**Prerequisite.** An alias analysis pass before lowering is needed to tell the
adapter which heap pointers can alias.  Without it, every store through an
unknown pointer havoces all heap regions (the over-approximation above).

### Interaction with the bidirectional analysis

The bidirectional analysis treats heap regions exactly like stack regions:

- **Forward (reach):** a `MemoryStore` to `heap$N` narrows the reachable states
  for that region.
- **Backward (state):** a `select(heap$N, offset)` in the assertion obligation
  propagates a constraint on the heap region's contents backward through the
  CFG.
- **Combined check:** `reach AND state` infeasibility at entry proves the
  assertion regardless of whether the memory is stack or heap.

The only difference is that heap regions start unconstrained (no `alloca`
initialisation), so the reachable-state formula begins with `True` for heap
rather than whatever the alloca initialisation implies.

### Summary

| Concept           | Stack (current)        | Heap (planned)            |
|-------------------|------------------------|---------------------------|
| Region source     | `alloca` instruction   | `malloc`/`new` call site  |
| Region name       | `fn$stackN`            | `heap$callN`              |
| Aliasing          | distinct by default    | call-site abstraction     |
| Unknown store     | havoces one region     | havoces all heap regions  |
| Deallocation      | end of scope (implicit)| `free` havoces region     |
| Prerequisite      | none                   | alias analysis pass       |

---

## C++ Stack Objects (Step 3 — done)

C++ methods compile to functions with an implicit `*this` pointer parameter.
The adapter already treats pointer parameters as `ext_region` symbols
(`fn$__ext_N`).  With per-field regions in place (Step 2), struct field
accesses through `*this` emit `StructFieldGep` and redirect to
`ext_0$f{N}` — the same mechanism as local struct allocas.  At the call
site, return-summary injection substitutes the ext region with the caller's
actual allocation, connecting the callee's field writes to the caller's
concrete object.

Constructors (`@_ZN3FooC1Ev`) and destructors (`@_ZN3FooD1Ev`) are
regular functions in the LLVM IR — no special handling needed.  Templates
and inheritance are transparent at the IR level (they compile down to
concrete struct types).

What is **not** covered here: heap-allocated objects (`new` / `delete` —
Step 4) and virtual dispatch (Step 5), both of which require additional
analysis passes.

---

## Virtual Dispatch (Step 5)

`call %vtable_fn_ptr(...)` is an indirect call with no static callee.  This
requires a points-to / class-hierarchy analysis pass that maps each virtual
call site to the set of concrete callees, then either:

- inlines each candidate and checks under the union, or
- builds per-class summaries and joins them at the call site.

This is the most complex piece and is independent of Steps 1–4.
