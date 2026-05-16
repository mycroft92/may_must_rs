# Memory Model Design

This document describes the memory model used by the bidirectional may/must
analysis, organised by implementation status.

**Done (Steps 1–3):** stack allocas, type-aware GEP offsets, per-field struct
regions, C++ stack objects via `*this`.

**Open (Steps 4–5):** heap model (`malloc`/`new`) and virtual dispatch.

---

## Stack Memory Model (Steps 1–3 — done)

### Regions

Each local `alloca` in a function is assigned a distinct named array region
during lowering (`adapter.rs`):

```
alloca i32           → region  fn$stack0
alloca [5 x i32]     → region  fn$stack1
alloca %Foo          → region  fn$stack2   (base region; fields go to fn$stack2$fN)
```

Each region is an abstract integer array `Memory` in the SMT encoding.
Reads and writes become `select` / `store` operations on the named array.

Pointer parameters are treated as external regions:

```
fn(int *p, int *q)  → ext regions  fn$__ext_0,  fn$__ext_1
```

The caller may pass the same underlying allocation for both; the abstract model
treats them as distinct unless a callee summary proves otherwise
(currently approximated: aliased pointer parameters → UNKNOWN).

### Pointer environment (`PointerEnv`)

After node-transfer lowering, `resolve_memory_effects` performs a forward
dataflow pass to build a `PointerEnv` mapping every SSA pointer to a
`(region, offset)` pair.  All abstract `Load`/`Store` effects are rewritten
to `select`/`MemoryStore` on concrete named regions.

```
%ptr = alloca [5 x i32]          → PointerEnv[%ptr] = (fn$stack0, 0)
%gep = getelementptr %ptr, 0, 2  → PointerEnv[%gep] = (fn$stack0, 2)
%v   = load i32, %gep            → select(fn$stack0, 2)
store i32 42, %gep               → MemoryStore { region: fn$stack0, offset: 2, value: 42 }
```

### Step 1 — Type-aware GEP offsets (done)

`lower_gep` in `adapter.rs` walks the GEP type chain using
`LLVMGetGEPSourceElementType` and `TargetData`:

- **First index** (pointer-level stride): `index × store_size(SrcTy) / 4`
- **Array element** (`[N × T]`): `index × store_size(T) / 4`
- **Struct field** (constant index into struct): `offset_of_element(struct, idx) / 4`

All offsets are normalised to i32 units (divide byte offset by 4).  `TargetData`
is built once per module from `FunctionGraph::data_layout_str` and threaded
through the lowering pipeline.

### Step 2 — Per-field struct regions (done)

When `lower_gep` detects the pure struct-field pattern (source element type =
Struct, indices = `[0, N]`), it emits `TransferEffect::StructFieldGep` instead
of `GetElementPtr`.  `resolve_memory_effects` then binds the result pointer to
a dedicated region `{base}$f{N}` at offset 0:

```
alloca %Foo           → base region  fn$stack0
gep %Foo* %s, 0, 0   → PointerEnv[%fp0] = (fn$stack0$f0, 0)
gep %Foo* %s, 0, 1   → PointerEnv[%fp1] = (fn$stack0$f1, 0)
store 3, %fp0        → MemoryStore { region: fn$stack0$f0, offset: 0, value: 3 }
store 7, %fp1        → MemoryStore { region: fn$stack0$f1, offset: 0, value: 7 }
```

Each field lives in its own SMT array — no array-theory lemmas needed to
separate `s.x` from `s.y`.  Nested struct fields chain naturally:
`gep(gep(alloca))` → `fn$stack0$f1$f2`.

### Step 3 — C++ stack objects (done)

C++ methods compile to functions with an implicit `*this` pointer parameter.
The adapter already treats pointer parameters as `ext_region` symbols
(`fn$__ext_N`).  With per-field regions in place, struct field accesses through
`*this` emit `StructFieldGep` and redirect to `__ext_0$f{N}` — the same
mechanism as local struct allocas.  At the call site, return-summary injection
substitutes the ext region with the caller's actual allocation.

Constructors (`@_ZN3FooC1Ev`) and destructors (`@_ZN3FooD1Ev`) are regular
functions in the LLVM IR — no special handling needed.  Templates and
single-inheritance classes are transparent at the IR level.

---

## Flat Address Layout — ptrtoint / inttoptr (done)

### Problem

LLVM programs, especially CIL-lowered C, routinely convert pointers to integers
for equality tests and pointer arithmetic:

```llvm
%a  = ptrtoint ptr %p to i32        ; pointer → integer address
%b  = ptrtoint ptr %q to i32
%eq = icmp eq %a, %b                ; pointer equality via integer comparison

%f  = ptrtoint ptr %field to i32    ; container_of pattern
%s  = add i32 %f, -4               ; subtract field offset → struct base
%p  = inttoptr i64 %s to ptr        ; recover enclosing struct pointer
```

Without a concrete address model these were `UnsupportedInstruction` errors.
Modelling addresses as free symbolic constants introduces **false equalities**:
Z3 can set `addr_A = 0` and `addr_B = 2`, making `(region A, offset 3)` and
`(region B, offset 1)` both evaluate to `3`.

### Encoding

Each named region is assigned a concrete, non-overlapping integer base address
(`src/common/flat_layout.rs`):

```
base(region_0) = 0
base(region_1) = STRIDE          (STRIDE = 4096)
base(region_2) = 2 × STRIDE
…
```

Regions are registered in a fixed order during the `adapt_procedure` pre-pass:
stack allocas (in vertex order), then ext pointer params, then global variables
(first-reference order).

**`ptrtoint ptr %p to iN`** — where `%p → (region, offset)` in `PointerEnv`:

```
→  Assign { result, Term::Int(base(region) + offset) }
```

The result is a **concrete integer constant** — no free Z3 variables, no false
equalities possible.

**`inttoptr iN %x to ptr`** — where `%x` was produced by ptrtoint or
subsequent constant arithmetic (`add`, `sub`, `mul`):

```
eval_flat_addr(%x, flat_int_vars) → addr
flat_layout.region_at(addr)       → (region, offset)
→  env.bind(result_ptr, region, Term::Int(offset))
```

Arithmetic on integer variables is propagated through a `flat_int_vars` side
table so that the full `ptrtoint → add/sub → inttoptr` chain resolves.

If the integer value is not statically evaluable (e.g., loaded from memory as
`select(region, k)`), the `inttoptr` result is left unbound — conservative,
may produce `UNKNOWN` but never unsound.

### Guarantees

- `flat_addr(A, i) ≠ flat_addr(B, j)` for any two distinct regions `A ≠ B`
  and offsets `i, j` with `|i|, |j| < STRIDE`. No false pointer equalities.
- The stride does not imply adjacency: two consecutive regions in the layout
  are not assumed to be adjacent in memory. Arithmetic that crosses region
  boundaries (e.g. pointer arithmetic past the end of an allocation) is left
  unresolved.

### Limitation

Pointers stored as integers and reloaded from memory are not tracked:

```c
int x;
unsigned addr = (unsigned)&x;   // ptrtoint → concrete flat addr ✓
store_to_memory(addr);          // addr written to a memory cell
unsigned v = load_from_memory();// v = select(region, k) — not in flat_int_vars
int *p = (int *)v;              // inttoptr left unbound → UNKNOWN
```

This covers the linked-list pattern where `next`/`prev` are stored as integers
in struct fields.  Full support requires combining the flat layout with the heap
model (Step 4) and symbolic evaluation of memory-loaded integer addresses.

---

## Heap Memory Model (Step 4 — planned)

### Problem

`malloc` / `new` return opaque pointers at runtime.  The current model only
tracks stack allocas.  Heap objects need different treatment because:

1. Multiple call sites may alias the same underlying allocation.
2. Allocation size is often dynamic.
3. Deallocation (`free` / `delete`) may invalidate a region mid-execution.

### Proposed model

**Call-site regions.** Each `malloc` / `new` call site is treated as a distinct
named region `heap$callC` (C = stable per-call-site id):

```
%p = call i8* @malloc(...)   →  heap$call42
%q = call i8* @malloc(...)   →  heap$call87
```

All runtime objects allocated at the same call site share one abstract region
(standard allocation-site abstraction — sound when results don't cross-alias).

**Per-field heap struct regions.** When a `malloc` result is cast to a struct
pointer type and accessed via `StructFieldGep`, the existing field-sensitive
machinery creates dedicated sub-regions automatically — no special-casing is
needed:

```
%raw = call i8* @malloc(sizeof(Foo))     →  pts(%raw) = { heap$call42 }
%p   = bitcast i8* %raw to Foo*          →  pts(%p)   = { heap$call42 }
%fp0 = gep Foo* %p, 0, 0  (StructFieldGep, field 0)
                                         →  pts(%fp0) = { heap$call42$f0 }
%fp1 = gep Foo* %p, 0, 1  (StructFieldGep, field 1)
                                         →  pts(%fp1) = { heap$call42$f1 }
store i32 42, %fp0  →  MemoryStore { region: heap$call42$f0, offset: 0, value: 42 }
store i32  7, %fp1  →  MemoryStore { region: heap$call42$f1, offset: 0, value:  7 }
```

Each heap struct field gets its own SMT array — the same precision as stack
struct fields (Step 2), requiring no array-theory reasoning to separate fields.
The alias analysis (Step 4 prerequisite, see `ALIAS_ANALYSIS.md`) propagates
these `$fN` subscripts through the points-to sets so that field-level havocing
is precise even for heap objects.

**Pointer tracking.** `PointerEnv` is extended to map heap pointer SSA values
to `(heap$callC, offset)` or `(heap$callC$fN, 0)` pairs using the same
machinery as stack pointers.  GEP offsets use the same `lower_gep` logic
(Steps 1–2 apply).

**Aliasing over-approximation.** A `PointerStore` whose region cannot be
resolved havoces all heap regions — sound but may produce `UNKNOWN` for
programs with complex aliasing.

**Free / delete.** `free(p)` havoces the region `p` points to.  No
use-after-free reasoning; well-typed programs are assumed.

**Prerequisite (complete).** The alias analysis pass (`src/common/alias_analysis.rs`)
is implemented and wired into the lowering pipeline.  `resolve_memory_effects` uses
`AliasResult` to bind `PointerStore`/`PointerLoad` operations that the local
`PointerEnv` cannot resolve.  See `ALIAS_ANALYSIS.md` for the full design.

### Interaction with the bidirectional analysis

Heap regions behave identically to stack regions in the analysis:

- **Forward (reach):** `MemoryStore` to `heap$N` narrows reachable states.
- **Backward (state):** `select(heap$N, offset)` propagates constraints backward.
- **Combined check:** `reach AND state` infeasibility at entry → Verified,
  regardless of whether the memory is stack or heap.

Heap regions start unconstrained (no `alloca` initialisation), so the
reachable-state formula begins with `True` for heap.

### Stack vs heap summary

| Concept           | Stack (done)            | Heap (planned)            |
|-------------------|-------------------------|---------------------------|
| Region source     | `alloca` instruction    | `malloc`/`new` call site  |
| Region name       | `fn$stackN`, `fn$stackN$fM` | `heap$callC`, `heap$callC$fM` |
| Aliasing          | distinct by default     | call-site abstraction     |
| Unknown store     | havoces one region      | havoces all heap regions  |
| Deallocation      | end of scope (implicit) | `free` havoces region     |
| Prerequisite      | none                    | alias analysis (done — see `ALIAS_ANALYSIS.md`) |

---

## Virtual Dispatch (Step 5 — planned)

`call %vtable_fn_ptr(...)` is an indirect call with no static callee.  This
requires a points-to / class-hierarchy analysis pass that maps each virtual
call site to the set of possible concrete callees, then either:

- inlines each candidate and checks under the union, or
- builds per-class summaries and joins them at the call site.

This is the most complex piece and is independent of Steps 1–4.
