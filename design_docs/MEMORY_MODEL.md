# Memory Model Design

This document describes the memory model used by the bidirectional may/must
analysis, organised by implementation status.

**Done (Steps 1–4):** stack allocas, type-aware GEP offsets, per-field struct
regions, C++ stack objects via `*this`, heap call-site abstraction
(`malloc`/`new`/`calloc`), vtable fn-ptr infrastructure.

**Partial (Step 5):** virtual dispatch — vtable slot resolution and
`IndirectCall` rewrite are implemented; pointer write effects in `ReturnSummary`
are not, which prevents full end-to-end virtual dispatch across function
boundaries.

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

## Heap Memory Model (Step 4 — done)

### Problem

`malloc` / `new` return opaque pointers at runtime.  Without a heap model, the
analysis treats their results as unconstrained pointers, producing `UNKNOWN` for
any assertion that depends on heap-allocated state.

### Call-site abstraction

Each `malloc` / `calloc` / `_Znwm` (`new`) / `_Znam` (`new[]`) /
`__cxa_allocate_exception` call site is treated as a distinct named region:

```
%p = call ptr @malloc(...)   →  fn$heap$malloc@0
%q = call ptr @malloc(...)   →  fn$heap$malloc@1
%c = call ptr @_Znwm(...)    →  fn$heap$_Znwm@2
```

The naming scheme is `{function_name}$heap${callee}@{index}` where `index` is a
per-function monotone counter.  All runtime objects allocated at the same call
site share one abstract region — the standard allocation-site abstraction.
Distinct call sites remain distinguishable in `PointerEnv` and in the SMT
encoding, so writes to `%p`'s region never alias writes to `%q`'s region.

The whitelist of recognised allocators lives in `HEAP_ALLOCATORS` at the top of
`src/common/adapter.rs`.

### Implementation: `HeapAlloc` transfer effect

A new `TransferEffect::HeapAlloc { result_ptr: String, region: String }` variant
(in `src/common/abstract_cfg.rs`) is emitted instead of a regular `Call` when
the callee is in `HEAP_ALLOCATORS`.

**WP and SP:** both are identity — a heap allocation does not change existing
memory contents, and the resulting region starts unconstrained.

**PointerEnv binding:** `resolve_memory_effects` in `src/common/adapter.rs`
handles `HeapAlloc` in the same arm as `Alloca`:

```rust
TransferEffect::Alloca { target, region }
| TransferEffect::HeapAlloc { result_ptr: target, region } => {
    env.bind(target.clone(), region.clone(), Term::int(0));
}
```

After this, the heap pointer SSA name maps to `(region, 0)` in the env, so
subsequent GEPs, loads, and stores resolve identically to stack allocas.

### Pre-pass: region naming and FlatLayout registration

`adapt_with_purity_and_summaries` in `src/common/adapter.rs` runs a pre-pass
over all instructions before lowering to collect heap call sites:

```
for instruction in &graph.vertices:
    if opcode == Call && result is pointer-typed:
        if callee ∈ HEAP_ALLOCATORS:
            region = "{fn}$heap${callee}@{index}"
            heap_alloc_regions.insert(instruction, region)
            index += 1
```

Each region is also pre-registered with `FlatLayout` (same call as stack
allocas) so that `ptrtoint` on a heap pointer resolves to a concrete, unique
flat address — preventing false equality between heap and stack pointers.

### Per-field heap struct regions

When a heap pointer is accessed through `StructFieldGep`, the existing
field-sensitive machinery creates `$fN` sub-regions automatically:

```
%raw = call ptr @_Znwm(8)             → PointerEnv[%raw] = (fn$heap$_Znwm@0, 0)
%p   = bitcast ptr %raw to Counter*   → PointerEnv[%p]   = (fn$heap$_Znwm@0, 0)   [alias]
%fp0 = gep Counter* %p, 0, 1          → PointerEnv[%fp0] = (fn$heap$_Znwm@0$f1, 0)
store i32 42, ptr %fp0
    → MemoryStore { region: fn$heap$_Znwm@0$f1, offset: 0, value: 42 }
load i32, ptr %fp0
    → Assign { target: "%v", value: select(fn$heap$_Znwm@0$f1, 0) }
```

Each heap struct field gets its own SMT array — the same precision as stack
struct fields (Step 2).  No array-theory reasoning is needed to separate fields.

### Interaction with the bidirectional analysis

Heap regions behave identically to stack regions:

- **Forward (reach):** `MemoryStore` to `heap$...` narrows reachable states.
- **Backward (state):** `select(heap$..., k)` propagates constraints backward.
- **Combined check:** `reach AND state` infeasibility at entry → Verified,
  regardless of whether the memory is stack or heap.

Heap regions start fully unconstrained (no initialisation value), so they do
not narrow `reach` until a `MemoryStore` is encountered.

### Stack vs heap summary

| Concept           | Stack (Steps 1–3)        | Heap (Step 4)                          |
|-------------------|--------------------------|----------------------------------------|
| Region source     | `alloca` instruction     | `malloc`/`new`/etc. call site          |
| Region name       | `fn$stackN`, `fn$stackN$fM` | `fn$heap$malloc@N`, `fn$heap$malloc@N$fM` |
| Aliasing          | distinct by default      | call-site abstraction (same site = same region) |
| Field sub-regions | `StructFieldGep` → `$fN` | same — automatic                       |
| Unknown store     | havoces one region       | havoces all heap regions               |
| Deallocation      | end of scope (implicit)  | `free`/`delete` not yet modelled       |
| FlatLayout entry  | pre-pass, vertex order   | pre-pass, call-site order              |

### Test

`tests/heap_distinct.c` + `may_must_analysis::driver::tests::heap_distinct_malloc_sites_do_not_alias`
verify that two distinct `malloc` call sites do not alias, so a write through
`%b` cannot clobber `*a`:

```c
int *a = malloc(sizeof(int));
int *b = malloc(sizeof(int));
*a = 1;
*b = 2;
may_assert(*a == 1);   // Verified
```

---

## Virtual Dispatch (Step 5 — partial)

### What is implemented

#### `IndirectCall` transfer effect

A new `TransferEffect::IndirectCall { callee_ptr: String, memory_effect }` variant
(in `src/common/abstract_cfg.rs`) is emitted when a `call ptr %fn(...)` instruction
has no statically known callee.  WP and SP are identical to `Call`.

In `resolve_memory_effects` (`src/common/adapter.rs`), if `callee_ptr` has been
resolved to a concrete function name via the vtable lookup (see below), the
`IndirectCall` is rewritten to a concrete `Call`:

```rust
TransferEffect::IndirectCall { callee_ptr, memory_effect } => {
    if let Some(callee) = fn_ptr_vars.get(&callee_ptr) {
        rewritten.push(TransferEffect::Call { callee: callee.clone(), memory_effect });
    } else {
        rewritten.push(TransferEffect::IndirectCall { callee_ptr, memory_effect });
    }
}
```

#### Vtable constant expression GEP resolution

LLVM IR encodes vptr stores as:

```llvm
store ptr getelementptr inbounds ([3 x ptr] @_ZTV7Counter, i64 0, i64 2),
      ptr %slot
```

The value is a `ConstantExpr` GEP of a global variable — not an SSA
instruction.  `as_const_gep_of_global()` in `src/common/llvm_utils/llvm_wrap.rs`
detects this pattern:

```rust
pub fn as_const_gep_of_global(&self) -> Option<(String, i64)>
```

It returns `(global_name, offset)` where `offset` is the sum of all GEP index
operands.  `resolve_memory_effects` uses this to bind the ConstantExpr to a
`global$<name>` region at the computed offset, making it visible in `PointerEnv`
before the main forward pass runs.

#### Vtable fn-ptr element extraction

`constant_fn_ptr_elements()` in `src/common/llvm_utils/llvm_wrap.rs` reads the
initialiser of a global constant array and extracts each element as a function
name (or `None` for null / non-function entries):

```rust
pub fn constant_fn_ptr_elements(&self) -> Option<Vec<Option<String>>>
```

It handles: direct `Function` references, `ConstantPointerNull`, and
`ConstantExpr` bitcasts of functions.  It is safe to call on any global value —
non-array types return `None`.

**Safety note:** `LLVMGetOperand` is only safe on `ConstantExpr` values, not on
plain constants (`ConstantInt`, `GlobalVariable` refs, etc.).  The inner helper
`constant_fn_ptr_elements_inner` guards every `LLVMGetOperand` call with an
`!LLVMIsAConstantExpr(elem).is_null()` check.

#### Vtable map and fn-ptr variable side table

`resolve_memory_effects` builds two side tables during its pre-scan phase:

- `vtable_fn_ptrs: HashMap<String, Vec<Option<String>>>` — maps each global
  region name (e.g. `global$_ZTV7Counter`) to the per-slot function names
  extracted by `constant_fn_ptr_elements`.  Built eagerly during the GEP
  ConstantExpr pre-scan.

- `fn_ptr_vars: HashMap<String, String>` — maps SSA pointer names to function
  names.  Populated when a `PointerLoad` from a known vtable region at a
  concrete index resolves to a function name; consumed by the `IndirectCall` arm.

The `PointerLoad` arm (in the main forward pass) performs the vtable lookup:

```rust
if let Term::Int(idx) = &binding.offset {
    if let Some(entries) = vtable_fn_ptrs.get(&binding.region) {
        if let Some(Some(fn_name)) = entries.get(*idx as usize) {
            fn_ptr_vars.insert(target_ptr.clone(), fn_name.clone());
            // do NOT bind target_ptr in PointerEnv — it's a fn ptr, not a data ptr
        }
    }
}
```

### Known limitation: pointer write effects in `ReturnSummary`

Full C++ virtual dispatch (constructor stores vptr, virtual call in caller)
does not verify end-to-end because:

1. The constructor's vptr store is a `PointerStore` that rebinds the `this`
   pointer SSA name to the vtable region.  This binding lives in the
   constructor's local `PointerEnv` only.

2. `ReturnSummary` encodes integer value relations (the `__retval` formula).
   It does not encode pointer write effects — so the constructor's vptr write
   is not visible to the caller.

3. In the calling function, the `PointerLoad` of the vptr field reads from the
   object region (not the vtable region), producing an unconstrained pointer.
   The `IndirectCall` stays unresolved; its return value is unconstrained.
   Z3 can assign it 0, making `v == 42` unsatisfiable → false `UNSAFE`.

This is a **precision** issue, not a soundness bug: the tool never claims
`Verified` for an actually-unsafe program.

**Fix — pointer store-to-load forwarding:** implemented.  See the next section.

### Pointer store-to-load forwarding (`ptr_at` map)

#### Within-function

`resolve_memory_effects` in `src/common/adapter.rs` maintains a side table:

```
ptr_at: HashMap<(region: String, offset: i64), (region: String, offset: Term)>
```

`ptr_at[(R, k)] = (VR, VO)` means: the memory cell `(R, k)` currently holds a
pointer to `(VR, VO)`.

**`PointerStore { target_slot, value_ptr }`** — instead of rebinding `env[target_slot]`
(the old SSA-alias approach), the new code writes to `ptr_at`:

```
if env[target_slot] = (R, Int(k)) and env[value_ptr] = (VR, VO):
    ptr_at[(R, k)] = (VR, VO)
```

In the constructor body this records
`ptr_at[("fn$__ext_0", 0)] = ("global$_ZTV7Counter", 2)`.

**`PointerLoad { target_ptr, source_slot }`** — before the vtable fn-ptr check,
`ptr_at` is consulted:

```
if env[source_slot] = (R, Int(k)):
    if ptr_at[(R, k)] = (VR, VO):
        env[target_ptr] = (VR, VO)      ← indirect through stored pointer
    else:
        env[target_ptr] = (R, k)         ← old conservative fallback
```

Now, a subsequent `PointerLoad` from `env[target_ptr] = (global$_ZTV7Counter, 2)` hits
the vtable fn-ptr check and resolves to `_ZNK7Counter3getEv`.

#### Cross-function — `PointerWriteEffect` in `ReturnSummary`

`ptr_at` entries for external regions (ext params) are exported via
`PointerWriteEffect` (in `src/common/adapter.rs`):

```rust
pub struct PointerWriteEffect {
    pub param_index: usize,   // which pointer parameter was written through
    pub param_offset: i64,    // offset within the param's region
    pub target_region: String,
    pub target_offset: Term,
}
```

`ReturnSummary` now carries `ptr_writes: Vec<PointerWriteEffect>`.  The
extraction step (`extract_ptr_writes`) scans the callee's final `ptr_at` for
entries whose region matches `callee$__ext_N` and emits one
`PointerWriteEffect` per entry.

`AdaptedProcedure` stores the final `ptr_at` so driver.rs can extract
`ptr_writes` when building the `ReturnSummary`.

#### Cross-function application in `resolve_memory_effects`

When `resolve_memory_effects` encounters a `Call { callee }` effect and the
callee has `ptr_writes` in its registered summary, it:

1. Looks up the original LLVM instruction via `node_to_instruction[node_id]` to
   get the actual call arguments.
2. For each `PointerWriteEffect { param_index, param_offset, target_region, target_offset }`:
   - Finds `env[actual_arg[param_index]]` = `(caller_region, caller_base_offset)`.
   - Adds `ptr_at[(caller_region, caller_base_offset + param_offset)] = (target_region, target_offset)`.
3. Subsequent `PointerLoad`s in the same function see the updated `ptr_at` and
   resolve the vtable correctly.

#### Call chain propagation

The constructor chain `main → C1 (_ZN7CounterC1Ev) → C2 (_ZN7CounterC2Ev)` is
handled by the driver's bottom-up fixed-point iteration:

| Iteration | What happens |
|-----------|-------------|
| 1 | C2 processed: ptr_at[(ext_0, 0)] = vtable → C2 ReturnSummary.ptr_writes populated |
| 2 | C1 processed with C2's summary: Call C2 → ptr_at[(ext_0, 0)] = vtable propagated → C1 ReturnSummary.ptr_writes populated |
| 3 | main processed with C1's summary: Call C1 → ptr_at[(heap$_Znwm@0, 0)] = vtable → PointerLoad %8 → env[%8] = (global$vtable, 2) → PointerLoad %10 → fn_ptr_vars[%10] = Counter::get → IndirectCall resolved ✓ |

For functions with no integer return value (like constructors returning `void`
or an opaque `this` pointer that never appears in an integer formula),
`ptr_write_summary_if_any` in `src/common/adapter.rs` creates a
`ReturnSummary` with `relation: Formula::True` purely to carry the ptr_writes.
This ensures the constructor's side effects propagate even when
`compute_return_summary` returns `None`.

### Test

`tests/vtable_dispatch.cpp` exercises the pattern.  The test
`vtable_dispatch_verifies` in `src/may_must_analysis/driver.rs` asserts that the
assertion `v == 42` is `Verified` end-to-end, with the vtable resolved through
the C1→C2 constructor chain and `Counter::get` returning `value_` = 42.
