# TODO

## Current Backlog

- add real-valued lowering so fixtures like `tests/flow/float_compare.c` are
  analyzed instead of reported as unsupported
- strengthen cyclic procedure handling:
  observer-invariant synthesis covers pointer-parameter looping callees; tighter
  invariant checking and broader callee patterns (non-pointer return values)
  remain open
- decide whether the driver should gain best-effort module analysis internally
  instead of relying on the CLI fallback path
- broaden cast/instruction coverage beyond the current integer/boolean subset
- decide whether `assertions::translation` should become a CLI input path or
  remain a library-only component
- keep the loop-invariant provider / LLM path aligned with the active checker
- tighten and document the current call-summary contract, especially what kinds
  of return relations are inferred and reused soundly

## Richer Structures (C structs → C++ classes)

Phased plan for supporting structured types beyond flat integer arrays.
Full design (stack + heap model) is in `MEMORY_MODEL.md`.

### Step 1 — Fix struct/aggregate GEP layout (done)

`lower_gep_offset` now walks the GEP type chain using `LLVMGetGEPSourceElementType`
and `TargetData` (`LLVMOffsetOfElement` / `LLVMStoreSizeOfType`).  All offsets are
normalised to i32 units.  `TargetData` is built once per module from
`FunctionGraph::data_layout_str` and threaded through to the GEP lowering.

What this unlocks: C structs with scalar fields, C++ POD classes,
mixed-width structs (e.g. `{i32, i64}`), nested structs.

### Step 2 — Per-field memory regions

Currently one `alloca` maps to one integer-array region. For a struct with
`n` fields the SMT solver must reason about array indices to distinguish fields,
which is imprecise.

Plan: in `resolve_memory_effects`, split a struct alloca into one named region
per field:
  `alloca %Foo` → regions `fn$s$x`, `fn$s$y`, ...

A `store` to `s.x` becomes `MemoryStore { region: "fn$s$x", offset: 0, value }`,
leaving `fn$s$y` completely untouched. This makes field-level invariants
expressible without array-theory reasoning.

Changes: `adapter.rs` (`resolve_memory_effects`), the `PointerEnv` binding
structure (needs to track field splits), and `abstract_cfg.rs` WP rules.

### Step 3 — Stack-allocated C++ objects

Free once Steps 1+2 are done. C++ methods compile to functions with an
implicit `*this` pointer parameter, which the adapter already handles as an
`ext_region`. Constructors and destructors are regular functions; they work
once struct fields do. Templates and inheritance are transparent at the IR
level (they compile to concrete structs).

### Step 4 — Heap model

`malloc`/`new` return opaque pointers; the current model only tracks stack
allocas. Plan: treat each `malloc` call site as a fresh named region
(e.g. `heap$call_site_N`). Aliasing across sites is over-approximated by
havocing all heap regions at unknown pointer stores. This is sound but may
produce `UNKNOWN` for programs that alias heap regions.

Prerequisite: alias analysis pass before lowering so the adapter knows which
heap pointers can alias.

### Step 5 — Virtual dispatch

`call %vtable_fn_ptr(...)` is an indirect call — no static callee name to
look up. This requires a points-to / class-hierarchy analysis pass that maps
each virtual call site to the set of possible concrete callees, then either:
- inlines each candidate and checks under the union, or
- builds per-class summaries and joins them at the call site.

This is the most complex piece and is independent of Steps 1–4.
