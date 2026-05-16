# TODO

## Current Backlog

- **`assume(cond)` intrinsic support** — add a `may_assume(_Bool)` sentinel
  (mirroring `may_assert`) recognised by `program_graph.rs` and lowered by the
  adapter to `TransferEffect::Assume(cond)` on the call node.  `Assume` already
  exists in the WP engine (`wp_one` returns `cond ⇒ post`); the work is purely
  in the frontend:
  1. Declare `may_assume` in `verification.h` alongside `may_assert`.
  2. Detect `may_assume` calls in `program_graph.rs` (strip from the visible
     graph, record as an `AssumeSite` or emit the assume inline — similar to
     how `may_assert` sites are handled, but as an `Assume` effect rather than
     an obligation).
  3. In `adapter.rs`, lower each `may_assume` call to
     `TransferEffect::Assume(condition)` on the call node, where `condition` is
     the translated argument formula.
  4. Add a unit test: a loop with a precondition `assume(x > 0)` that should
     discharge an assertion `assert(x > 0)` trivially at entry.
  This is the prerequisite for running SV-COMP benchmarks natively, since
  `__VERIFIER_assume` maps directly to `may_assume`.

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

### Step 2 — Per-field memory regions (done)

`TransferEffect::StructFieldGep { target, base, field_index }` is emitted when
`lower_gep` detects a pure struct-field access (source element type = Struct,
two indices [0, N]). `resolve_memory_effects` binds the result pointer to
`{base_region}$f{N}` at offset 0, so loads and stores to different fields land
in separate SMT arrays — no array-theory reasoning needed.

A test (`struct_fields.c`) verifies `p.x == 3`, `p.y == 7`, `p.x + p.y == 10`
with cross-field non-interference checked by the solver.

### Step 3 — Stack-allocated C++ objects (done)

Free once Steps 1+2 are done. `*this` is already an `ext_region`; with
per-field regions (Step 2), field accesses through `*this` emit
`StructFieldGep` and the return-summary machinery substitutes the ext
region with the caller's allocation. Constructors, destructors, templates,
and single-inheritance classes are all transparent at the LLVM IR level.

### Step 4 — Heap model

`malloc`/`new` return opaque pointers; the current model only tracks stack
allocas. Plan: treat each `malloc` call site as a fresh named region
(e.g. `heap$call_site_N`). Aliasing across sites is over-approximated by
havocing all heap regions at unknown pointer stores. This is sound but may
produce `UNKNOWN` for programs that alias heap regions.

**Prerequisite complete:** the alias analysis pass (`src/common/alias_analysis.rs`)
is implemented and wired into the lowering pipeline.  `resolve_memory_effects`
now uses `AliasResult` to bind pointer operations that the local `PointerEnv`
cannot resolve.  The remaining work is wiring `heap$callC` region names into
the adapter so that `malloc` call sites produce `Seed` constraints in the AA
and the lowered CFG contains concrete `MemoryStore` effects for heap writes.

### Step 5 — Virtual dispatch

`call %vtable_fn_ptr(...)` is an indirect call — no static callee name to
look up. This requires a points-to / class-hierarchy analysis pass that maps
each virtual call site to the set of possible concrete callees, then either:
- inlines each candidate and checks under the union, or
- builds per-class summaries and joins them at the call site.

This is the most complex piece and is independent of Steps 1–4.
