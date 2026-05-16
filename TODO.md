# TODO

## Strategic Direction

Broaden SV-COMP coverage (more categories, bitvector theory, richer instruction
support) but **correctness gates coverage** — do not add support for a new feature
if doing so requires an unsound approximation.  Ordering of priorities:

1. **Fix unsound approximations first** — an analysis that silently emits a wrong
   `Verified` on a benchmark that is actually unsafe is worse than one that emits
   `UNKNOWN` or `ERROR`.
2. **Extend instruction coverage** — instructions currently producing
   `UnsupportedInstruction` errors should be modelled soundly (returning `UNKNOWN`
   when the model is too weak) before new categories are attempted.
3. **Broaden category/theory support** — bitvector arithmetic, new SV-COMP
   categories, heap model — only after the above two layers are stable.

## Soundness Debt (fix before broadening)

These items can produce a **wrong `Verified`** on a program that is actually unsafe.
Fix in order:

- **`udiv`/`urem` treated as signed** — `udiv i32 a b` and `sdiv i32 a b` are both
  lowered to `Term::div(lhs, rhs)`.  In the unbounded-Int model, if an operand is
  negative (possible for values from unmodeled calls), the result differs from C
  unsigned semantics.  Fix: inject `Assume(lhs >= 0)`, `Assume(rhs >= 0)`, and
  `Assume(result >= 0)` for `udiv`; `Assume(lhs >= 0)` and `Assume(result >= 0)`
  for `urem`.  This is analogous to the ZExt `>= 0` injection and equally cheap.

- **Unsigned icmp collapsed to signed** — `get_icmp_predicate` in `llvm_wrap.rs`
  maps `ult/ule/ugt/uge` to the same `</<=/>/>=` symbols as their signed
  counterparts.  For operands the analysis can prove are non-negative this is
  sound; for values from unmodeled calls or signed arithmetic it is not.  Fix:
  either propagate a sign flag through the comparison and inject `>= 0` constraints
  on operands of unsigned comparisons, or emit a conservative `UNKNOWN` when a
  comparison operand cannot be proved non-negative.

## Known Benchmark Gaps (as of `1e7fb97`, 2026-05-16)

Reference: `benchmarks/sv-comp/RESULTS.md`, latest run.
Totals: 51 UNKNOWN · 5 UNSOUND · 7 MISSED · 105 files.

### UNSOUND (wrong `Verified` on unsafe program — false safe)

- `c/loops/count_up_down-1` — expected SAFE, got UNSAFE
- `c/loops/linear_sea.ch` — expected SAFE, got UNSAFE
- `c/loops/trex03-2` — expected SAFE, got UNSAFE
- `c/loops/veris.c_NetBSD-libc_loop.i` — expected SAFE, got UNSAFE
- `c/loop-invariants/bin-suffix-5` — expected SAFE, got UNSAFE

`count_up_down-1` and `trex03-2` were previously fixed (in `970a9dd`) by
ZExt/SExt `Assume` bounds in WP, but the `TypeBound` fix (which restores loop
invariant synthesis) removes these from WP. The underlying root cause for
these two is likely **unsigned icmp collapsed to signed** — fix that item
first before revisiting.

### MISSED (wrong verdict on unsafe program)

- `c/loops/array-2`
- `c/loops/ludcmp`
- `c/loops/nec20`
- `c/loops/sum01_bug02.i`
- `c/loops/sum04-1.i`
- `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i`
- `c/loop-invariants/linear-inequality-inv-b` — expected UNSAFE, got SAFE

### UNKNOWN breakdown by category

locks 13 · loops 33 · loop-crafted 5 · loop-invariants 0.

## Instruction Coverage (sound but lossy — produce ERROR/UNKNOWN today)

- **Integer bitwise And/Or/Xor** — currently only lowered for `i1`-typed values
  (mapped to Boolean `and`/`or`/`xor`).  Integer-width variants fall through to
  `Nop`, leaving the result variable unconstrained → `UNKNOWN` for any program
  that uses bitmask operations.  Fix: lower as `Rem(lhs, 2^w)` or emit an
  `Assume(result >= 0 && result <= max(|lhs|, |rhs|))` as a conservative
  overapproximation, then refine toward bitvector modelling later.

- **Shifts (`Shl`, `LShr`, `AShr`)** — not in the opcode match → fall to the `_`
  wildcard → `UnsupportedInstruction` error for any program that uses shifts.
  Fix: lower `shl x, n` as `Mul(x, 2^n)` when `n` is a constant (sound for
  non-negative `x`); `lshr`/`ashr` as `Div(x, 2^n)`.  Constant shifts cover the
  majority of SV-COMP uses.

## Long-term / Structural

- **Integer overflow / wrap-around** — the unbounded-Int model does not wrap.
  Programs that depend on two's-complement overflow (e.g. `INT_MAX + 1 < 0`
  checks) are not correctly modelled.  Long-term fix: switch scalars to the SMT
  BitVector theory, or add modular-arithmetic axioms selectively.

## Current Backlog

- **type-based domain bounds in the adapter** — emit `TransferEffect::Assume`
  range constraints directly in `lower_node_transfer` based on LLVM integer
  type widths (e.g. `i8 → [-128, 127]`, `i32 → [-2^31, 2^31-1]`) without
  routing through C-level macros.  Soundness is clear; the challenge is
  performance: naively adding two assumes per arithmetic result caused SMT
  timeouts (array_max_5 regression).  Needs predicate simplification /
  subsumption pass before the solver call, or selective application only at
  widening points (ZExt, SExt, call returns with typed signatures).  Currently
  worked around via `nondet_*()` macros in `verification.h` that inject bounds
  at the C level for SV-COMP nondeterministic inputs.

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
