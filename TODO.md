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

- **`udiv`/`urem` treated as signed** — DONE.  `Assume(lhs >= 0)`, `Assume(rhs >= 0)`,
  `Assume(result >= 0)` already injected for both `udiv` and `urem`.

- **Unsigned icmp collapsed to signed** — DONE (`0.4.2`).  Added `is_unsigned_icmp()`
  to `llvm_wrap.rs`; adapter injects `Assume(lhs >= 0)` and `Assume(rhs >= 0)` before
  any `ult`/`ule`/`ugt`/`uge` comparison so the unbounded-int model cannot admit
  negative operands that bitvector semantics would treat as large unsigned values.

## Known Benchmark Gaps (as of `ea8e6f5`, 2026-05-16)

Reference: `benchmarks/sv-comp/RESULTS.md`, latest run.
Totals: ~51 UNKNOWN · 3 UNSOUND · 7 MISSED · 105 files.
(`count_up_down-1` and `trex03-2` fixed by Hoare-style inductiveness WP in `ea8e6f5`.)

### UNSOUND (wrong `Verified` on unsafe program — false safe)

- `c/loops/linear_sea.ch` — expected SAFE, got UNSAFE
- `c/loops/veris.c_NetBSD-libc_loop.i` — expected SAFE, got UNSAFE
- `c/loop-invariants/bin-suffix-5` — expected SAFE, got UNSAFE

### MISSED (wrong verdict on unsafe program)

- `c/loops/array-2` — needs memory-relational invariant (`menor <= array[0]`)
  to produce BugFound; currently UNKNOWN (see Current Backlog)
- `c/loops/ludcmp`
- `c/loops/nec20`
- `c/loops/sum01_bug02.i`
- `c/loops/sum04-1.i`
- `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i`
- `c/loop-invariants/linear-inequality-inv-b` — expected UNSAFE, got SAFE

### UNKNOWN breakdown by category

locks 13 · loops 33 · loop-crafted 5 · loop-invariants 0.
(`array-1` fixed in v0.9.0 by entry-safety candidate synthesis with Phase-B
discharge — the inductive invariant `(j==0) || (array[0]>=menor)` is accepted
without exit closure and the bidirectional check proves the assertion.)

## Instruction Coverage (sound but lossy — produce ERROR/UNKNOWN today)

- **Integer bitwise And/Or/Xor** — DONE (`0.4.1`).  `And` with non-negative
  constant mask emits `TypeBound(result >= 0 && result <= mask)`.  `Xor` with
  constant `-1` (bitwise NOT) lowers to `result = -x - 1`.  `Or` leaves result
  unconstrained (no useful bound without bitvector range info).

- **Shifts (`Shl`, `LShr`, `AShr`)** — DONE (`0.4.1`).  Constant-amount shifts
  lower to `Mul(x, 2^n)` / `Div(x, 2^n)`.  `LShr` adds a `TypeBound(result >= 0)`.
  Variable shift amounts leave the result unconstrained.  Bitvector-precise
  semantics deferred to long-term BitVector theory work.

- **`unreachable` instruction** — DONE (`0.4.3`).  Emits `Assume(False)`, so
  the backward precondition on any path reaching it is `False` (dead path).
  Marks dead code following noreturn calls (`abort`, `__assert_fail`, `exit`).
  Previously caused spurious `UnsupportedInstruction` errors and `UNKNOWN`
  verdicts on functions that call these routines.

## Long-term / Structural

- **Integer overflow / wrap-around** — the unbounded-Int model does not wrap.
  Programs that depend on two's-complement overflow (e.g. `INT_MAX + 1 < 0`
  checks) are not correctly modelled.  Long-term fix: switch scalars to the SMT
  BitVector theory, or add modular-arithmetic axioms selectively.

## Current Backlog

- **Memory-relational invariant templates** — `c/loops/array-1` is SAFE (v0.9.0)
  via entry-safety candidates.  `c/loops/array-2` correctly returns UNKNOWN (v0.10.1)
  after fixing a soundness bug where variable-valued preheader store facts produced
  tautological invariants that falsely verified the program as SAFE.  The remaining
  gap: a *cross-region relational* candidate generator producing `select(R1,i) <= select(R2,j)`
  templates from assertion postconditions would let the tool report BugFound for
  array-2 (the relational candidate `menor <= array[0]` would fail exit closure since
  `array[0] > menor` is unsatisfied when they are equal) and extend coverage to other
  memory-relational cases.

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

### Step 5 — Virtual dispatch (done, `0.6.0`)

Indirect calls through vtable pointers (`call %vtable_fn_ptr(...)`) are now
resolved to concrete callees at the lowering boundary:

1. **Module-wide vtable map** — `CallSummaryRegistry::scan_graph_vtables`
   reads all vtable globals (handling Clang's `{ [N x ptr] }` struct wrapper)
   and populates a `vtable_map: HashMap<region, Vec<Option<fn_name>>>`.

2. **`ptr_at` side table** — `resolve_memory_effects` tracks
   `ptr_at: HashMap<(region, concrete_offset), (region, Term)>` recording what
   pointer is stored at each memory cell (e.g. the vptr store in a constructor
   propagated via `ReturnSummary::ptr_writes`).

3. **Vtable PointerLoad** — when loading a pointer from a cell that holds a
   vtable region, the vtable map is consulted to insert the resolved function
   name into `fn_ptr_vars`.

4. **IndirectCall rewrite** — `TransferEffect::IndirectCall` is rewritten to
   `TransferEffect::Call { callee }` once the callee is known.

5. **Return summary application** — `apply_pending_return_summaries` now also
   processes resolved indirect calls (second loop over CFG nodes), applying
   callee return summaries exactly as for direct calls.

6. **Field sub-region substitution** — `substitute_ext_regions` now does
   prefix-match on `$f`-suffixed regions so that callee field access through
   `ext_N$fK` maps to the caller's `actual_region$fK`.

Test: `vtable_dispatch_verifies` — `Counter::get()` via virtual dispatch,
assertion `v == 42` verified `Safe`.
