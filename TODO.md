# TODO

## Strategic Direction

Broaden SV-COMP coverage (more categories, bitvector theory, richer instruction
support) but **correctness gates coverage** — do not add support for a new feature
if doing so requires an unsound approximation.

Priority order:

1. **Fix unsound approximations first.** A wrong `Verified` on an unsafe
   program is worse than `UNKNOWN` or `ERROR`.
2. **Tighten memory precision.** Many UNKNOWNs come from over-conservative
   havoc'ing, not from genuine theory gaps — fixing these is cheap progress.
3. **Extend instruction coverage.** Instructions currently producing
   `UnsupportedInstruction` should be modelled soundly (returning `UNKNOWN` if
   the model is too weak) before new categories are attempted.
4. **Broaden category/theory support** — bitvector arithmetic, new SV-COMP
   categories, heap model — only after the above three layers are stable.

## Soundness Debt (fix before broadening)

These items can produce a **wrong `Verified`** on a program that is actually unsafe.

- **`udiv`/`urem` treated as signed** — DONE.  `Assume(lhs >= 0)`, `Assume(rhs >= 0)`,
  `Assume(result >= 0)` already injected.
- **Unsigned icmp collapsed to signed** — DONE (`0.4.2`).  Adapter injects
  `Assume(lhs >= 0)` and `Assume(rhs >= 0)` before any `ult/ule/ugt/uge`.
- **Phase-B bypassing exit closure** — DONE (`0.11.0`).  Removed for assertion
  verification.  See [[feedback_phase_b_soundness]] in memory.

## Known Benchmark Gaps (as of `170bab6`, 2026-05-19)

Reference: `benchmarks/sv-comp/RESULTS.md`, latest run.
Totals: ~51 UNKNOWN · 3 UNSOUND · 7 MISSED · 105 files.

### UNSOUND (false-SAFE — wrong `Verified` on unsafe program)

- `c/loops/linear_sea.ch` — expected SAFE, got UNSAFE
- `c/loops/veris.c_NetBSD-libc_loop.i` — expected SAFE, got UNSAFE
- `c/loop-invariants/bin-suffix-5` — expected SAFE, got UNSAFE

### MISSED (UNKNOWN on programs we should solve)

- `c/loops/array-1` — DONE (`0.13.0`).  ACHAR's new `counter-assert-disj+imm`
  tier (Tier 2b) discovers `((j==0)||(array[0]>=menor)) ∧ (SIZE==1)` by
  conjoining immutable preheader facts with the counter-init disjunction.
- `c/loops/array-2` — direct analysis returns UNKNOWN; `--bmc-bound 1` finds
  the bug.  Plumb `--bmc-bound` into the benchmark runner.
- `c/loops/ludcmp`
- `c/loops/nec20`
- `c/loops/sum01_bug02.i`
- `c/loops/sum04-1.i`
- `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i`
- `c/loop-invariants/linear-inequality-inv-b`

### UNKNOWN breakdown by category

locks 13 · loops 33 (32 after array-1) · loop-crafted 5 · loop-invariants 0.

## Memory Model Precision (high-impact, low-cost wins)

These are the items the analysis currently over-approximates conservatively;
making them precise removes a class of UNKNOWNs across the suite.

### Targeted havoc — `CallMemoryEffect::WritesOnly`

Today `CallMemoryEffect` has two states: `PreservesMemory` (no havoc) and
`HavocMemory` (drop all store facts).  Real-world calls write only some
regions.  Adding `WritesOnly(Vec<Region>)` lets SP preserve facts for
non-written regions.  Concrete wins:

- `llvm.stacksave` / `llvm.stackrestore` — DONE (`0.13.0`) by marking pure in
  `is_known_pure_external`.  Was dropping preheader store facts for VLA
  programs (e.g., `array-1`'s `SIZE = 1` got havoc'd before the loop header).
- `memcpy(dst, src, n)` — writes only `dst` region.  Currently unrolled
  element-by-element in the adapter for constant `n`; the relational form
  could be expressed as `WritesOnly([dst])` for variable `n`.
- `memset(dst, c, n)` — same as memcpy.
- Heap allocators (`malloc`, `calloc`, `realloc`) — write only their returned
  region.  Currently havoc all memory.
- POSIX I/O (`read`, `write`, `fputc`, …) — write only the buffer argument's
  region.

Implementation sketch:

```rust
enum CallMemoryEffect {
    PreservesMemory,
    HavocMemory,
    WritesOnly(Vec<String>), // region names
}
```

In `apply_effects_sp`: on `WritesOnly(regs)`, retain facts whose region is
**not** in `regs` (drop only writes that match).  Symmetric change in
`wp_one`.

### Constant-offset stores through symbolic GEPs

`store i32 v, ptr %gep` where `%gep = getelementptr ... i64 K` (constant index)
currently goes through `PointerEnv` resolution and becomes
`MemoryStore { region, offset: K, value: v }`.  Variable-index GEPs (`i64 %j`)
become `MemoryStore { region, offset: %j, value: v }` and *drop all facts for
that region* in `apply_effects_sp` (see the `None` branch of `try_as_constant_int`).

When the loop-invariant analysis later proves `j ∈ [0, n)` and `n ≤ region_size`,
the variable-offset store *could* be summarised as preserving facts at offsets
known to differ from `j` modulo the inductive bound.  This is the
**non-interference principle** in array reasoning.  Plan:

1. After loop-invariant synthesis, re-run a forward fact pass that uses
   `j ∈ [...]` to keep `(region, K) → v` for any `K` outside `j`'s range.
2. For `array-2`-style programs where the safety property is about `array[0]`
   and the loop writes `array[j]` with `j ≥ 1` (induced from `j++` in the
   prefix), the fact `(stack6, 0) → original_value` would survive.

This is a strict improvement and would close a chunk of the array-bound
UNKNOWNs.

### Per-index array-fact reconstruction from SMT models

`IceState::from_model` currently loses per-index store information because
`ModelValue::ArrayDefault(d)` flattens Z3's `(store (const d) i v)` to just
`d`.  Fix in `src/common/smt/solver.rs`: walk the array model expression and
emit `ModelValue::ArrayStores { default, stores: Vec<(idx, value)> }`.  Then
`IceState::from_model` can populate `scalars["region[idx]"] = value` per index.

Impact: ACHAR's cheap pre-screening becomes precise on array-bearing
candidates; today we conservatively return `None` for select terms whose index
isn't in `scalars` (see `eval_term`).  Per-index reconstruction lets screening
correctly reject more candidates without SMT calls.

### Field-sensitive heap allocation

`malloc`/`new` already get unique `heap$<callee>@N` regions per call site
(per `MEMORY_MODEL.md` Step 4 prerequisite, alias_analysis is in place).
What's missing:

- The adapter doesn't yet emit `Seed { region: heap$..., size: N }` for
  alias analysis to track sub-region facts across the call boundary.
- Concrete writes to fields of a heap-allocated struct don't propagate to
  the caller's analysis without explicit field-region binding.

Both are mechanical wiring through the AA pipeline; see
[[project_array1_entry_safety]] and the Step 4 entry below for context.

### Struct-aware field regions for nested aggregates

`StructFieldGep` (Step 2 of Richer Structures, done) handles
`gep [0, N]` (one-level field access).  Nested cases like
`gep [0, N, 0, M]` (field N of field N of a struct) fall back to the
flat-offset path and lose field-region separation.  Generalisation:
recursively descend the GEP type chain and accumulate a region-suffix path
like `region$fN$fM`.

### Pointer-relational facts (alias-set narrowing)

`AliasResult` currently captures may-alias sets.  When two pointers are
provably must-equal (e.g., same alloca, same GEP path), the analysis still
treats their loads as independent.  Adding a must-equal closure lets WP
propagate equalities like `*p == *q` when `p` and `q` are must-aliased.
Practical win: cyclic-callee summaries where the formal parameter aliases a
caller's local don't lose precision through the call.

### Heap shape — simple linked-list axioms (longer-term)

The current heap model treats each `malloc` site as a fresh region with no
linkage between sites.  Linked-list traversals (`while (p != null) p = p->next`)
need a *reachability* predicate, not just per-site regions.  Selectively
axiomatising "list segments" — `lseg(p, q)` between two cell sequences —
unlocks the SV-COMP `heap-manipulation` category.  Major undertaking; out of
scope until simpler heap items above land.

## Instruction Coverage (sound but lossy — produce ERROR/UNKNOWN today)

- **Integer bitwise And/Or/Xor** — DONE (`0.4.1`).  `And` with non-negative
  constant mask emits `TypeBound(result >= 0 && result <= mask)`.  `Xor` with
  constant `-1` lowers to `result = -x - 1`.  `Or` leaves result unconstrained.
- **Shifts (`Shl`, `LShr`, `AShr`)** — DONE (`0.4.1`).  Constant-amount shifts
  lower to `Mul(x, 2^n)` / `Div(x, 2^n)`.  `LShr` adds `TypeBound(result >= 0)`.
- **`unreachable` instruction** — DONE (`0.4.3`).  Emits `Assume(False)`.
- **Floating point** — `float_compare.c` and similar still unsupported.
  Real-valued lowering exists but isn't wired in for IR-level fcmp/fp_arith.
- **Variable-amount shifts** — leave result unconstrained today.  Sound but
  produces UNKNOWN whenever a loop uses `x << y` with `y` non-constant.

## Long-term / Structural

- **Integer overflow / wrap-around** — the unbounded-Int model does not wrap.
  Programs that depend on two's-complement overflow (e.g. `INT_MAX + 1 < 0`)
  are not correctly modelled.  Long-term fix: switch scalars to SMT BitVector
  theory, or add modular axioms selectively.
- **BMC fallback for direct-mode UNKNOWN** — when invariant synthesis times
  out and returns UNKNOWN, automatically retry with a small BMC bound (1–3
  iterations).  `array-2` would become BugFound under this policy.  Cheap
  to implement: a 5-line addition in `driver.rs::analyze_module` after the
  invariant search returns UNKNOWN.

## Current Backlog

- **Memory-relational invariant templates** — `array-1` is now Verified
  (v0.13.0) via the `counter-assert-disj+imm` tier.  `array-2` is findable as
  UNSAFE via `--bmc-bound 1`.  The remaining gap for invariant-based coverage:
  a *cross-region relational* candidate generator producing
  `select(R1,i) ≤ select(R2,j)` templates from assertion postconditions.  The
  candidate `menor ≤ array[0]` would extend coverage to other memory-relational
  cases where BMC is impractical (large or symbolic loop bounds).
- **BMC --bmc-bound plumbing in benchmark runner** — to count `array-2` etc.
  as fixed in SV-COMP score.

## Loop Exit Summaries

Loop verification is split across `loops.rs` (invariant checking) and
`backward.rs` (exit-closure discharge).  `VerifiedLoopInvariant` enforces that
only fully-checked invariants reach `run_backward`.

### Current: one-step exit closure

`check_loop_invariant_verbose` propagates `Bad_v` backward from each exit edge
through the loop body (back edges excluded) to the header, then checks
`UNSAT(I_h ∧ exit_header_state)`.  `SummaryTables::loop_invariants` stores raw
`(CfgNodeId, Formula)` InductiveHints from the pre-pass; `verify_precomputed`
in `backward.rs` re-checks them against real assertion postconditions before
converting to `VerifiedLoopInvariant`.

### Planned: backward fixpoint with back edge included

For stronger discharge: run a backward fixpoint inside the loop body **with
the back edge included**, intersecting with `I_h` at the header at each
iteration until convergence.  The fixed point `B_{h,e}` satisfies
`UNSAT(I_h ∧ B_{h,e})` — strictly stronger than the current one-step check.

### Long-term: relational LoopExitSummary

A `LoopExitSummary { header, exit_edge, relation: Formula }` would encode the
full relational summary `R_{L,e}(x, x')`: starting at `x` at the header, the
loop exits through `e` reaching `x'`.  Safety rule:
`UNSAT(I_h(x) ∧ R_{L,e}(x, x') ∧ Bad_v(x'))`.  Separates loop reasoning from
assertion-site reasoning, enables summary reuse across multiple assertion
sites in the same loop, and is a prerequisite for compositional loop analysis.

## ACHAR Candidate Generation

### Tier order (as of `0.13.0`)

Assertion-derived tiers come FIRST.  Each tier is bounded by `|atoms|`-many
candidates (typically ≤ 10) before any combinatorial expansion.

1. **assert-atoms** — exact negations of the violation conjuncts.
2. **counter-assert-disj** — `counter_init || negation_atom`.
3. **counter-assert-disj+imm** — `(counter_init || negation_atom) ∧ ⋀ immutable_inits`.
   Strengthens (2) with preheader facts that the loop body cannot change.
   The `SIZE = 1` fact for `array-1` lives here.
4. **pred-assert-disj** — `pred_atom || negation_atom`.  Pairs the loop
   continuation guard `j < SIZE` (mined from icmp Predicate-Assigns) with the
   safety atom.
5–11. Predicate/combinatorial expansions (counter-pred-disj, counter-combo-disj,
combo-atoms, combo-conj, ice-disj, combo-disj).

### Deferred ACHAR improvements

- **CLI option for ACHAR timeout** — `--achar-timeout=SECONDS` to override the
  current 10s default; useful for benchmark sweeps where some loops legitimately
  need longer.  See `synthesize_with_cegis::timeout` parameter.
- **N-term conjunction synthesis** — instead of pairwise, grow conjunctions
  atom-by-atom guided by ICE witnesses: start with the atom that eliminates
  the most negative examples, add atoms until inductive or budget exhausted.
- **Implication atoms** — `A => B` shapes for per-element array properties
  (`counter ≤ k => select(arr, counter) ≥ 0`).  Natural for safety proofs over
  array loops where the property holds for processed elements only.  Would
  subsume the "j > 0 → array[0] ≥ menor" shape the current `+imm` tier
  approximates with a conjunctive strengthening.
- **Type-based domain bounds in the adapter** — emit `TransferEffect::Assume`
  range constraints from LLVM integer type widths (`i8 → [-128, 127]`, etc.)
  rather than relying on C-level `nondet_*()` macros.  Sound but historically
  slow (SMT timeouts on `array_max_5`); needs predicate simplification before
  the solver call, or selective application at widening points.

## Architecture Cleanups

- **Cyclic procedure handling** — observer-invariant synthesis covers
  pointer-parameter looping callees; tighter invariant checking and broader
  callee patterns (non-pointer return values) remain open.
- **Driver vs CLI fallback** — decide whether the driver should gain
  best-effort module analysis internally instead of relying on the CLI fallback.
- **`assertions::translation`** — decide whether to become a CLI input path or
  remain library-only.
- **Call-summary contract** — tighten and document what kinds of return
  relations are inferred and reused soundly.

## Richer Structures (C structs → C++ classes)

Phased plan for supporting structured types beyond flat integer arrays.

- **Step 1 — Fix struct/aggregate GEP layout** — DONE.  Walks GEP type chain
  using `LLVMGetGEPSourceElementType` + `TargetData`.  Offsets normalised to
  i32 units, `TargetData` built once per module.
- **Step 2 — Per-field memory regions** — DONE.  `TransferEffect::StructFieldGep`
  binds `{base_region}$f{N}` so loads/stores at different fields land in
  separate SMT arrays.
- **Step 3 — Stack-allocated C++ objects** — DONE.  `*this` is an `ext_region`;
  with per-field regions, field accesses through `*this` emit `StructFieldGep`
  and the return-summary machinery substitutes the ext region with the
  caller's allocation.
- **Step 4 — Heap model** — alias analysis pass implemented and wired into
  lowering.  Remaining: wire `heap$<callee>@N` region names into the adapter
  so `malloc` call sites produce `Seed` constraints and lowered CFG contains
  `MemoryStore` effects for heap writes.
- **Step 5 — Virtual dispatch** — DONE (`0.6.0`).  Indirect calls through
  vtable pointers resolved at the lowering boundary via module-wide vtable
  map + `ptr_at` side table.

## Heap support work items (Step 4 detail)

- **Heap region naming** — emit `heap$<callee>@N` regions in the adapter at
  every `malloc`/`calloc`/`realloc`/`new` call site.  Currently
  `heap_alloc_regions` is populated but its bindings don't propagate to
  `MemoryStore`/`Load` lowering.
- **Aliasing across heap sites** — over-approximate by havoc on unknown-pointer
  store, but use AA results to keep regions disjoint when AA proves it.
  `resolve_memory_effects` already calls `AliasResult` for pointer ops that
  the local `PointerEnv` cannot resolve — extend this to allocations.
- **Struct-of-heap-allocated-fields** — combining Step 2's `$fN` suffix with
  Step 4's `heap$` prefix gives `heap$malloc@0$f0`, `heap$malloc@0$f1`, …
  Naturally compositional.
