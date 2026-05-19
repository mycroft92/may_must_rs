# TODO

## Primary goal — equivalence with the SMASH paper

Implement *Compositional May-Must Program Analysis* (Godefroid, Nori,
Rajamani, Tetali, PLDI 2010) faithfully.  Our **only addon** is ACHAR
loop-invariant synthesis to keep the backward NOT-MAY direction
terminating over loops; everything else must be a paper construct or a
transparent realization of one.

See [`Rearch.md`](Rearch.md) for the architectural critique that drives
this work, and `design_notes/SMASH_FORWARD_MUST.md` for the directional
mapping between paper concepts and our types.

## The architectural mismatch (per Rearch.md)

The current driver is **bottom-up + per-assertion-local**.  The paper is
**top-down + demand-driven over interprocedural queries**.  These are
fundamentally different control flows, not a small rule bug.

Today:
- `analyze_module_with_llm` (`driver.rs:154`) walks every procedure
  bottom-up, computing a single `ReturnSummary` per function eagerly.
- Each assertion site spawns an isolated `run_backward` call with the
  current `SummaryTables`.
- Calls are inlined via the registry in `adapter.rs:87`; call effects in
  `abstract_cfg.rs:591` are essentially `Nop`.
- "Must summary" creation is a comment in `driver.rs:239` that doesn't
  fire (`driver.rs:404` never adds must/not-may summaries; it only caches
  loop invariants at `driver.rs:430`).
- `forward_may_usesummary` (formerly `must_post_usesummary`) implicitly
  treats summary precondition as `True` (`rules.rs:368`).

Paper:
- Unit of work is a **query** `⟨pre ⇒ proc post⟩`, not `AssertionSite`.
- Top-level assertion is a query with `post = ¬assertion`.
- Call sites generate **sub-queries** with caller-derived pre and post.
- Each procedure can have **many** contextual `MustSummary(pre, post)` and
  `NotMaySummary(pre, post)` summaries, looked up by context match.
- A worklist drives the analysis demand-first; callees are analyzed only
  when a query needs them.

## Refactor roadmap (staged, in order)

| Step | Task ID | QUERY_REFACTOR §10 step | Status |
|---|---|---|---|
| Types first (`Query`, `QueryResult`, `SummaryKey`, `InProgressQuery`) | #15 | 1 | ✅ done |
| Projection helper (`project_to_interface`) | #20 | 2 | ✅ done |
| Scheduler skeleton (per-procedure, queue + dispatch) | #15 | 3 | ✅ done |
| CREATE_NOTMAYSUMMARY / CREATE_MUSTSUMMARY at query completion | #17 | 4–5 | ✅ done |
| Subsumption-aware reuse (forward_may_usesummary checks pre via implies) | #18 | 6 | ✅ done |
| 6A — Scheduler reshape to per-module | #16 | (decomposed) | ✅ done |
| 6B — Module-level Scheduler ownership; bridge `sched.table` → legacy `SummaryTables` between procedures | #16 | 6 (cont'd) | in progress |
| 6C — Cut `compute_return_summary` from analysis path; contextual summaries alone | #16 | 7 + 8 | pending |
| Per-region `N_e` evidence (only if test-motivated) | #19 | (skipped unless needed) | pending |
| In-progress query subsumption for recursion | #21 | 9 | pending |

The "6A / 6B / 6C" labels are sub-decomposition of task #16 (call
mediation) introduced for commit-sized checkpoints.  They are now
canonically tracked here; commit messages and code comments reference
this table.

Loop machinery (ACHAR, observer, entry-safety) stays as the internal
procedure analyzer.  Only the interprocedural orchestration and summary
semantics change.

## What is already aligned (keep)

| Paper construct | Our code | Notes |
|---|---|---|
| Backward NOT-MAY (WP) | `RuleEngine::notmay_pre*` | ✅ Correct rule; needs query-context plumbing |
| Forward MAY (SP) | `RuleEngine::forward_may_post*` | ✅ Renamed in v0.15.0 |
| Forward MUST | Realized as backward NOT-MAY on acyclic CFG (native or BMC-unrolled).  `RuleEngine::forward_must_post` + `must_bugfound` + `NodeSummary.must_reach` exist as the paper-equivalent direct rule but are currently inert until SP becomes memory-aware. | See `design_notes/SMASH_FORWARD_MUST.md` |
| Loop invariant synthesis | ACHAR + observer + entry-safety | ✅ Our intentional addon |
| `NotMaySummary { pre, post }` | `summaries::NotMaySummary` | Shape correct; needs subsumption & contextual reuse |
| `MaySummary { pre, post }` | `summaries::MaySummary` | Shape correct; usage assumes `pre=True` today |
| `MustSummary { pre, post }` | `query::ContextualMustSummary` | New under-approximate sibling.  Replaces the v0.14 `smash::MustPathSummary` scaffolding. |
| Query worklist | `query::Query`, `scheduler::Scheduler` | ✅ Skeleton wired; drains every assertion verdict |
| Projection | `query::project_to_interface` | ✅ Substitution-only; preserves all memory regions verbatim |

## Deprecated scaffolding (delete in a future cleanup)

- `smash::MustPathSummary` — v0.14 scaffolding, replaced by
  `query::ContextualMustSummary`.
- `smash::SmashSummaryDB` — v0.14 scaffolding, replaced by
  `query::ContextualSummaryTable`.  `run_smash` will be simplified to
  take `&SummaryTables` directly.
- `smash::SmashRunResult` / `smash::VerdictEngine` — superseded by
  `scheduler::DispatchOutcome` carrying `AssertionResult` directly.
- Root-level `loop_redesign.md`, `Loop_search_and_use.md`, and the
  case-equivalent `LOOPS.md`/`loops.md` — deleted (superseded by
  `design_notes/LOOPS.md`).

## Soundness debt (paper-violating behaviours)

These can produce a **wrong `Verified`** or a **wrong `UNSAFE`**.  Fix
before any further coverage work.

- **`udiv`/`urem` treated as signed** — DONE.
- **Unsigned icmp collapsed to signed** — DONE (`0.4.2`).
- **Phase-B bypassing exit closure** — DONE (`0.11.0`).
- **Unsound `bugfound` from `reach ∧ state` on cyclic CFGs** — DONE
  (`0.16.0`).  Combining two MAY-family over-approximations and finding
  a satisfying model does NOT prove a real bug.  Now requires
  `cfg_is_acyclic`.  Was the root cause of false-UNSAFE on:
  - `c/loops/linear_sea.ch` (expected SAFE)
  - `c/loops/veris.c_NetBSD-libc_loop.i` (expected SAFE)
  - `c/loop-invariants/bin-suffix-5` (expected SAFE)

## Memory model precision

Independent of the query refactor.  These expand what the analysis can
model precisely, removing UNKNOWN verdicts without changing soundness.

### Targeted havoc — `CallMemoryEffect::WritesOnly`

`CallMemoryEffect` currently has `PreservesMemory` (no havoc) and
`HavocMemory` (drop all store facts).  Add `WritesOnly(Vec<Region>)` to
preserve facts for non-written regions.

Concrete wins:

- `llvm.stacksave` / `llvm.stackrestore` — DONE (`0.13.0`).
- `memcpy(dst, src, n)` — writes only `dst`.  Currently unrolled
  element-by-element for constant `n`; relational form for variable `n`
  becomes `WritesOnly([dst])`.
- `memset(dst, c, n)` — analogous.
- Heap allocators (`malloc`, `calloc`, `realloc`) — write only the
  returned region.
- POSIX I/O — write only the buffer argument's region.

Sketch:

```rust
enum CallMemoryEffect {
    PreservesMemory,
    HavocMemory,
    WritesOnly(Vec<String>),
}
```

In `apply_effects_sp` and `wp_one`: on `WritesOnly(regs)`, drop facts
whose region is in `regs`; preserve everything else.

### Memory-aware forward SP

`sp_one` for `MemoryStore`/`Load` is a no-op.  Making SP track memory
via store substitution (mirroring `wp_one`) would unlock a true
`forward_must_post` rule running alongside backward NOT-MAY in the same
fixpoint.  Today's forward MUST is realized via backward-on-acyclic
specifically because SP lacks this.

### Constant-offset stores through symbolic GEPs

Variable-index GEPs drop all facts for the target region.  After a loop
invariant proves `j ∈ [0, n)`, we could keep `(region, K) → v` for any
`K` outside `j`'s range (non-interference in array reasoning).

### Per-index array-fact reconstruction from SMT models

`IceState::from_model` loses per-index store info because Z3's
`(store (const d) i v)` is flattened to `ModelValue::ArrayDefault(d)`.
Walk the array model expression in `src/common/smt/solver.rs` and emit
`ModelValue::ArrayStores { default, stores: Vec<(idx, value)> }`.

### Field-sensitive heap allocation

`malloc` already gets `heap$<callee>@N` regions per call site (alias
analysis present).  Remaining wiring:

- Adapter doesn't emit `Seed { region: heap$..., size: N }` for AA.
- Concrete writes to fields of heap-allocated structs don't propagate
  without explicit field-region binding.

### Struct-aware field regions for nested aggregates

`StructFieldGep` handles `gep [0, N]` (one-level).  Nested
`gep [0, N, 0, M]` falls back to flat-offset.  Recursively descend the
GEP type chain accumulating `region$fN$fM`.

### Pointer must-equal closure

`AliasResult` has may-alias sets.  Add must-equal closure (provably same
alloca / same GEP path) so WP can propagate `*p == *q` when must-aliased.

### Heap shape — linked-list axioms (longer-term)

Per-site heap regions done.  Linked-list traversal needs reachability
predicates (`lseg(p, q)`).  Major undertaking; unlocks SV-COMP
heap-manipulation category.

## Instruction coverage

- **Floating point** — `float_compare.c` style still unsupported.
- **Variable-amount shifts** — leave result unconstrained.

## Long-term / structural

- **Integer overflow / wrap-around** — unbounded-Int model doesn't wrap.
  Long-term fix: switch scalars to SMT BitVector theory.
