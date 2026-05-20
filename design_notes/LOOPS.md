# Loops in the Query-Driven Model

This document specifies how loop handling fits into the query-driven
SMASH architecture described in
[`QUERY_REFACTOR.md`](QUERY_REFACTOR.md).  Loop invariant synthesis
(ACHAR + observer + entry-safety) is our **one intentional addon** to
the paper — it makes the backward NOT-MAY direction terminate over
loops.  This document defines exactly where it plugs in, what state it
shares with the rest of the analysis, and how it interacts with
contextual summaries and BMC.

Companion documents:

- [`QUERY_REFACTOR.md`](QUERY_REFACTOR.md) — the query model itself.
- [`SMASH_FORWARD_MUST.md`](SMASH_FORWARD_MUST.md) — forward MUST = backward NOT-MAY on acyclic (native or BMC-unrolled) CFG.
- Source: `src/may_must_analysis/loops.rs` — `check_loop_invariant_verbose`
  three-stage check (initiation + inductiveness + exit closure).

---

## 1. Why loops are special

A SMASH-paper query `⟨pre ⇒ P post⟩` is, in principle, a Hoare triple
checked over the procedure body.  For straight-line code both the
forward MUST direction (concrete witness) and the backward NOT-MAY
direction (WP propagation) terminate naturally: the CFG is acyclic, so
each direction is a single traversal.

A back edge breaks both directions:

- **Forward MUST** would re-enter the loop body indefinitely, growing
  `must_reach` at the header without convergence.  Bounded-model
  checking solves this by unrolling each loop to a fixed depth `k`,
  producing an acyclic CFG.  See [`SMASH_FORWARD_MUST.md`](SMASH_FORWARD_MUST.md).
- **Backward NOT-MAY** needs an **inductive over-approximation** of the
  reachable header states (a loop invariant `I`) to close the fixpoint:
  `WP(body, I) ⇒ I` lets backward propagation terminate when it reaches
  the header.  Without `I` it would iterate `WP^n(body, post)` forever.

ACHAR synthesises this `I`.  It is the only place where the paper's
strictly-local-per-procedure analysis grows into a more sophisticated
search — and that is by design.

---

## 2. Where invariants live in the query model

The current code stores invariants in
`SummaryTables::loop_invariants` keyed by procedure name only.  In the
query model this is **insufficient** because ACHAR's candidate
generation reads the assertion's violation formula
(`negation_atoms`, `violation_negation_atoms(...)` in `achar.rs`) to
build assertion-derived disjunctions — different queries on the same
procedure may need different invariants.

The query-aware schema:

```rust
pub struct ContextualSummaryTable {
    // ... (notmay, must as in QUERY_REFACTOR.md)
    /// Loop invariants keyed by (procedure, query-post-fingerprint).
    /// `query_post_fingerprint` is a canonical hash of Q.post (or a
    /// stronger key if the same post fingerprints different invariants).
    pub loop_invariants:
        BTreeMap<(ProcedureName, QueryPostFingerprint), Vec<(CfgNodeId, Formula)>>,
}
```

Invariant synthesis runs **once per (procedure, query-post)**, and the
result is cached.  Queries with the same procedure but different posts
re-synthesise.  Two cheap optimisations:

1. **Post-independent invariants** (counter monotonicity `j ≥ 0`,
   simple bounds) are valid for *every* assertion in the procedure.
   The pre-pass `discover_loop_invariants` already produces these
   without an assertion context.  Cache them under
   `QueryPostFingerprint::None`.
2. **Cross-query reuse** by subsumption: if an invariant proved for
   `post = P` is strong enough to discharge a new query with
   `post = P'` (i.e. the same `I` survives exit closure against `P'`),
   reuse it without re-running ACHAR.  Cheap: a single
   `check_loop_invariant_verbose` call per cached invariant.

---

## 3. Soundness — three checks must hold against the *query's* post

`VerifiedLoopInvariant` exists today to enforce that an invariant has
passed all three checks (initiation, inductiveness, exit closure)
against the **real assertion postconditions**.  The query refactor
preserves this guarantee — only the source of "real assertion
postconditions" changes:

```
exit closure check:
    for each exit edge e from the loop body:
        let post_e = WP(body \ back-edges, Q.post, from e back to header)
        check  UNSAT(I_h ∧ post_e)
```

`Q.post` here is the **query's** post, projected onto the loop's
visible variables (after callee renames, after caller-side context
substitution).  Today the code reads `assertion_postconditions` — a
`BTreeMap<CfgNodeId, Formula>` keyed by the exit edge's target node
— which is constructed in `backward.rs` from the assertion site's
obligation.  The query refactor builds the same map from `Q.post`
directly.

The `VerifiedLoopInvariant` type stays as-is and is the only handle
the rules engine accepts when seeding `reach` at loop headers; this
type-level guarantee is what blocked the historical Phase-B
unsoundness (see `feedback_phase_b_soundness` in memory) and must
remain unweakened.

---

## 4. Backward NOT-MAY around a loop

Inside a procedure's CFG, when the backward NOT-MAY pass reaches a
loop header:

```
backward NOT-MAY at loop header `h`:
    if tables.loop_invariants[(procedure, fingerprint(Q.post))] is empty:
        run synthesize_loop_invariants(h, Q.post)   // ACHAR + others
        cache the produced VerifiedLoopInvariant(s)

    for each VerifiedLoopInvariant I_h at h:
        # I_h has already passed initiation + inductiveness + exit
        # closure against Q.post.  Seed `reach[h]` with I_h so that
        # WP through the body terminates when it crosses the back
        # edge.
        engine.summary_mut(h)?.reach = Formula::or(engine.summary(h)?.reach.clone(), I_h);

    # If no invariant was found, the query result is Unknown.
```

The invariant strengthens `reach[h]` *only* — it does not seed `state`,
because the invariant is an over-approximation of *reachable* states,
not of violation pre-states.  This is identical to today's behaviour.

---

## 5. Forward MUST around a loop

Today's forward MUST direction is realized as **backward NOT-MAY on an
acyclic CFG** (see `SMASH_FORWARD_MUST.md`).  For programs with loops,
the orchestrator must first acyclify:

```
forward MUST at procedure P:
    if cfg(P).has_back_edges():
        for k in 1..=bmc_bound:
            unrolled_cfg = bmc::unroll_single_loop(cfg(P), k)
            result = backward_notmay_on_acyclic(unrolled_cfg, Q.pre, Q.post)
            if result == Reachable: return Reachable(witness)
        return Unknown
    else:
        return backward_notmay_on_acyclic(cfg(P), Q.pre, Q.post)
```

The `bmc_bound` comes from `InvariantConfig`.  Each unroll produces an
acyclic graph over which the existing backward direction is *precise*
modulo SMT — and crucially, WP through `MemoryStore` *does* substitute
the stored value into selects on the same region, so the result is
memory-aware.  This is why we don't need a separate
`forward_must_post` rule (yet); see the soundness argument in
`SMASH_FORWARD_MUST.md`.

### Why BMC and ACHAR coexist

They serve **different directions** in the paper sense.  ACHAR makes
backward NOT-MAY terminate so that *safety proofs* are tractable.  BMC
makes forward MUST terminate so that *bug witnesses* are concrete.
Neither replaces the other; they cooperate.

The current `bmc::bmc_check` already builds an acyclic unrolled CFG
and runs `bmc_sat_check` (a one-pass backward WP) on it.  Under the
new architecture, this is the forward MUST realization for cyclic
procedures.  The renaming in `engine_verdict` logs from
`engine=must/bmc` to `engine=forward-must/bmc-unrolled` is cosmetic;
the algorithm is unchanged.

---

## 6. Loop invariants and contextual summaries

A loop is **internal** to a procedure.  Its invariant does not cross
the procedure interface; it lives entirely in the procedure's local
state.  Therefore loop invariants do **not** appear in `MustSummary` or
`NotMaySummary` — those are projected to procedure-interface variables
(formals, return, externally-visible memory).

What *does* cross the interface, from the loop's perspective:

- The **values produced** at procedure exit, which a callee summary
  must capture.  E.g., a procedure with a loop that fills an array and
  returns its sum produces a summary `MustSummary { pre, post: sum == ... }`
  in terms of the formal parameters and the returned `__retval`.  The
  loop invariant `I_h` was used internally to discharge the exit closure
  against `Q.post`, but `I_h` itself is not part of the summary.
- The **external regions** the loop modifies.  If a loop writes to an
  externally-visible region (e.g., a pointer argument), the summary
  must capture the post-state of that region.  ACHAR currently mines
  memory-relational invariants (e.g., `select(R1, i) ≤ select(R2, j)`)
  that are visible at the interface; these flow into the summary's
  postcondition via the existing `compute_return_summary` / observer
  paths.

In short: loop invariants are an implementation detail of the
intra-procedural analysis; they affect *which* contextual summaries can
be derived, but they don't appear in the summary table itself.

---

## 7. Caching, invalidation, and the worklist

When the scheduler dispatches a query `Q` on procedure `P`:

```
1. Lookup loop invariants for (P, fingerprint(Q.post)).
   - HIT: use cached VerifiedLoopInvariant(s) directly.
   - MISS: synthesize.  This may itself trigger sub-queries if the
     loop body contains calls (ACHAR's CEGIS loop uses the oracle which
     evaluates formulas with call effects already abstracted by the
     contextual summary tables).
2. Seed reach[loop_headers] with the invariants.
3. Run intra-procedural backward NOT-MAY to fixpoint.
4. For BugFound: run BMC at increasing bounds (forward MUST direction).
5. CREATE_*_SUMMARY from the result.
```

### Invalidation

Cached invariants are valid as long as the procedure's body hasn't
changed.  In a single-run module analysis the body doesn't change, so
invariants live for the duration of `Scheduler::analyze_module`.

If summaries for callees inside the loop body change (a recursive
sub-query completes and tightens its summary), the *correctness* of
the cached invariant is unaffected — ACHAR's checks
(`check_loop_invariant_verbose`) use only the local body + assertion
post.  The *strength* needed may have changed (a tighter callee summary
might let a weaker invariant suffice), but reuse remains sound.  The
worklist will discover this when re-running the affected outer query.

---

## 8. Recursion at the loop level

A loop body that calls itself recursively (e.g., a recursive helper
inside the loop) is handled by the *call* mechanism, not by ACHAR.  The
loop invariant search treats each call as an opaque step constrained
by the matching contextual summary (or by an in-progress optimistic
placeholder).  If the placeholder is too weak to discharge the exit
closure, ACHAR's candidate fails and the query result is Unknown — the
recursive cycle then forces the scheduler's iterative refinement step,
which may strengthen the placeholder on a subsequent iteration.

---

## 9. Mapping to existing code

| Concern | Existing site | Change under query refactor |
|---|---|---|
| ACHAR entry point | `synthesize_loop_invariants` in `backward.rs` | Called by scheduler per (procedure, query-post-fingerprint).  Result cached in `ContextualSummaryTable::loop_invariants`. |
| `check_loop_invariant_verbose` | `loops.rs:359` | Unchanged; called from synthesis. |
| `VerifiedLoopInvariant` | `loops.rs:152` | Unchanged; the only invariant type accepted by `run_backward`. |
| `discover_loop_invariants` (pre-pass) | `backward.rs:550` | Runs once per procedure regardless of query; produces post-independent invariants stored under fingerprint `None`. |
| `bmc::bmc_check` | `bmc.rs:55` | Becomes the forward-MUST realization for cyclic procedures; unchanged internally. |
| Loop invariants in `SummaryTables` | `summaries::SummaryTables::loop_invariants` | Migrate to `ContextualSummaryTable::loop_invariants` (keyed by `(procedure, fingerprint)`). |
| Memory-relational invariants exposed at interface | `compute_return_summary`, observer summaries | Continue producing summaries; the new `ContextualSummaryTable` accepts them with contextual `pre` (currently `True`). |

---

## 10. Implementation order (alongside `QUERY_REFACTOR.md`)

The loop concerns interleave with the query refactor steps:

- After **step 1** (types): add `QueryPostFingerprint`, extend the
  loop-invariant cache key.
- After **step 3** (scheduler skeleton): plumb the loop-invariant
  cache through the scheduler's intra-procedural call.
- After **step 6** (call handling): verify ACHAR's CEGIS loop still
  works when call effects are mediated by contextual summaries instead
  of eagerly inlined ones (ACHAR uses the oracle, which sees the
  formula post-substitution; should be transparent).
- After **step 8** (recursion): test mutual recursion involving a
  loop, e.g. `array_max_5` (already in the test suite).

---

## 11. Correctness checks (loop-specific)

Unit tests to add as the refactor progresses:

- `QueryPostFingerprint` is structurally canonical: equivalent posts
  map to the same fingerprint; non-equivalent posts map to different
  ones modulo collisions (low risk for first cut).
- Cached invariants under one query-post still pass
  `check_loop_invariant_verbose` against a different but
  *implied-stronger* query-post (subsumption test).
- Cyclic procedure with a known-unsafe execution (`array-2`-like) is
  reported BugFound via `forward MUST = BMC-unrolled + backward-on-acyclic`,
  even when no `MustSummary` already exists in the table.
- The historical false-UNSAFE cases (`linear_sea.ch`,
  `veris_NetBSD-libc_loop.i`, `bin-suffix-5`) continue to report
  Unknown (or SAFE if invariant synthesis succeeds) — never UNSAFE.
