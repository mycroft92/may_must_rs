# Loop Invariant Analysis

This document describes the full loop invariant pipeline: detection, candidate
generation, the three-part soundness check, and the interprocedural precomputed
summary flow.  It also records known design decisions and their rationale,
including the `config=None` observer-pattern path.

---

## 1. Loop Detection

`detect_loops` in `loops.rs` finds every **natural loop** in the CFG:

1. Call `cfg.detect_back_edges()` — returns every edge `(latch → header)` whose
   target dominates its source in a DFS traversal.
2. For each back edge, compute the **loop body** by backward BFS from latch to
   header (all nodes from which header is reachable without leaving the loop).
3. Collect **exit edges** — outgoing edges from body nodes whose targets are
   outside the body.
4. Record the **back-edge guard** (the loop-continuation condition on the latch
   → header edge).

The result is a `LoopInfo` struct per back edge.  Nested loops appear as
separate entries; `sort_innermost_first` orders them by body size so inner
loops are processed before outer ones (inner invariants are available when
checking inductiveness of outer loops).

---

## 2. Invariant Candidate Generation

Three algorithmic strategies plus an optional LLM path.

### 2.1 Algorithmic candidates (`algorithmic_candidates`)

Pattern-matched from the CFG structure; no solver queries.  Sources:

- **Back-edge guard and its negation** — the loop-continuation and
  loop-termination conditions are direct candidates.
- **Header-to-body entry guards** — guards on edges from the header into the
  loop body.
- **Exit-edge guard negations** — the negation of each exit guard (loop just
  terminated).
- **Counter bounds** — when a guard is `i < n` or `i <= n`, emit `i >= 0`,
  `i <= n`, and `i >= 0 && i <= n`.
- **Predicate assignments in the body** — if the body assigns `p = (some
  comparison)`, emit the comparison and its negation as candidates.
- **Self-increment lower bounds** — assignments of the form `i = i + c` suggest
  `i >= 0`.
- **Literal lower bounds** — assignments `i = k` (constant) suggest `i >= k`.

All candidates are simplified by substituting constant loop definitions
(`normalize_formula_with_defs`).

### 2.2 CHC solving (`chc_loop_invariant`)

Handles the single pattern `i < n` (or `i < bound`) on the back-edge guard.
Delegates to `chc::solve_loop_chc` to produce `0 <= i && i <= n` as a
closed-form invariant.  Returns `None` for all other guard shapes.

### 2.3 Houdini template weakening (`houdini_candidates`)

Generates a large template set of linear arithmetic candidates:

- For every integer variable visible in the loop, for every integer constant
  found in the assertion postcondition or loop body: emit `var >= c` and
  `var <= c`.
- All pairs `(lo, hi)` produce range conjunctions `var >= lo && var <= hi`.
- All pairs of distinct variables produce `v1 <= v2`, `v1 >= v2`, `v1+1 <= v2`.
- Constants `{-1, 0, 1}` are always included.

The caller feeds these through `check_loop_invariant_verbose` and accepts
whichever subset passes; the Houdini algorithm keeps weakening until an
inductive conjunction remains.

### 2.4 LLM-guided CEGIS

When `llm` is configured and a strategy above fails, the LLM backend receives a
context (loop body, guard, exit postcondition, previous failed attempts) and
proposes a candidate.  Parsed candidates go through the same
`check_loop_invariant_verbose` gate.  Up to `max_tries` proposals per loop.

---

## 3. The Three-Part Soundness Check

`check_loop_invariant_verbose` in `loops.rs` checks a candidate invariant `I`
for three conditions in order.

### 3.1 Initiation

> Does `I` hold the first time the loop header is entered?

Method: propagate the **violation** of `I` (i.e., `NOT I`) backward from the
header to the function entry, with all back edges excluded.  Query the oracle
for feasibility of the violation at entry.

- **Infeasible** → initiation passes (`NOT I` cannot be reached from entry).
- **Feasible or Unknown** → `InitiationFailed`.

### 3.2 Inductiveness

> If `I` holds at the start of an iteration, does it still hold at the start of
> the next?

Method: compute `WP_inductive(body, NOT I)` — the weakest precondition of
violating `I` after one body pass, using Hoare-style implication for `Assume`
effects (see `notes/inductiveness-assume-wp-semantics.md`).  This gives
`inductive_header` — the condition at the header under which `I` can be
violated after one step.  Query:

```
oracle.implies(I, inductive_header)
```

- **Valid** → inductiveness passes (the invariant is preserved).
- **Invalid or Unknown** → `InductivenessFailed`.

**Why Hoare-style for Assume in inductiveness only:**
If a loop body contains `Assume(c)` where `c` involves a fresh call-return
variable (e.g., `nondet_uint()` returns fresh `v` with `Assume(v >= 0)`), the
standard `c AND post` WP would demand `I → (v >= 0)` — unprovable for any `I`
over program state.  Using `c → post` (Hoare-style) asks instead whether `I`
is preserved *on paths where `c` holds*, which is the correct condition.

### 3.3 Exit closure

> Does `I` block the violation path at every loop exit?

For each exit edge whose target has a non-trivial entry in
`assertion_postconditions` (the violation precondition propagated backward from
the assertion site with back edges blocked):

1. Compute `exit_header` — the WP of the exit violation propagated back to the
   loop header (restricted to the loop body).
2. Check feasibility of `I AND exit_header`.
   - **Infeasible** → the invariant blocks the violation at this exit (exit
     closure passes for this edge).
   - **Feasible or Unknown** → `ExitClosureFailed { exit_edge }`.

Exit closure ties the invariant to the **specific assertion** being proved.  An
invariant can be inductive without being strong enough to discharge the
obligation at the exits; exit closure catches this.

**When exit closure is skipped:**
Pass `&BTreeMap::new()` as `assertion_postconditions`.  This is intentional in
two places:
- `discover_loop_invariants` — pre-computes invariants with no assertion site.
- `observer_summary_invariants` — the observer-pattern invariants are designed
  to be inductive; the authoritative discharge is done by the subsequent
  `analyze_with_tables` call.

---

## 4. Precomputed Loop Summary Flow

### 4.1 Pipeline overview

```
analyze_module_with_llm()                           [driver.rs]
  │
  ├─ for each looping function:
  │    discover_loop_invariants(cfg, fn, oracle)     [backward.rs]
  │      └─ calls synthesize_loop_invariants with assertion_postconditions=∅
  │         (scope = True — no assertion site yet)
  │         tries Algorithmic → CHC → Houdini → Template
  │         exit closure SKIPPED (empty postconditions ⟹ no exit to check)
  │    → stored in SummaryTables::loop_invariants
  │
  └─ for each function, for each assertion site:
       analyze_with_summaries(…, tables, config)     [driver.rs]
         └─ precomputed = tables.get_loop_invariants(fn)
            analyze_with_tables(cfg, fn, site, oracle, tables, config, precomputed)
              └─ computes assertion_postconditions once from site
                 calls synthesize_loop_invariants with real assertion_postconditions
                 (exit closure active — tied to specific assertion)
```

`discover_loop_invariants` and `analyze_with_tables` both call the same
`synthesize_loop_invariants` function; the only difference is the
`assertion_postconditions` argument:

- **Pre-pass** (`discover_loop_invariants`): passes `&BTreeMap::new()`.
  `check_loop_invariant_verbose` sees empty postconditions and skips exit
  closure.  LLM is disabled (`config = None`).
- **Per-assertion** (`analyze_with_tables`): passes computed WP states.
  Exit closure is active and ties the invariant to the specific assertion.

### 4.2 Inside `analyze_with_tables`

```
if acyclic:
    run_backward(…, &[], …)   ← no invariant needed

else (cyclic):
    excluded = detect_back_edges()
    assertion_postconditions = compute_preliminary_backward_states(cfg, site, excluded)

    if precomputed is Some(invs) and !invs.is_empty() and !force_llm:

        exit_closure_ok =
            if config.is_none():
                true                 ← observer pattern: run_backward is authoritative
            else:
                precomputed_satisfy_exit_closure(assertion_postconditions, invs, oracle)

        if exit_closure_ok:
            return run_backward(cfg, site, oracle, excluded, invs, tables)
            ↑ fast path: precomputed invariant passed all three checks

        // exit closure failed: fall through to synthesis
        // (do NOT try run_backward here — see below)

    // synthesis path
    invariants = synthesize_loop_invariants(assertion_postconditions, …)
    return run_backward(cfg, site, oracle, excluded, invariants, tables)
```

**Why `run_backward` is NOT attempted when exit closure fails:**

When exit closure fails for the precomputed invariant, running `run_backward`
with that invariant is unsound.  The mechanism that makes it unsafe:

1. `run_backward` injects the invariant into `reach` at the loop header and
   then runs the bidirectional fixpoint with back edges excluded.
2. The backward `state` component propagates from the assertion backward through
   the exit edge, adding the exit condition (e.g. `j ≥ SIZE`) to the state at
   the loop header.
3. This state then propagates backward through the loop-initialization code
   (e.g. `j = 0`).  The exit condition `j ≥ 1` combined with `j = 0` gives
   `0 ≥ 1 = False`, so `state` at the function entry collapses to `False`.
4. `reach AND state = True AND False = False → Verified` — a false safe.

The invariant in `reach` at the header never interacts with the already-False
`state` at the entry check point.  The spurious Verified is caused entirely by
the loop-init vs. exit-condition contradiction on the direct
entry→header→exit→assertion path; the loop body (which is what actually drives
`j` from 0 to `SIZE`) is invisible in this one-pass backward analysis.

The correct response when exit closure fails is to attempt synthesis, which
searches for a stronger invariant that can discharge the specific assertion.
If synthesis also fails, the result is `UNKNOWN` (sound; cannot be `Verified`).

### 4.3 `precomputed_satisfy_exit_closure`

Re-runs `check_loop_invariant_verbose` (all three checks, including exit
closure) for each precomputed invariant against the assertion-specific
`assertion_postconditions`.  Returns `false` for the first invariant that fails
any check.

Exit closure is checked unconditionally for every loop that has a precomputed
invariant.  An earlier optimisation that skipped the check when a syntactic
scan of the loop body found no writes to names mentioned in the obligation
formula was removed in v0.7.2 because it produced false-Verified results:
when the obligation is on a loaded scalar whose source region is not mentioned
in the obligation formula directly, the scan incorrectly declared the loop
irrelevant.  See `debug/array-2-false-safe.md` for the full analysis.

When exit closure fails, the caller falls through directly to synthesis (see
§4.2).  Using `run_backward` with a precomputed invariant that failed exit
closure is unsound and was removed in v0.7.4 — see §4.2 for the full
explanation.

### 4.4 The `config=None` observer path

`config=None` is used exclusively by `infer_cyclic_observer_summary` in
`driver.rs`.  The call is:

```rust
analyze_with_tables(cfg, fn, &site, oracle, &SummaryTables::new(),
    None,           // config=None
    Some(&invariants))
```

The invariants came from `observer_summary_invariants`, which checks only
initiation + inductiveness (exit closure skipped with `&BTreeMap::new()`).
When `config.is_none()`, `precomputed_satisfy_exit_closure` is skipped entirely
and the precomputed invariants are used directly.

**Why this is sound:**

1. The observer invariants are proven inductive — every reachable header state
   satisfies them.  Injecting them into `reach` is a valid overapproximation.
2. `run_backward` is the authoritative check.  If the invariant is too weak to
   discharge the obligation, `run_backward` returns `Unknown` or `BugFound`,
   not a false `Verified`.
3. Running `precomputed_satisfy_exit_closure` would likely fail for observer
   invariants (they are disjunctive — `counter <= k OR accumulator >= value` —
   not shaped to pass an exit-closure query).  A failure would fall through to
   `synthesize_loop_invariants`, which uses the same backward-state approach and
   would not find a better candidate.

**Why `precomputed_satisfy_exit_closure` is needed in the `config=Some` path:**

In the regular driver path, `discover_loop_invariants` runs with no assertion
site and skips exit closure.  The precomputed invariant may be a perfectly good
inductive invariant (`i >= 0 && i <= n`) that cannot discharge a particular
assertion (e.g., the assertion is about array contents, not the counter).  Exit
closure re-checks with the specific assertion before accepting the invariant;
failure triggers fall-through to full synthesis with CHC/Houdini/LLM which can
find a stronger, assertion-specific invariant.

### 4.5 Invariant injection in `run_backward`

```rust
for (header, invariant) in conjunct_loop_invariants(loop_invariants) {
    summary.reach = Formula::and(summary.reach, invariant);
}
```

The invariant is **conjuncted** into `reach` at the loop header.  Multiple
invariants for the same header are combined by conjunction.  After injection,
`run_to_fixpoint` runs the bidirectional forward/backward pass with back edges
blocked, and the final decision is `reach AND state` at entry.

---

## 5. Nested Loops

Inner loop invariants are passed as the `inner: InnerInvariants` parameter to
`check_loop_invariant_verbose` and to `backward_states`.  During the backward
propagation that computes initiation or inductiveness, inner loop bodies are
**summarised** at their headers rather than re-entered:

- `summarize_inner_loops` collects inner headers and their invariants.
- Inner body nodes (excluding the header itself) are added to
  `summarized_inner_nodes` and skipped during edge propagation.
- The inner invariant is seeded into the state at the inner header, as if the
  inner loop were replaced by its invariant.

This ensures that outer invariant checking does not re-expand inner loops and
that inner invariants are available when reasoning about the outer body.

---

## 6. Files

| File | Role |
|---|---|
| `src/may_must_analysis/loops.rs` | `detect_loops`, `algorithmic_candidates`, `chc_loop_invariant`, `houdini_candidates`, `check_loop_invariant_verbose`, `backward_states` |
| `src/may_must_analysis/backward.rs` | `discover_loop_invariants`, `synthesize_loop_invariants`, `analyze_with_tables`, `run_backward`, `precomputed_satisfy_exit_closure` |
| `src/may_must_analysis/driver.rs` | `analyze_module_with_llm`, `analyze_with_summaries`, `observer_summary_invariants`, `infer_cyclic_observer_summary` |
| `src/may_must_analysis/chc.rs` | CHC solver for counter-loop patterns |
| `src/may_must_analysis/rules.rs` | `RuleEngine::run_to_fixpoint`, forward/backward propagation rules |
