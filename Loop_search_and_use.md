# Loop Invariant Search and Use

This document describes exactly how loop invariants are detected, generated,
checked, and applied in the bidirectional may/must analysis.  All references
are to source files under `src/`.

---

## 1. Loop Detection (`may_must_analysis/loops.rs` — `detect_loops`)

Before any invariant work, `detect_loops` calls `cfg.detect_back_edges()`.  A
**back edge** is any CFG edge whose target dominates its source in DFS
traversal — exactly the edges that form cycles.

For each back edge `(latch → header)`:

| Field | Meaning |
|---|---|
| `header` | Back edge target — unique entry point of the loop; invariants are asserted here |
| `latch` | Back edge source — the node that jumps back to the header |
| `body` | All nodes reachable from the latch back to the header (backward BFS); includes header and latch |
| `exit_edges` | Every edge leaving the body (source ∈ body, target ∉ body) |
| `back_edge_guard` | The formula on the back edge — the loop continuation condition |

**Nested loops**: `sort_innermost_first` sorts all detected loops by body size
so inner loops are processed before outer ones.  Already-accepted inner
invariants are passed as `InnerInvariants<'_>` to every subsequent call so
that inner loop bodies can be summarised without re-entering them.

---

## 2. Assertion-Specific Backward Pre-pass (`backward.rs` — `compute_preliminary_backward_states`)

Before any candidate is tried, `analyze_with_tables` runs one backward
propagation with all back edges excluded.  It seeds the assertion node with
`WP(¬obligation)` and propagates backward through the acyclic CFG skeleton.
The result is a map:

```
assertion_postconditions: BTreeMap<CfgNodeId, Formula>
```

The value at each node is "the conditions under which a violation can arrive
at this node after the loop exits."  The value at a loop's exit-edge target is
precisely what a valid invariant must block.

This map is computed **once per assertion** and reused by every candidate
check for every loop in the function, avoiding redundant backward passes.

---

## 3. Synthesis Pipeline (`backward.rs` — `synthesize_loop_invariants`)

For each loop (innermost-first) the following phases are tried in sequence
until one produces an accepted candidate.  All candidates are checked by
`check_loop_invariant_verbose` (see §4).

### Phase 1 — Algorithmic (`loops.rs` — `algorithmic_candidates`)

No solver calls at this stage; O(CFG size).  Mines candidates from:

- The **back-edge guard** and its negation (e.g. `i < n` → also `¬(i < n)`).
- **Header→body entry edge guards**.
- **Exit edge guard negations** (loop termination conditions).
- **Counter increment patterns** — `i = i + c` → generates `i >= 0`.
- **Integer literal assignments** — `i = 0` → generates `i >= 0`.
- **Predicate assignments** — if `b` is assigned predicate `p`, generates `p`,
  `¬p`, all five comparison variants (`<`, `<=`, `>`, `>=`, `==`) of the same
  operands, and `b ⇒ p`.

Constants and variables with unique non-recursive definitions in the body are
substituted via `normalize_formula_with_defs`.  Tautologies (`True`, `False`,
`a ⇒ a`) and duplicates are dropped by `push_nontrivial`.

These candidates are checked with the **full three-way check** — exit closure
is included.

### Phase 2 — Entry-safety (`loops.rs` — `entry_safety_candidates`)

Only attempted when Phase 1 fails **and** `assertion_postconditions` is
non-empty (i.e. a specific assertion site is being checked).

Generates candidates of the form `counter == init_value || safety_condition`:

1. `preheader_store_facts_at_header` runs the same forward SP pass as the
   initiation check (§4.1) but stops before the header's own effects and
   extracts concrete store facts — e.g. `(stack0, 0) → 0` meaning
   `select(stack0, 0) == 0`, i.e. the counter variable starts at 0.
2. `direct_violations` reads the violation formula at exit-edge targets
   directly from `assertion_postconditions` (no backward propagation through
   the body).  `safety = ¬violation`.
3. Produces:
   - `(all scalar init facts) || safety`
   - Per-counter: `select(region, 0) == init || safety`
4. Also generates the backward-propagated variant (`exit_violation_at_header`)
   as a fallback.

**Exit closure is intentionally skipped for this phase**: `first_accepted_candidate`
is called with `&BTreeMap::new()` as the postconditions map.  Only initiation
and inductiveness are checked here.  The authoritative discharge of the
assertion obligation is performed by the subsequent `run_backward`
bidirectional check — the same observer-invariant pattern used in `driver.rs`
for cyclic callee summaries.  See `LOOPS.md` §Phase-B for the soundness
argument.

### Phase 3 — ACHAR ICE learner (`achar.rs` — `grammar_candidates`)

Enumerates candidates from a grammar over the loop's variable vocabulary, guided
by concrete SMT example states:

**Vocabulary collection** (`collect_vocab`): gathers integer-sorted variables from
loop body effects (`Assign`, `MemoryStore`), `Select` terms from loop body effects
and assertion postconditions, and integer constants from the body plus `{0, 1}`.
LLVM-internal variables (`__vla_expr*`) are filtered out.

**Atom generation** (`generate_atoms`): all pairwise comparisons (`<=`, `<`, `==`)
between terms, plus comparisons of each term against each constant.

**ICE example collection**: the oracle is queried for concrete models of the
forward reach (positive example) and each exit violation (negative examples).

**Filtering**: atoms false on the positive example are dropped.  Safety atoms —
those false on at least one negative example — are identified.

**Candidate priorities**:
1. Positive-consistent atoms (capped at `MAX_CONJUNCTIONS`).
2. Pairwise conjunctions of positive-consistent atoms.
3. Observer-style `counter <= idx || safety` and general `pos || safety`
   ICE-guided disjunctions (capped at `MAX_ICE_DISJ`).
4. Pairwise disjunctions of positive-consistent atoms (capped at `MAX_PAIRWISE_DISJ`).

Full three-way check including exit closure.

---

## 4. What `check_loop_invariant_verbose` Checks

Entry point: `loops.rs` — `check_loop_invariant_verbose(info, cfg, candidate, oracle, assertion_postconditions, inner)`.

**Normalization first**: `normalize_candidate` applies
`header_node.transfer.wp(I)` to translate `I` into the header's *input*
variable space (before the header's own effects run).  This is necessary
because the invariant is asserted at the header's input, not its output.

---

### 4.1 Initiation

**Goal**: prove `I` holds the first time the header is entered.

`forward_reach_at_header(cfg, header, inner)` computes a forward
over-approximation of first-entry states at the header:

1. Detects all back edges and excludes them.
2. Computes a topological order of the acyclic CFG skeleton.
3. Propagates SP (strongest postcondition) forward from the entry node.
   At each node, for each incoming non-back edge:
   - Applies the source node's effects via `apply_effects_sp`.
   - Applies the edge guard and edge phi-assignment effects.
   - OR-s the result into this node's reach formula.
4. Simultaneously maintains a `StoreFacts` map: concrete
   `(region, offset) → value` pairs produced by `MemoryStore` effects with
   constant offsets.  At join points (multiple predecessors), store facts are
   **intersected** — only facts that hold on every incoming path survive.
5. Inner/sibling loop headers are OR-seeded with their accepted invariants so
   the code after those loops is not widened to `True`.
6. Returns the header's reach formula augmented with store facts expressed as
   `select(region, k) == value` equations.

The store facts are critical: they let Z3 know concrete values like
`select(stack0, 0) == 0` (counter starts at 0) and `select(stack1, 0) == 1`
(SIZE == 1), without which `reach_h` is a symbolic memory expression Z3
cannot evaluate concretely.

**Check**: `oracle.feasibility(reach_h ∧ ¬I)`.

- Infeasible → initiation passes (no reachable first-entry state violates I).
- Feasible or Unknown → `InitiationFailed`.

---

### 4.2 Inductiveness

**Goal**: prove `I ∧ body ⊢ I` — if I holds at the header and one loop
iteration runs, I still holds at the header.

**Step A** — `edge_source_requirement(cfg, back_edge, &candidate)`:

1. Applies WP of the back edge's own transfer effects (phi assignments etc.)
   to `I`.
2. Conjoins the back edge guard.
3. Applies the **latch** node's own WP (standard `wp`, not Hoare-style).

Result: the requirement at the latch for `I` to hold at the header after
taking the back edge.

**Step B** — `backward_states(seeds=[(latch, latch_req)], excluded=all_back_edges, restrict_to=body, ignore_body_guards=true, inductive_assume=true)`:

- Propagates backward from the latch through the loop body only (edges
  restricted to those with both endpoints in `info.body`).
- Back edges are excluded to prevent cycles.
- `inductive_assume=true` → uses `wp_inductive` for all body nodes.
  For `Assume(c)`, `wp_inductive` produces `c → post` (Hoare-style) instead
  of the standard `c ∧ post`.  This prevents fresh nondet return variables
  (e.g. from `nondet_int()` in the loop condition) from making the
  implication unprovable.  See `LOOPS.md` §Inductiveness for the soundness
  argument.
- `ignore_body_guards=true` → edge guards within the body are suppressed
  (replaced with `True`), giving the unconditional WP rather than a
  path-specific one.

Result: `inductive_header = inductive_states[header]` (the WP of the
inductiveness requirement propagated back to the header).

**Check**: `oracle.implies(&candidate, &inductive_header)`.

- Valid → inductiveness passes (`I ⊢ WP(body, I)` at the header).
- Invalid or Unknown → `InductivenessFailed`.

Note: the latch node uses standard `wp` (not Hoare-style) in Step A.  In
practice the latch is an increment/decrement node with no `Assume` effects, so
this causes no problems.  If a latch ever had an `Assume` on a fresh nondet
variable, the affected candidate would be spuriously rejected (conservative,
not unsound).

---

### 4.3 Exit Closure

Skipped entirely when `assertion_postconditions` is empty (e.g. the
`discover_loop_invariants` pre-pass, and the entry-safety phase).

For each exit edge where the target node has an entry in
`assertion_postconditions`:

**Step A** — `edge_source_requirement(cfg, exit_edge, &postcondition)`:

1. Applies WP of the exit edge's transfer and guard to the violation
   postcondition.
2. Applies the source (last body) node's WP using standard `wp`.

Result: the violation condition as it must hold at the exit edge source.

**Step B** — `backward_states(seeds=[(exit_source, exit_req)], excluded=all_back_edges, restrict_to=body, ignore_body_guards=true, inductive_assume=false)`:

- Same body-restricted backward propagation as inductiveness, but:
  - `inductive_assume=false` → standard `wp` (not Hoare-style), because this
    is a violation path, not an inductiveness proof.
- Result: `exit_header = exit_states[header]` — the conditions at the header
  that lead to a violation through this exit edge.

**Check**: `oracle.feasibility(I ∧ exit_header)`.

- Infeasible → the invariant blocks all violations through this exit.
  Exit closure passes.
- Feasible or Unknown → `ExitClosureFailed { exit_edge }`.

**Why exit closure fails for loops with nondet calls**: backward WP through a
`Call { HavocMemory }` (e.g. `nondet_int()`) drops all memory constraints via
`HavocRegions`.  After propagation, `exit_header` collapses to only scalar
constraints like `j >= 0`.  Then `I ∧ (j >= 0)` is trivially satisfiable, so
exit closure always fails regardless of how strong I is.  The entry-safety
Phase-B pattern works around this by skipping exit closure and relying on
`run_backward` to perform the authoritative check.

---

## 5. Using Accepted Invariants (`backward.rs` — `run_backward`)

Once an invariant `I` is accepted for header `h`, it is pushed into the
`accepted: Vec<(CfgNodeId, Formula)>` list.  After all loops are processed,
`run_backward` is called with this list.

### 5.1 Back edge blocking

All back edges are registered as blocked in the `RuleEngine`.  The analysis
runs in topological order over the acyclic skeleton with back edges removed.

### 5.2 Forward reach injection

For each `(header, invariant)` pair, the invariant is **conjuncted** into
`summary.reach` at the header:

```
reach[header] = invariant          (if no prior reach)
reach[header] = reach[header] ∧ I (if prior reach exists)
```

If multiple invariants were accepted for the same header (rare), they are all
conjuncted via `conjunct_loop_invariants`.  This makes `reach[header]` the
forward over-approximation of reachable states at the header: since I is
inductive and holds at first entry, every actual header state satisfies I, so
I contains them.

### 5.3 Backward state seeding

`WP(¬obligation)` is computed at the assertion node and set as
`state[assertion_node]`.  This encodes the violation condition.

### 5.4 RuleEngine fixpoint

`engine.run_to_fixpoint` propagates:

- `reach` **forward** using SP (strongest postcondition) through node transfer
  effects and edge guards.
- `state` **backward** using WP of `¬obligation` through node transfer
  effects and edge guards.

Both propagate simultaneously in topological order (back edges blocked).

### 5.5 Decision at the function entry

At the entry node the engine has:

- `reach[entry]`: over-approximation of reachable states from program inputs.
- `state[entry]`: conditions under which a violation can propagate from the
  assertion back to the entry.

Final check:

| Query result | Judgement |
|---|---|
| `oracle.feasibility(reach ∧ state)` → Infeasible | `Verified` |
| `oracle.feasibility(reach ∧ state)` → Feasible (with model) | `BugFound` + counterexample |
| Neither determinable | `Unknown` |

The invariant constrains `reach` at the header, which flows forward through
the loop's exit path to the assertion site.  The backward `state` flows
backward through the exit path to the header.  At entry, `reach ∧ state`
infeasible means no reachable state is a violation state.

---

## 6. Precomputed Invariant Reuse (`driver.rs` → `backward.rs`)

`driver.rs` calls `discover_loop_invariants` once per function **before**
checking any assertion.  This calls `synthesize_loop_invariants` with empty
`assertion_postconditions` — exit closure is skipped for all phases.  The
resulting invariants are cached in `SummaryTables` and reused across all
assertion checks in the same function.

When `analyze_with_tables` is called for a specific assertion:

1. If precomputed invariants exist, `precomputed_satisfy_exit_closure` re-runs
   `check_loop_invariant_verbose` with the real `assertion_postconditions` for
   each precomputed invariant.
2. If **all pass** exit closure → reuse precomputed invariants, go straight to
   `run_backward`.
3. If **any fail** exit closure → fall through to `synthesize_loop_invariants`
   with this assertion's postconditions.  The pre-pass invariant may be too
   weak for this specific assertion; a stronger one is needed.

The exit-closure re-check for precomputed invariants has no syntactic
short-circuit: even loops that appear to not write any variable mentioned in
the obligation are re-checked, because the obligation formula may reference a
*loaded scalar* whose source region name does not appear in the formula text.

---

## 7. Summary of Checks Per Phase

| Phase | Initiation | Inductiveness | Exit closure |
|---|---|---|---|
| Algorithmic | ✅ | ✅ | ✅ |
| Entry-safety | ✅ | ✅ | ❌ (skipped; `run_backward` discharges) |
| ACHAR ICE learner | ✅ | ✅ | ✅ |
| Precomputed (pre-pass) | ✅ | ✅ | ❌ (no assertion site yet) |
| Precomputed (per-assertion reuse) | — | — | ✅ (re-checked before reuse) |

---

## 8. Soundness Properties

| Property | Status |
|---|---|
| Initiation via forward SP over-approximation | Sound |
| Inductiveness via Hoare-style WP for `Assume` | Sound (correct semantics) |
| Store-fact intersection at join points | Sound (conservative) |
| Phase-B exit-closure skip for entry-safety | Sound (`run_backward` discharges) |
| Concrete-integer filter on entry-safety store facts | Sound (prevents tautological candidates from variable-valued facts) |
| Whole-formula negation in entry-safety safety formula | Sound (prevents spurious type-bound atoms from contaminating candidates) |
| Latch node uses standard WP in inductiveness path | Conservative in failure only (spurious rejection, never false-Verified) |
| `HavocMemory` transparent in standard WP | Relies on paired `HavocRegions`; missing `HavocRegions` → more UNKNOWN, never false-Verified |

See `LOOPS.md` for the detailed soundness argument for each check.
