# Loop Invariant Synthesis Redesign

Notes from design discussion, 2026-05-17.

> **Status (2026-05-19):** The observer-disjunction approach and Phase-B exit-closure skip described below were reverted or removed as unsound (see LOOPS.md). The current implementation uses the three-phase synthesis pipeline (algorithmic → entry-safety → ACHAR ICE) with all three invariant checks required for every candidate. Memory-relational invariants (cross-region templates) remain an open item; array-2 is now covered by BMC (`--bmc-bound 1`) rather than invariant synthesis. The CHC/PDR and greedy N-term conjunction ideas in §Proposed New Synthesis Step are still unimplemented.

---

## Problem

For programs whose safety depends on a memory-relational invariant (e.g. `max >= numbers[k]`), the current Houdini/CHC/algorithmic candidate generators only produce scalar arithmetic candidates (counter bounds, predicate guards). They cannot express relations between a scalar accumulator and a memory cell, so synthesis returns no invariant and the result is UNKNOWN.

The observer-disjunction approach tried in the session (`i <= k || max >= numbers[k]`) was reverted because:

- `extract_lt_pair_terms` treats `Le` and `Lt` identically, producing `acc >= obs` for both `acc < obs` and `acc <= obs` violations. For a Le-violation the correct negation is strict (`acc > obs`), so the generated invariant is the violation itself, not its negation.
- Skipping exit closure to work around oracle limitations introduced a soundness hole: the initialization-vs-exit-condition collapse in `run_backward` gives a false Verified for unsafe programs whose loop starts at a fixed value (e.g. `j = 0` contradicts `j >= SIZE` in the backward state, collapsing state to False at entry).

---

## Key Observation

The backward state at the loop header, `S_h = assertion_postconditions[header]`, is `exit_condition AND violation`. A sound invariant `I` must satisfy `I AND S_h` infeasible, i.e. `I → NOT violation`.

The Houdini candidates already give us the `exit_condition` side (counter bounds). What is missing is the `NOT violation` side (the memory-relational condition).

**The conjunct approach:** for each accepted Houdini/CHC candidate `C`, generate

```
I_combined = C AND NOT violation_conjunct
```

where `violation_conjunct` is extracted from `S_h`. This combined candidate:

- Passes exit closure trivially: at the loop exit the `NOT violation_conjunct` component IS the assertion, so `I_combined AND S_h` is immediately infeasible.
- Passes inductiveness correctly for safe programs (e.g. `max` only increases, so `max >= numbers[0]` is preserved).
- Fails inductiveness correctly for unsafe programs (e.g. array-2: assigning `menor = array[0]` breaks `array[0] > menor`).

No skipping of exit closure is needed. This is the key advantage over the observer-disjunction approach.

---

## Forward Summary / Narrowing Loop Header Reach

The forward pass (back edges excluded) gives tight reach `R_h` at the first header entry — typically the initialization state (e.g. `i = 1, max = numbers[0]`). Two uses:

1. **Initiation is automatic**: `R_h → I_combined` is trivially satisfied when `violation_conjunct` is false at the initialization point (e.g. `max = numbers[0] → max >= numbers[0]`). We can use `R_h` to cheaply pre-filter candidates before oracle queries.

2. **Tighter inductiveness**: the paper criterion for inductiveness in a bidirectional setting is

   ```
   (I AND R_body) → WP(body, I)
   ```

   rather than the current `I → WP(body, NOT I)`. Using the forward reach inside the body as an additional hypothesis makes more candidates provable. We already compute `R_h` in `run_to_fixpoint`; exposing it to `synthesize_loop_invariants` enables this.

---

## Paper Criterion (POPL 2010, bidirectional may/must)

For loop invariant `I` to be sound in the bidirectional framework:

1. `reach_init_propagated_to_header → I` — initiation from the forward direction.
2. `(I AND reach_body) → WP(body, I)` — inductiveness using forward body reach as hypothesis.
3. `I AND S_h` infeasible — exit closure tying `I` to the specific assertion.

Our current checks approximate (2) as `I → WP(body, NOT I)` (no body reach context). The forward summary enhancement would close this gap.

---

## Proposed New Synthesis Step

After the existing Houdini/CHC/algorithmic pass (not replacing it), add:

1. Parse `S_h = assertion_postconditions[header]` into conjuncts; separate the exit condition from the violation conjuncts.
2. Negate each violation conjunct precisely (Lt → Ge, Le → Gt, Ge → Lt, Gt → Le).
3. For each candidate `C` already accepted (or failing exit closure from the Houdini pass), generate `C AND NOT violation_conjunct`.
4. Run `check_loop_invariant_verbose` with full exit closure — no skipping.

This is deterministic, needs no LLM, no loop-relevance filter, and exit closure is guaranteed to pass for safe programs by construction.

---

---

## Concrete Redesign Proposal (2026-05-17)

### Core Principle

The invariant checker must be sound even if synthesis is weak. Right now those two concerns are mixed, and that is what lets bad invariants slip through.

The current bug is exactly that: initiation in `loops.rs:443` is checked by cutting all back edges and running a backward test. For later loops, that under-approximates reachability and can make absurd candidates look valid (e.g. the exit condition `!(i < length)` passes initiation for loop 3 because earlier loops are invisible when back edges are cut globally).

### Algorithm: Loop-Local Proof, Per Assertion, Innermost-First

1. Build the loop nest tree from SCCs or natural loops.
2. For a given assertion A, compute which loops are on paths to A.
3. Process those loops innermost to outermost.
4. For each loop L, compute:
   - `Reach_h`: a sound forward over-approximation of states at the loop header.
   - `Post_e`: for each exit edge `e`, the backward obligation that must hold after exiting L.
   - `Step_L`: the one-iteration transition relation from header back to header, with inner loops already summarized.
5. Introduce an unknown invariant `Inv_L(s)`.
6. Prove `Inv_L` by solving these obligations:
   - **Initiation**: `Reach_h(s) → Inv_L(s)`
   - **Inductiveness**: `Inv_L(s) ∧ Step_L(s, s') → Inv_L(s')`
   - **Exit closure**: `Inv_L(s) ∧ Exit_e(s, s') → Post_e(s')` for every exit edge `e`
7. If all three pass: inject `Inv_L` at the header and continue outward.
8. If no invariant is found: return Unknown. Never accept a weak or generic invariant just because it passed an unsound pre-pass.

`Reach_h` is computed by a forward pass from the function entry with back edges excluded — this is tight (typically the preheader initialization state) and directly replaces the current initiation check that cuts all back edges globally and runs a backward feasibility query.

### Solving for Inv_L

**Primary: CHC/PDR.** Encode each loop as Horn clauses; let the solver synthesize `Inv_L`. The invariant is accepted only if the solver proves all three obligations. This is the cleanest correctness-first design.

For arrays: avoid quantified invariants at first. Instantiate only the cells that matter to the assertion. For `array_program.c`, the observed cells are `numbers[0]` through `numbers[4]`.

**Fallback: obligation-guided templates, not blind guard mining.**

Generate predicate atoms from:
- Loop guards (back-edge and exit conditions)
- Preheader facts (`Reach_h` at the header)
- Exit obligations (`Post_e`)
- Frame facts for variables/regions the loop does not touch
- Observer patterns (see below)

The key observer schema already present conceptually in `driver.rs:844`:

```
i <= k || max >= numbers[k]
```

This must be a first-class atom in Houdini/ICE template generation — not restricted to scalar bounds like `i >= 0`. The `k` is instantiated to each index that appears in the assertion's exit obligations.

### For array_program.c

The right per-assertion invariant is `i <= k || max >= numbers[k]` for each asserted index `k`. The loop proof runs five times with:

```
i <= 0 || max >= numbers[0]
i <= 1 || max >= numbers[1]
i <= 2 || max >= numbers[2]
i <= 3 || max >= numbers[3]
i <= 4 || max >= numbers[4]
```

These are the finite-index instantiations of the real universal invariant `∀ j < i. max >= numbers[j]`. The universally-quantified form is beyond the current SMT model; the per-assertion instantiation is tractable.

**Initiation check with Reach_h:** Before the max loop, the preheader sets `i = 1` and `max = numbers[0]`. So `Reach_h` includes `i = 1 ∧ max = numbers[0]`. For the k=0 invariant:
- `Reach_h → (i <= 0 || max >= numbers[0])`: `max = numbers[0]` makes the right disjunct trivially true. No oracle query needed.

**Inductiveness check with Step_L:** One step of the max loop is `if numbers[i] > max: max = numbers[i]; i = i + 1`. Given `i <= k || max >= numbers[k]`, after one step: if `i <= k` was false (so `max >= numbers[k]` holds), the new max ≥ old max ≥ numbers[k], and the invariant is preserved. If `i <= k` was true, after the step `i' = i + 1`; if `i' <= k` still, trivially holds; if `i' = k + 1 > k`, then we need `max' >= numbers[k]` — since the step processed `numbers[i] = numbers[k]`, max is updated if needed. This is the obligation the CHC/PDR or oracle must prove.

**Exit closure:** At the exit, `i >= length > k`, so `i <= k` is false, leaving `max >= numbers[k]` — which IS `Post_e` for that assertion. Trivially infeasible with the violation `max < numbers[k]`.

### Changes Needed in This Codebase

1. **Replace the initiation check** in `loops.rs:443` with a forward reachability computation at the loop header (back edges excluded, from function entry). The current backward-feasibility query under-approximates for later loops.

2. **Make synthesis assertion-driven** in `backward.rs:405`. Currently the same synthesis runs for the pre-pass (`discover_loop_invariants`, no assertion) and the per-assertion pass. These should be explicitly different: the pre-pass can use weak scalar candidates; the per-assertion pass must use obligation-guided templates including observer atoms.

3. **Add observer atoms to Houdini template generation** in `loops.rs`. For each `select(region, k)` term appearing in the exit obligations (`Post_e`), generate `counter <= k || accumulator >= select(region, k)` as a template atom — where counter and accumulator are identified from the loop guard and body update pattern.

4. **Remove generic pre-pass invariant acceptance as a source of truth for assertion proofs.** The pre-pass (`discover_loop_invariants`) is useful for callee summaries but must not short-circuit the assertion-specific synthesis path.

5. **Cache by (loop header, obligation shape)**, not just by function. Two assertions with different exit obligations need different invariants for the same loop.

---

## What Was Reverted

- `loop_touches_assertion` relevance filter and `loop_write_regions_and_vars` call in `synthesize_loop_invariants`
- `observer_disjunctive_candidates`, `extract_counter_acc_obs`, `extract_exit_counter_term`, `extract_lt_pair_terms`, `const_int_index` helpers
- `effective_postconditions` indirection in `synthesize_loop_invariants`
- Corresponding change to `precomputed_satisfy_exit_closure`
- `analyze_with_tables` precomputed block simplified back to: observer path (config=None) uses precomputed directly; regular path always synthesizes.
