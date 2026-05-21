# Soundness Bug: Inductiveness Check Omitted Loop Continuation Guard

## Symptom

`sum04-1.i` from the SV-COMP `c/loops` benchmark was verified as **SAFE** when it
is **UNSAFE**.  The program computes `sn = 6` at loop exit and asserts
`sn == 16 || sn == 0`, which always fails.

## Root Cause: Wrong Inductiveness Check

In `src/analysis/loops/mod.rs`, `check_loop_invariant_verbose` used
`ignore_body_guards=true` when calling `backward_states` for the inductiveness
check.  This suppressed all edge guards during the backward WP computation,
making `inductive_header` equal to `WP_body(I)` without the loop continuation
guard.

The check then was:

```
I → inductive_header
```

With `ignore_body_guards=true`, `inductive_header = WP_body(I)` (no loop guard).
The invariant `sn == 0` vacuously satisfied this because:
- With guards suppressed, both branches of `if (i < 4) { sn += 2; }` contributed
  to WP, giving `WP_body(sn == 0) = (sn == 0) OR (sn == -2)`.
- `sn == 0 → (sn == 0) OR (sn == -2)` is trivially true.

So the invariant `sn == 0` was accepted as inductive even though the loop body
modifies `sn`.  This injected `sn == 0` into the forward reach at the loop header,
making `reach ∧ state` infeasible at the assertion, producing a false SAFE verdict.

## Correct Inductiveness Rule

Hoare-style inductiveness: `{I ∧ B} S {I}`, i.e.:

```
I ∧ loop_continuation_guard → WP(body, I)
```

With `ignore_body_guards=false`, `backward_states` from the latch seeded with `I`
gives:
```
inductive_header = B ∧ WP_body(I)
```

The correct check is then `(I ∧ B) → (B ∧ WP_body(I))`, which cancels `B` and
reduces to `I ∧ B → WP_body(I)` — correct.

## Why Extracting B from `info.header`'s Outgoing Edges Fails

The CFG is at the **instruction level** (one node per visible instruction, not per
basic block).  `info.header` points to the **first instruction** of the header
basic block (e.g., a `load`).  Its direct outgoing edges are sequential (guard =
True).  The actual conditional branch lives in a separate node deeper in the body.

Attempting to extract the continuation guard from `outgoing_edges(info.header)` and
applying WP of the header node's effects yields `True` — wrong.

## Fix

Compute the continuation guard `B` by running a second `backward_states` call
seeded with `Formula::True` at the latch:

```rust
let continuation_guard = backward_states(
    cfg,
    &[(info.latch, Formula::True)],
    &excluded,
    Some(&info.body),
    false,   // respect edge guards
    inner,
    false,
)?
.and_then(|states| states.get(&info.header).cloned())
.unwrap_or(Formula::True);
```

This traverses the same body path, including the actual branch node with its
conditional edge guard.  The result at `info.header` is exactly `B` expressed in
pre-state variable terms.

Then the inductiveness check:

```rust
let inductive_antecedent = Formula::and(candidate.clone(), continuation_guard);
oracle.implies_with_model(&inductive_antecedent, &inductive_header)
```

checks `(I ∧ B) → inductive_header` = `(I ∧ B) → (B ∧ WP_body(I))`, which is
the Hoare rule `{I ∧ B} S {I}`.

## Impact

- `sum04-1.i`: was SAFE (unsound), now UNKNOWN (correct; DART needed for UNSAFE)
- `loop_counter_assertion_is_safe` test: now passes correctly
- `array_1_verified` test: now passes correctly
- All 144 tests pass.
