# Design Note: Assume WP Semantics in Inductiveness Check

## Context

The loop invariant inductiveness check lives in `check_loop_invariant_verbose`
in `src/may_must_analysis/loops.rs`.  It checks whether a candidate invariant
`I` is preserved by one loop body iteration:

```
oracle.implies(I, inductive_header)
```

where `inductive_header = WP(body, I)` — the weakest precondition of `I`
propagated backward through one full loop body pass (via `backward_states`).

## The Problem

`TransferEffect::Assume(c)` uses `c AND post` as its WP semantics:

```rust
TransferEffect::Assume(condition) => Formula::and(condition.clone(), post.clone()),
```

This is correct for the **violation analysis**: a violating trace must pass
through the assume, so `c` must be true on that path.

But for **inductiveness**, the correct formulation is:

> "If `I` holds at the start of an iteration AND `c` holds (the path is
> feasible), then `I` holds after the iteration."

Which is: `I ∧ c → WP_rest(I)`, equivalently `I → (c → WP_rest(I))`.

Our check computes `I → (c AND WP_rest(I))`, which splits into two
obligations:

1. `I → c`  — the invariant must imply the assume condition
2. `I → WP_rest(I)` — actual inductiveness

Obligation 1 fails whenever `c` involves a **fresh call-return variable** that
appears nowhere in `I`.  For example, `nondet_uint()` called inside a loop
condition produces a fresh `v_call` and an `Assume(v_call >= 0)`.  The oracle
treats `v_call` as universally quantified, so `I → v_call >= 0` is invalid for
any invariant `I` that does not mention `v_call`.  Result: inductiveness always
fails for such loops, producing UNKNOWN.

## Current Workaround

We introduced `TransferEffect::TypeBound(c)` with WP = identity (drops `c`
entirely from WP).  Type-system facts from `nondet_*()` macros and ZExt/SExt
bounds are emitted as `TypeBound` instead of `Assume`.  This restores
inductiveness checks at the cost of removing the condition from the backward
WP entirely.

`TypeBound` is sound because the conditions it carries are always satisfied by
well-typed programs, so removing them from WP does not cause false VERIFIED
verdicts.  The forward reach (SP) still picks them up.

## The Deeper Question

Could we instead fix the inductiveness check to use Hoare-style implication for
`Assume` effects?

Instead of:
```
WP(Assume(c), post) = c AND post      ← current, correct for violation analysis
```

Use in the inductiveness-specific WP computation:
```
WP(Assume(c), post) = c → post        ← correct for inductiveness
```

This would mean:
- `I → (c → WP_rest(I))` — if c is false the condition is vacuously true;
  if c is true we need I to be preserved.  Both are correct.
- No need to distinguish `TypeBound` from `Assume` for this purpose.
- Would also fix cases where user `__VERIFIER_assume` constraints appear inside
  loops — currently those also produce overly strong inductiveness obligations.

## What to Try

1. Add a `wp_mode` parameter (or separate function) to `backward_states` in
   `loops.rs` that switches `Assume` WP from `c AND post` to `c → post`.
   Only the inductiveness call to `backward_states` uses the implication mode;
   the initiation and exit-closure calls keep `c AND post`.

2. Verify that the change does not break any existing tests.

3. Run the SV-COMP benchmark suite and compare results.  If inductiveness
   improves across the board (not just for type-bound variables), the
   `TypeBound` workaround can potentially be retired and all `nondet_*()`
   macros can revert to plain `assume()`.

4. Check soundness: using `c → post` means inductiveness is checked over a
   larger set of states (those where c is false are vacuously covered).  This
   is sound because the real loop only executes on paths where c holds; we are
   simply not over-requiring the invariant to hold on infeasible paths.

## Files Involved

- `src/may_must_analysis/loops.rs` — `check_loop_invariant_verbose`,
  `backward_states`
- `src/common/abstract_cfg.rs` — `wp_one` (WP semantics per effect)
- `verification.h` — `nondet_*()` macros (could revert to `assume()`)
- `src/common/llvm_utils/program_graph.rs` — `AssumeSite.is_type_bound` field
- `src/common/adapter.rs` — `lower_assumes`, ZExt/SExt `TypeBound` emission
