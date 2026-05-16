# Design Note: Assume WP Semantics in Inductiveness Check

## Status: IMPLEMENTED (Hoare-style fix, 2026-05-16)

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

The old check computed `I → (c AND WP_rest(I))`, which splits into two
obligations:

1. `I → c`  — the invariant must imply the assume condition
2. `I → WP_rest(I)` — actual inductiveness

Obligation 1 fails whenever `c` involves a **fresh call-return variable** that
appears nowhere in `I`.  For example, `nondet_uint()` called inside a loop
condition produces a fresh `v_call` and an `Assume(v_call >= 0)`.  The oracle
treats `v_call` as universally quantified, so `I → v_call >= 0` is invalid for
any invariant `I` that does not mention `v_call`.  Result: inductiveness always
fails for such loops, producing tautology invariants (`True`) or UNKNOWN.

## Previous Workaround (SUPERSEDED)

We had introduced `TransferEffect::TypeBound(c)` with WP = identity for
`nondet_*()` macros.  This restored inductiveness but also removed the type
condition from the **violation WP** for calls made outside the loop body,
allowing the oracle to find spurious negative models (e.g., `n = -1` for
`nondet_uint()`) that caused false UNSAFE verdicts (UNSOUND results in
SV-COMP benchmarks like `count_up_down-1` and `trex03-2`).

## The Fix: Hoare-style WP for Inductiveness Only

The principled solution is to use `c → post` (Hoare-style implication) for
`Assume(c)` only in the inductiveness-specific backward propagation, while
keeping `c AND post` everywhere else.

### Changes Made

**`src/common/abstract_cfg.rs`** — added `wp_inductive` to `Transfer`:

```rust
pub fn wp_inductive(&self, post: &Formula) -> Formula {
    self.effects
        .iter()
        .rev()
        .fold(post.clone(), |acc, effect| wp_one_inductive(effect, &acc))
}

fn wp_one_inductive(effect: &TransferEffect, post: &Formula) -> Formula {
    match effect {
        TransferEffect::Assume(condition) => Formula::implies(condition.clone(), post.clone()),
        other => wp_one(other, post),
    }
}
```

**`src/may_must_analysis/loops.rs`** — added `inductive_assume: bool` parameter
to `backward_states`.  The inductiveness call passes `true`; initiation and
exit-closure calls pass `false`:

```rust
let pre_at_source = if inductive_assume {
    cfg.node(edge.source).ok()?.transfer.wp_inductive(&post_at_source)
} else {
    cfg.node(edge.source).ok()?.transfer.wp(&post_at_source)
};
```

**`verification.h`** — all `nondet_*()` macros reverted from `type_bound()` back
to `assume()`.  The Hoare-style WP fix makes `TypeBound` unnecessary for this
purpose.  `TypeBound` is still emitted by the adapter for ZExt/SExt range bounds,
which is correct and unrelated to this fix.

### Soundness

Using `c → post` for inductiveness means we check the invariant is preserved
on all paths where `c` holds.  When `c` is a fresh variable constraint (`v >= 0`),
the path where `c` is false is infeasible in any real execution — the SMT model
is unbounded but the real program only runs on well-typed values.  The violation
WP still uses `c AND post`, so the bidirectional `reach AND state` check at
entry is unaffected.

### Result (SV-COMP benchmarks, 2026-05-16)

- `count_up_down-1`: UNSOUND → SAFE (fixed)
- `trex03-2`: UNSOUND → SAFE (fixed)
- Remaining UNSOUND: `linear_sea.ch`, `bin-suffix-5`, `veris.c_NetBSD-libc_loop.i`
  (heap / array alias cases — separate work)

## Files Involved

- `src/may_must_analysis/loops.rs` — `check_loop_invariant_verbose`,
  `backward_states`
- `src/common/abstract_cfg.rs` — `wp_one`, new `wp_inductive`
- `verification.h` — `nondet_*()` macros (reverted to `assume()`)
- `src/common/llvm_utils/program_graph.rs` — `AssumeSite.is_type_bound` field
- `src/common/adapter.rs` — `lower_assumes`, ZExt/SExt `TypeBound` emission
