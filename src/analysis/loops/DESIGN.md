# Loop Detection and Invariant Verification

## Loop detection

`detect_loops(cfg)` finds all natural loops via back-edge detection:
- A back edge `(src → header)` is any edge where `header` dominates `src`
  in the DFS tree (header is an ancestor of src).
- Each loop is represented as `LoopInfo { header, body, back_edges, exits }`.
- `sort_innermost_first` orders loops so inner loops are synthesized before
  their containing outer loops.

## VerifiedLoopInvariant

The only type accepted by `run_backward`. Constructible only through paths
that run all three checks. Never bypass the constructor.

```rust
pub struct VerifiedLoopInvariant {
    pub header: CfgNodeId,
    formula: Formula,
}
```

## Three-check verification — check_loop_invariant_verbose

Checks a candidate formula `I` against a loop:

1. **Initiation** — `I` holds at the loop header before the first iteration
   (i.e., the pre-header state implies `I`). Checked with `oracle.implies`.

2. **Inductiveness** — `I ∧ WP(body, I)` is satisfiable only when `I` is
   maintained: checked as `oracle.implies(I, WP(body, I))`.

3. **Exit closure** — at every loop exit, `I ∧ ¬loop-guard` implies
   the assertion postcondition. Checked with `oracle.implies`.

All three must pass for `InvariantCheckResult::Accepted`. The type system
enforces this: `VerifiedLoopInvariant::new` is only called on `Accepted`.

## Forward reach at header

`forward_reach_at_header` computes the strongest postcondition (SP) from the
pre-header up to the loop header, giving ACHAR an initial positive example
(a concrete reachable state at the header) to filter atoms against.

## TypeBound vs Assume in inductiveness

`TypeBound` effects contribute to SP (reach) but not to WP (state). This is
critical for loops containing `nondet_*()` calls: the fresh nondeterministic
variable `v` would otherwise appear in `WP(body, I)`, making
`oracle.implies(I, WP)` unprovable for any program-state invariant `I`. See
CLAUDE.md § TypeBound for the full soundness argument.
