# Forward MUST — DART Concrete Path Exploration

`analysis/dart/mod.rs`

## Purpose

When the backward bidirectional analysis returns `Unknown` (no loop invariant
found or analysis inconclusive), DART performs bounded concrete path
exploration to find real counterexamples.

## dart_explore

Depth-first search over concrete paths through the CFG:
- At each branch, queries the SMT oracle to check which paths are feasible.
- Bounded by `DartConfig::max_loop_iters` — each back edge is counted.
- Returns `BugFound` with a concrete model on the first SAT path that reaches
  the assertion violation, or `Unknown` if all paths within the bound are
  infeasible or the bound is exceeded.

## Verdict semantics

- `BugFound` from DART is a *real* counterexample (a satisfying assignment
  to all program variables along a concrete path).
- `Unknown` from DART means the bound was exhausted; it is not a proof of safety.

DART is used only as a fallback bug-finder, never as a proof.

## DartConfig

```rust
pub struct DartConfig {
    pub max_loop_iters: usize,  // default: 5
}
```
