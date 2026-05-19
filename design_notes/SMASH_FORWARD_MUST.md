# SMASH Paper Equivalence — Forward MUST Direction

This document records the **directional mapping** between SMASH-paper
analyses and our types — i.e., where the forward MUST direction lives
in our codebase given that `TransferFn::sp` does not yet model memory.
For the **larger architectural realignment** (query-driven worklist,
contextual summaries, demand-driven scheduling), see
[`../Rearch.md`](../Rearch.md) and the corresponding refactor roadmap
in [`../TODO.md`](../TODO.md).

Our only intentional addon to the paper is ACHAR loop-invariant
synthesis to keep backward NOT-MAY terminating over loops.

## Key insight: forward MUST = backward analysis on (acyclic or unrolled) CFG

The paper presents four analyses (forward MAY, forward MUST, backward
NOT-MAY, backward NOT-MUST) as distinct directions.  In implementation
terms, **forward MUST and backward NOT-MAY-on-acyclic-CFG produce
equivalent BugFound witnesses** when both are sound:

- **Forward MUST**: start at entry with `True`, propagate concrete reachable
  states forward via SP, feasibility-check at each step.  At the assertion
  site: `must_reach[site] ∧ ¬obligation` SAT → bug.
- **Backward on acyclic CFG**: start at the assertion site with `¬obligation`,
  propagate via WP backward, with no loop-invariant widening.  At entry:
  `reach ∧ state` SAT → bug.

On an acyclic CFG (or one unrolled to acyclic via BMC), both are precise
modulo SMT.  Both produce a real concrete bug witness when SAT.  They
differ only in directionality and intermediate caching, not in soundness
or completeness.

**This codebase realises forward MUST as the latter**: BMC unrolls cyclic
CFGs to acyclic ones, then the existing backward analysis runs over the
acyclic result and reports BugFound when its (now sound) `reach ∧ state`
check is SAT.  No separate `forward_must_post` rule is needed — and one
would not work today, because `TransferFn::sp` does not model memory
effects (`sp_one` for `MemoryStore`/`Load` is a no-op).  The backward
direction's `wp` does model memory via store substitution, so backward
on acyclic is the only memory-aware sound BugFound path available.

## The four directions (paper recap)

For each procedure, the paper defines four analyses:

| Direction × Approximation | Name | Purpose |
|---|---|---|
| Forward + over-approx (SP) | **MAY** | Filter feasible paths; assist backward NOT-MAY |
| Forward + under-approx (concrete) | **MUST** | Find real bugs |
| Backward + over-approx (WP) | **NOT-MAY** | Prove safety |
| Backward + under-approx | **NOT-MUST** | Refine bug preconditions |

The paper's full algorithm alternates **forward MUST ⇄ backward NOT-MAY** as
the two decisive directions.  Forward MAY and backward NOT-MUST are
supporting passes.

## Mapping to our code

| Paper concept | Our realization |
|---|---|
| Backward NOT-MAY (WP) | `RuleEngine::notmay_pre*` |
| Forward MAY (SP) | `RuleEngine::forward_may_post*` |
| Forward MUST | **Backward NOT-MAY on acyclic CFG**, where acyclicity is either native or obtained via `bmc::bmc_check` unrolling.  Soundness: no loop-invariant widening, so the resulting `reach ∧ state` SAT model is concrete.  See the *key insight* above. |
| Backward NOT-MUST | absent (out of scope; supports interprocedural bug-precondition refinement but not soundness) |
| Alternation orchestrator | `smash::run_smash` — calls the may direction, then BMC if needed |

## NodeSummary

```rust
pub struct NodeSummary {
    pub node: CfgNodeId,
    /// Forward MAY (over-approximate reach), used by `notmay_pre_pruned`.
    /// SMASH paper: `MAY`.
    pub reach: Formula,
    /// Backward NOT-MAY (over-approximate violation precondition).
    /// SMASH paper: `NOT-MAY`.
    pub state: Formula,
    /// Forward MUST scaffolding.  Currently unused in the main verdict path
    /// because `TransferFn::sp` does not model memory (`sp_one` for
    /// `MemoryStore`/`Load` is a no-op), so an SP-based forward MUST would
    /// produce spurious BugFound on any memory-using program.  See the
    /// design discussion above for why backward-on-acyclic is the
    /// memory-aware realization instead.  Field retained for future work
    /// (e.g. memory-aware SP, or BMC-side per-step witness caching).
    pub must_reach: Formula,
}
```

## Verdict logic (current, paper-equivalent)

```
analyze_smash(procedure):
    run backward NOT-MAY to fixpoint over the CFG, using loop invariants
    (our addon) to terminate over loops.

    cfg_is_acyclic = (cfg has no back edges)

    if cfg_is_acyclic AND reach ∧ state SAT at entry:
        # Forward MUST direction (realized as backward-on-acyclic).
        # No widening occurred, so the SAT model is concrete and the bug
        # is real.
        return BugFound(model)

    if reach ∧ state UNSAT at entry:
        # Backward NOT-MAY at entry: safety proven.
        return Verified

    # Cyclic CFG with no decisive may verdict: try forward MUST via BMC
    # unrolling.  bmc_check unrolls to bound k, then runs the same backward
    # analysis on the acyclic unrolled CFG.  Sound BugFound iff SAT.
    if bmc_check returns BugFound:
        return BugFound

    return Unknown
```

## Why backward on acyclic = forward MUST

The two directions check the same logical condition:

- Forward MUST asks: does there exist a concrete entry state from which
  some execution reaches the assertion site with the violation holding?
- Backward NOT-MAY on the same CFG asks: does there exist an entry state
  such that the WP of `¬obligation` propagated backward from the assertion
  to the entry is satisfied?

On an acyclic CFG (no widening, no invariants injected), both questions
reduce to the same SMT formula: `path-constraint ∧ ¬obligation`.  Our
backward direction computes this exactly via WP through node and edge
transfers — and crucially, WP handles memory via store substitution
(`wp_one` for `MemoryStore` substitutes the stored value into selects on
the same region).  SP does not.

So implementing forward MUST as `backward-on-acyclic-CFG` is not a
shortcut — it is the **only memory-aware sound BugFound path** available
without rewriting the SP transformer.

## Out of scope / future work

- **Backward NOT-MUST.**  Refines interprocedural bug preconditions; not
  required for soundness or for the current SV-COMP coverage targets.
- **Fixpoint alternation between may and must directions over a shared
  summary DB.**  The current `run_smash` calls each direction once.  The
  paper's full algorithm iterates with cross-feed; this is a precision
  enhancement, not a soundness one.
- **Memory-aware SP.**  Would enable a true forward MUST rule running
  alongside backward NOT-MAY in the same fixpoint loop.  Significant work
  in `sp_one`; tracked as a future direction.
- **Cross-procedure MUST summaries** (`smash::MustPathSummary` consumed by
  callers).  Skeleton present but unused; needs the alternation fixpoint
  to be useful.
