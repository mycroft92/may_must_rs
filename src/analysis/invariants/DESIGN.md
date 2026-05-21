# ACHAR — Loop Invariant Synthesis

CEGIS (Counterexample-Guided Inductive Synthesis) with an ICE (Implication
CounterExample) learning strategy. Produces `VerifiedLoopInvariant` — all
three checks (initiation, inductiveness, exit closure) pass before a candidate
is returned. Returns `None` on timeout.

## Vocabulary

Two atom pools are built from the loop's CFG:

- **`pred_atoms`** — atoms extracted directly from CFG edge guards and
  predicate-assign effects (loop conditions like `i < n`).
- **`combo_atoms`** — pairwise comparisons (`≤`, `<`, `=`, `≥`, `>`) between
  terms collected from effects and the assertion postcondition. Filtered to
  positive-consistent atoms (not false at the pre-header state).

## ICE examples

- **Positive example** — a concrete reachable state at the loop header,
  computed by `forward_reach_at_header`. Atoms that are false here cannot be
  part of any sound invariant.
- **Negative examples** — violation states (models from failed exit-closure or
  inductiveness checks). Atoms that are true on all negatives are useless for
  ruling them out.

## Tiered candidate search

Candidates are tried in 11 tiers, stopping at the first accepted one:

| Tier | Shape | Rationale |
|---|---|---|
| 1 | Negation of violation conjuncts | Direct safety property |
| 2 | `counter_init ∥ negation_atom` | Counter-escape (loop runs ≥1 times) |
| 2b | Tier 2 + immutable preheader facts | When zero-trip exit needs ruling out |
| 3 | `pred_atom ∥ negation_atom` | Loop guard disjunction (handles zero-trip) |
| 4 | Predicate atoms alone | CFG-derived conditions |
| 5 | Pairwise conjunctions of pred atoms | Compound CFG conditions |
| 6 | `counter_init ∥ pred_atom` | Counter + loop guard |
| 7 | `counter_init ∥ combo_atom` | Counter + relational atom |
| 8 | Positive-consistent combo atoms | Relational vocabulary |
| 9 | Pairwise conjunctions of combo atoms | Compound relational |
| 10 | ICE-guided disjunctions | Example-steered `pos ∥ safety` |
| 11 | Pairwise disjunctions of combo atoms | Fallback |

Each candidate is passed to `check_loop_invariant_verbose`. A `Rejected`
result with a witness updates the ICE feedback; a `Screened` result (ruled out
by existing examples) skips the SMT call. `Accepted` wraps into
`VerifiedLoopInvariant` and returns immediately.

## Immutable preheader facts

Facts `select(region, 0) = K` where `region` is never written in the loop body
are conjoined with candidates in tier 2b. They are always true at the header
(set before the loop) and inductive (body never changes them), so conjoining
them adds information to exit closure without breaking inductiveness.
