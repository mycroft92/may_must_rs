# Backward Analysis — Assertion Checking

`analysis/backward/mod.rs` — top-level entry for checking one assertion.

## Entry points

```rust
pub fn analyze_with_tables(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    tables: &SummaryTables,
    config: Option<&InvariantConfig>,
    debug_names: &HashMap<String, String>,
) -> Result<AssertionResult, BackwardError>
```

For acyclic CFGs, calls `run_backward` directly. For cyclic CFGs, calls
`synthesize_loop_invariants` first.

## synthesize_loop_invariants

Detects loops (innermost first), runs `achar::synthesize_with_cegis` per
loop. Each accepted candidate is wrapped in `VerifiedLoopInvariant`. If any
loop produces no candidate within the timeout, returns
`Err(BackwardError::CyclicCfgUnsupported)`.

Pre-computed invariants (from `infer_cyclic_observer_summary`) can bypass
ACHAR via the `precomputed` parameter.

## run_backward

1. Conjuncts loop invariants into `reach` at loop headers.
2. Seeds `state` at the assertion node with `¬obligation`.
3. Calls `RuleEngine::run_to_fixpoint`.
4. At entry: calls `bugfound(entry, oracle, acyclic)` then `verified(entry, oracle)`.

## Rules (analysis/backward/rules.rs)

`RuleEngine` owns the `NodeSummary` map for one CFG.

Forward direction (reach / MAY):
- `forward_may_post(edge)` — SP of edge effects; widens `reach` via disjunction.
- `forward_may_usesummary(edge, tables)` — injects callee `MaySummary` at call edges.

Backward direction (state / NOT-MAY):
- `notmay_pre(edge)` — WP of edge effects; widens `state` backward.
- `notmay_pre_usesummary(edge, tables)` — injects callee `NotMaySummary`.
- `notmay_pre_pruned(edge)` — skips backward propagation when `reach` makes
  the path infeasible (pruning for efficiency).

## NodeSummary (analysis/backward/node_summary.rs)

```rust
pub struct NodeSummary {
    pub node:  CfgNodeId,
    pub reach: Formula,   // forward over-approx SP
    pub state: Formula,   // backward over-approx WP of ¬obligation
}
```

`combined()` returns `reach ∧ state`. Verified when this is UNSAT at entry.
