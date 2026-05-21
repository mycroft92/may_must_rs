# Interprocedural Analysis

`analysis/interproc/`

## Files

| File | Role |
|---|---|
| `summaries.rs` | `SummaryTables`, `MaySummary`, `NotMaySummary` data types |
| `query.rs` | `ContextualSummaryTable` keyed by `(function_name, precondition)` |
| `providers.rs` | `CandidateProvider` trait; `NoProvider` and `ManualProvider` |
| `scheduler.rs` | Demand-driven query worklist |
| `smash.rs` | Bidirectional orchestrator per assertion |
| `driver.rs` | Module-level orchestration, summary inference, report generation |

## Summary types

- `NotMaySummary { precondition, postcondition }` — from `pre`, no execution
  reaches a state satisfying `post` (a violation condition).
- `MaySummary { precondition, postcondition }` — from `pre`, the callee may
  reach `post` (over-approx forward reach).
- `ReturnSummary` — return-value relation for a specific callee; injected as
  `TransferEffect::Obligation` at call sites.

## ContextualSummaryTable (query.rs)

Stores summaries keyed by `(name, precondition)`:
- `merge_notmay` / `merge_must` — add unless subsumed by an existing stronger entry.
- Projection helpers rename formal parameters for caller→callee variable mapping.

## Scheduler (scheduler.rs)

Worklist of `Query` objects (one per assertion per function):
- `dispatch_next` pops one query, runs `smash::run_smash`, records the verdict.
- Later-dispatched queries see summaries from earlier ones.
- `create_notmay_summary` / `create_must_summary` project results to
  interface variables after each dispatch.

## SMASH orchestrator (smash.rs)

Per assertion:
1. `backward::analyze_with_tables` — bidirectional fixpoint. Returns `Verified`,
   `BugFound`, or `Unknown`.
2. If `Unknown`: `dart::dart_explore` — bounded concrete path search.
3. Returns the first decisive verdict, or `Unknown` if both are inconclusive.

## Driver (driver.rs)

Module-level entry: `analyze_module_with_provider`

1. Pre-scan all functions: build vtable dispatch map.
2. Load external summaries from `CandidateProvider`.
3. Iterative round-robin: infer `ReturnSummary` per function.
   - Acyclic: `compute_return_summary`.
   - Cyclic with pointer param: `infer_cyclic_observer_summary` (ACHAR-backed).
4. Per-function: `analyze_with_summaries` → build Scheduler, enqueue queries, drain.
5. Assemble `ModuleReport`.

## Observer pattern for cyclic callees

When a looping function reads an array parameter and returns a summary value,
`infer_cyclic_observer_summary` synthesizes an invariant relating the return
value to array elements (e.g. `retval ≥ array[i]` for a max function), then
verifies it with the full bidirectional check.

## External contract

```rust
pub fn analyze_module_with_provider(
    graphs: &[FunctionGraph],
    memory_pure: &HashSet<String>,
    provider: &dyn CandidateProvider,
    oracle: &Oracle,
    config: &InvariantConfig,
) -> Result<ModuleReport, ProgError>
```

Produces `ModuleReport { reports, summaries, computed_summaries }`, consumed
by `main.rs::print_module_report`.
