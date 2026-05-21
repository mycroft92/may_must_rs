# End-to-End Analysis Flow

## Pipeline

```
frontend::program_graph::generate_program_graph
  → one FunctionGraph per defined function
  → AssertSite / AssumeSite / TypeBound records stripped from visible graph

pointer_analysis::andersen::run_alias_analysis
  → AliasResult (points-to map for all pointers)
  → run once per module before the adapter loop

cfg::adapter::adapt_with_purity_and_summaries
  → lowers FunctionGraph → AdaptedProcedure
     Phase 1: lower each instruction to TransferEffect list
     Phase 2: build PointerEnv, resolve Load/Store to select/MemoryStore
     Phase 3: apply ReturnSummary relations at call sites
     Phase 4: model memcpy/memset by unrolling

analysis::interproc::driver::analyze_module_with_provider
  → pre-scans all functions for vtable map
  → loads external summaries from CandidateProvider
  → iterative round-robin: infer ReturnSummary per function
     acyclic: compute_return_summary
     cyclic with pointer param: infer_cyclic_observer_summary (ACHAR-backed)
  → per-function: build Scheduler, enqueue one Query per AssertionSite, drain

analysis::interproc::scheduler::Scheduler
  → pops queries, calls smash::run_smash per assertion
  → after each verdict projects result to interface vars, updates SummaryTables

analysis::interproc::smash::run_smash
  (1) backward::analyze_with_tables — combined bidirectional fixpoint
        - synthesize_loop_invariants (ACHAR) if CFG is cyclic
        - inject VerifiedLoopInvariants into reach at headers
        - run_backward: fixpoint over forward reach and backward state
        - decision at entry: reach ∧ state UNSAT → Verified; SAT → BugFound
  (2) if (1) Unknown: dart::dart_explore — concrete path DFS
        - bounded by max_loop_iters
        - first SAT model → real BugFound

smt::oracle
  → all SMT queries: check_infeasible, check_feasible_with_model, implies
```

## Bidirectional semantics

- `reach` (forward over-approx SP): seeded at entry with `True`, widened
  at joins, loop invariants injected at headers.
- `state` (backward over-approx WP): seeded at assertion with `¬obligation`,
  propagated backward.
- Combined check: `reach ∧ state` UNSAT at entry → no reachable violation.

## TypeBound vs Assume

`TypeBound` narrows `reach` via SP but contributes nothing to `state` WP.
Used for type-system facts (`nondet_uint() ≥ 0`) that would otherwise make
loop invariant inductiveness unprovable. See CLAUDE.md for soundness argument.

## Error-termination encoding

`reach_error()`, `__assert_fail(…)`, `__VERIFIER_error()` are treated as
`may_assert(false)` — the call site is stripped to an unconditional
`AssertSite`, `WP(¬False) = True`, so `reach ∧ True = reach`. If the path
is unreachable, `reach` is empty → Verified.
