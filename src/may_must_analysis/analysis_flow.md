# Analysis Flow

## End-to-End Flow

1. `llvm_utils::program_graph::generate_program_graph`
   builds one raw instruction graph per defined function.

2. `program_graph.rs`
   removes `may_assert`, `may_assume`, and `may_type_bound` from the visible
   instruction graph, recording each as an `AssertSite`, `AssumeSite`, or
   `TypeBound` respectively.

2.5. `common::alias_analysis::run_alias_analysis`
   runs field-sensitive, flow-insensitive Andersen alias analysis on the full
   module (called once by the driver before the summary loop, and once per
   function by `analyze_with_summaries`).  The `AliasResult` is threaded into
   all `adapt_with_purity_and_summaries` calls.

3. `common::adapter::adapt[_with_purity_and_summaries]`
   lowers one `FunctionGraph` into:
   - an `AbstractCfg` with `TransferEffect` sequences per node
   - a list of lowered `AssertionSite` obligations
   - a `debug_names` map (alloca SSA name → C source variable name)
   `resolve_memory_effects` builds the `PointerEnv`, resolves `Load`/`Store`
   to `select`/`MemoryStore`, and substitutes callee `ReturnSummary` relations
   at call sites.  `lower_assumes` injects `Assume` or `TypeBound` effects;
   the WP of `TypeBound` is identity (sound for type-system facts; avoids
   breaking inductiveness of loop invariants over nondeterministic inputs).

4. `driver.rs::analyze_module_with_provider`
   runs the full interprocedural analysis:
   - Pre-scans all functions to build the module-wide vtable map.
   - Loads external summaries from the `CandidateProvider`.
   - Iteratively infers `ReturnSummary` entries (up to `graphs.len()` rounds
     to converge mutual calls).  Cyclic callees that observe an array
     parameter use the observer pattern (`infer_cyclic_observer_summary`).
   - Converts inferred summaries to `MaySummary` / `NotMaySummary` entries
     in `SummaryTables`.
   - Calls `analyze_with_summaries` per function.

5. `driver.rs::analyze_with_summaries`
   per-function orchestration:
   - Builds a `Query` per assertion site and enqueues them into the
     `Scheduler`.
   - Drains the scheduler, collects `SmashRunResult`s, assembles a
     `ProcedureReport`.

6. `scheduler.rs::Scheduler::dispatch_next`
   pops each query and calls `smash::run_smash`.  After each verdict,
   `create_notmay_summary` / `create_must_summary` project the result to
   procedure-interface variables and merge it into the `ContextualSummaryTable`.

7. `smash.rs::run_smash`
   bidirectional orchestrator per assertion:
   - **Backward NOT-MAY** (`analyze_with_tables`): computes `reach ∧ state`
     via the combined bidirectional fixpoint.  Loop invariants are injected
     into `reach` at headers; backward WP of `¬obligation` seeds `state`.
     `Verified` if `reach ∧ state` is infeasible at entry; `BugFound` if SAT.
   - **Forward MUST / DART** (`forward_must::dart_explore`): if the may
     direction returns `Unknown`, enumerate concrete paths depth-first
     (bounded by `max_loop_iters`).  First SAT model is a real counterexample.
   - Returns the first decisive verdict, or `Unknown` if both are inconclusive.

8. `loops.rs` / `achar.rs`
   loop invariant machinery:
   - `detect_loops` / `sort_innermost_first` identify loop structure.
   - `check_loop_invariant_verbose` checks initiation, inductiveness, and
     exit closure against real assertion postconditions.  Only
     `VerifiedLoopInvariant` (all three checks pass) is accepted by
     `run_backward`.
   - ACHAR (`achar.rs`) uses grammar-based CEGIS to synthesise candidates;
     all three checks are run per candidate before acceptance.

9. `oracle.rs` / `smt/solver.rs`
   all SMT queries go here.  `oracle.check_infeasible`, `oracle.implies`, and
   `oracle.check_feasible_with_model` cover the three query shapes used by the
   analysis.

10. `main.rs`
    prints one `ProcedureReport` and a combined module verdict per function.

## Lowering Notes

- Branch conditions become edge guards.
- `phi` nodes become predecessor-specific edge assignments.
- Multiple concrete exits become one synthetic exit.
- `zext i1 → i32` lowers through `bool_to_int`.
- Memory uses integer arrays plus `select` / `store`.
- Pointer parameters become external regions `fn$__ext_N`; globals become
  `global$<name>` regions.
- Unsupported instructions are reported as `UNKNOWN`, not silently accepted.

## Bidirectional Semantics

- `reach` (forward): overapproximates reachable states; seeded with loop
  invariants at headers.
- `state` (backward): WP of `¬obligation`; encodes violation conditions.
- Combined check at entry: `reach ∧ state` infeasible → `Verified`.
- `TypeBound` effects narrow `reach` via SP but contribute nothing to `state`
  WP, keeping loop invariant inductiveness provable for nondeterministic
  type-constrained inputs (e.g. `nondet_uint()`).

## Error-Termination Sentinels

Calls to `reach_error()`, `__assert_fail(...)`, and `__VERIFIER_error()` are
treated as `may_assert(false)`: the call site must be unreachable for the
program to be safe.

Encoding (in `program_graph.rs`):
- The call is stripped from the visible CFG (like `may_assert`).
- An `AssertSite { is_unconditional_fail: true }` is recorded, anchored at
  the predecessor or successor visible instruction.

In `adapter.rs`:
- `lower_assertions` emits `Formula::False` as the obligation (skipping
  `lower_bool_value`).

Backward semantics:
- `WP(¬False)` = `WP(True)` = `True`: the violation condition is trivially
  satisfied everywhere.
- `reach ∧ True` = `reach`: if the path to the call site is unreachable
  (empty `reach`), the analysis returns `Verified`.

The SV-COMP benchmark runner (`benchmarks/sv-comp/`) also handles these via
`svcomp_shim.h` macros and `convert.py` stripping, but the Rust encoding is
the authoritative mechanism — it works on raw bitcode without preprocessing.
