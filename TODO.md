# TODO: Remaining Work For The Active Paper Driver

This file tracks what is still missing in the active `src/analysis` tree. The
archived implementation under `obsolete/src/analysis` is reference material
only.

## 1. Make The Analysis Interprocedural With Real Summary Flow

Current state:

- `src/analysis/summaries.rs` defines `Must`, `NotMay`, and `SummaryTable`.
- `src/analysis/driver.rs` has `answer_from_summaries`.
- Summary-use rules already exist in `src/analysis/rules.rs`.
- `src/analysis/driver.rs` now has `run_interprocedural`.
- Internal call edges now use:
  summary reuse -> MayCall query projection/recursion -> summary creation ->
  summary reuse retry.
- Unresolved internal calls now return `UNKNOWN` instead of unsound
  `NOT REACHED`.
- The local worklist inside each analyzed procedure is still intraprocedural.

Needed:

- Tighten the interprocedural alternation policy to match the paper more
  closely (current schedule is pragmatic, not a full formal alternation pass).
- Improve recursive-call handling beyond the current depth/stack cutoff.
- Add stronger evidence payloads for persisted summaries.
- Keep persisted summaries restricted to `Must` and `NotMay`.

## 2. Create And Reuse Summaries As A Full Lifecycle

Current state:

- Summary data structures and applicability checks exist.
- The interprocedural driver now creates:
  - `Must` summaries from reachable callee runs;
  - `NotMay` summaries from completed non-reachable callee runs.
- Created summaries are now persisted and reused on subsequent call edges.
- `SummaryTable::add` now de-duplicates identical summaries.
- MayCall projection now drops edge-local atoms at call boundaries.
- MayCall instantiation now applies call-instance renaming, formal/actual and
  retval/lhs bindings, and global/memory post-havoc at call boundaries.
- When projected call postconditions are vacuous, the active fallback uses:

```text
retval_<callee> < 0
```

- For the Figure-1 shape (`g`-like non-negative return pattern), the provider
  now synthesizes:

```text
NotMay: true => retval_<callee> < 0
```

Needed:

- Add broader summary applicability/coverage tests across different projected
  predicates and repeated call contexts.
- Replace the current call-post fallback with semantic caller-demand to callee
  return projection.
- Replace the current shape-based direct not-may synthesis with transition-level
  semantic proof obligations.
- Add provenance metadata that can explain why a summary was reused/rejected.
- Keep persisted summaries restricted to `Must` and `NotMay`.

## 3. Add Explicit Target Selection And Query Resolution

Current state:

- `src/main.rs` now builds assertion jobs for every embedded `may_assert(...)`
  site.
- For each site, the CLI runs:

```text
site reachability:      assert_violation(site)
violation reachability: assert_violation(site) && !assert_arg
```

- The transition layer now supports per-target assertion modes:
  `SiteReachability` and `Violation`.
- The CLI now reports per-site verdicts:
  `ASSERTION UNREACHABLE`, `ASSERTION TRUE WHEN REACHED`,
  `ASSERTION VIOLATION REACHABLE`, or `UNKNOWN`.
- The smoke test now covers direct bug and direct safe cases.

Needed:

- Implement `--assert` in the active driver so users can select a specific
  assertion/site from the CLI.
- Decide and document the stable output contract for modules with many
  assertion sites.
- Keep summaries target-specific while preserving soundness across differing
  assertion target modes.

## 4. Strengthen The Predicate And Transition Oracles

Current state:

- `src/analysis/oracle.rs` provides abstract oracle traits.
- `src/analysis/oracle.rs` now includes an SMT-backed `SmtPredicateOracle`.
- `src/analysis/transfer.rs` now includes an SMT-backed
  `SmtLlvmTransitionOracle` over metadata guard/effect predicates.
- `src/main.rs` now uses the SMT-backed predicate and transition oracles.
- `src/analysis/analysis_flow.md` now documents that `TransitionOracle`
  should answer the paper's transition queries, not own the driver or summary
  logic.

Needed:

- Improve the SMT encoding vocabulary so atoms become structured terms
  (integers/booleans/memory), not only Boolean symbols.
- Improve transition image computation so `theta` and `beta` are closer to real
  LLVM semantics than current guard/effect conjunctions.
- Decide whether to retain both SMT and syntactic transition-oracle variants
  long term.
- Improve `SmtLlvmTransitionOracle` so it computes more faithful approximations
  of:

```text
theta subset Post(Gamma_e, source)
Pre(Gamma_e, target) subset beta
```

- Keep LLVM adaptation in `llvm_adapter.rs`; do not move SMT setup there.
- Keep the paper-rule APIs unchanged while strengthening the backing oracle.

## 5. Add The Global May/Must Analysis Loop From The Paper

Current state:

- `run_intraprocedural` already runs a worklist over:

```text
(edge, source region, destination region)
```

- `MUST-POST` grows `Omega_n`.
- `NOTMAY-PRE` refines `Pi_n` and records may edges.

Needed:

- Decide what the top-level query loop is once summary reuse and learning are
  active.
- Alternate between summary lookup, intraprocedural rule application, and
  summary creation until the query is answered.
- Review whether the current requeue policy is sufficient.
- Decide how refined-region may edges should evolve after repeated splits.
- Add focused tests that name `Gamma_e`, `Pi_n`, `Omega_n`, `theta`, and
  `beta` directly.

## 6. Introduce Paper-Level Memory State

Current state:

- The active tree does not yet have a real paper-level memory object.
- `SmtPredicateOracle` now has an initial integer-array encoding for
  memory-shaped atoms:
  - `mem' = store(ptr, value)` is encoded with SMT `store`;
  - `x = load(mem', ptr)` (and `x = load(ptr)`) is encoded with SMT `select`.
- This is currently an atom-level encoding improvement, not a full memory
  state tracked through `Pi_n`, `Omega_n`, summaries, and query boundaries.
- The archived memory notes live in:

```text
obsolete/src/analysis/memory_updates.md
```

Needed:

- Decide what memory term belongs in active query/state vocabulary.
- Thread memory-state naming/versioning consistently through edge transfer and
  interprocedural projection (avoid ad-hoc `mem`/`mem'` conventions).
- Track memory through `Gamma_e`, summaries, and rule applications.
- Port only the useful ideas from the archived SMT memory plan.
- Keep `src/analysis` readable in paper vocabulary while doing this.

## 7. Improve LLVM Coverage

Current state:

- The adapter and transfer layers are intentionally small.
- Current smoke coverage only needs the direct `may_assert(0)` case.

Needed when demanded by the active driver:

- direct internal calls with summaries;
- return-value binding;
- `phi`;
- `switch`;
- `getelementptr`;
- casts/conversions;
- globals;
- heap objects;
- arrays and structs.

Unsupported behavior should remain explicit rather than silently treated as
safe.

## 8. Decide What To Do With `--assert`

Current state:

- `--assert` is parsed by the CLI but not implemented in the active driver.

Needed:

- Either translate command-line assertions into `ReachabilityQuery`;
- or make the CLI reject `--assert` more explicitly until return-query support
  exists.

## 9. Keep Documentation And Tests Aligned

Current state:

- The repository now has one active analysis tree and one archived tree.

Needed:

- Keep `README.md`, `TASKVIEW.md`, and `AGENTS.md` aligned with that split.
- Keep the smoke test aligned with actual active behavior.
- Do not describe archived code as active.

## 10. Verification Baseline

Keep these passing while evolving the active tree:

```sh
cargo fmt
cargo test
make -C tests smoke
```

Current unit-test baseline:

```text
39 passed
```
