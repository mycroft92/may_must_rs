# TODO: Remaining Work For The Active Paper Driver

This file tracks what is still missing in the active `src/analysis` tree. The
archived implementation under `obsolete/src/analysis` is reference material
only.

## 1. Make The Analysis Interprocedural With Real Summary Flow

Current state:

- `src/analysis/summaries.rs` defines `Must`, `NotMay`, and `SummaryTable`.
- `src/analysis/driver.rs` has `answer_from_summaries`.
- Summary-use rules already exist in `src/analysis/rules.rs`.
- The active worklist is still intraprocedural.
- Call-edge summary reuse is not yet active in the worklist.

Needed:

- Reuse applicable summaries before intraprocedural work.
- Add call-edge handling through:
  - `must_post_use_summary`
  - `not_may_pre_use_summary`
- Instantiate callee queries from caller state.
- Resume caller analysis from callee postconditions/proofs.
- Keep persisted summaries restricted to `Must` and `NotMay`.

This is the next place to start if the goal is a full paper-level
implementation. Without this, the active tree is still only an intraprocedural
paper skeleton.

## 2. Create And Reuse Summaries As A Full Lifecycle

Current state:

- Summary data structures exist.
- Applicability checks exist.
- The active driver does not yet learn summaries from completed analyses.

Needed:

- Create `Must` summaries when a target is shown reachable.
- Create `NotMay` summaries when a target is shown unreachable over the
  supported fragment.
- Store summaries in a way that stays target-specific.
- Reuse stored summaries across repeated procedure queries.
- Keep persisted summaries restricted to `Must` and `NotMay`.

## 3. Add Explicit Target Selection And Query Resolution

Current state:

- `src/main.rs` builds a single-target query from the first embedded
  `may_assert(...)`.
- The postcondition is now the target assertion's violation predicate:

```text
assert_violation(site) && !assert_arg
```

- Only the selected target site is treated as an assertion violation during
  transition; other `may_assert(...)` calls remain ordinary call effects.
- The smoke test now covers direct bug and direct safe cases.

Needed:

- Select the target assertion explicitly instead of taking the first one.
- Decide how multiple assertion sites should be surfaced at the CLI/query level.
- Translate command-line target choices into one resolved edge id.
- Keep summaries target-specific.

## 4. Strengthen The Predicate And Transition Oracles

Current state:

- `src/analysis/oracle.rs` provides abstract oracle traits.
- `SyntacticOracle` is the current predicate oracle.
- `src/analysis/transfer.rs` provides a metadata-backed `LlvmTransitionOracle`
  with syntactic guard/effect predicates.
- `src/analysis/analysis_flowq.md` now documents that `TransitionOracle`
  should answer the paper's transition queries, not own the driver or summary
  logic.

Needed:

- Add an analysis-level SMT encoding module under `src/analysis`.
- Decide whether one combined `SmtOracle` should implement both
  `PredicateOracle` and `TransitionOracle`, or whether encoding and oracle
  wrappers should be split across files.
- Add an SMT-backed `PredicateOracle`.
- Improve `LlvmTransitionOracle` so it computes more faithful approximations of:

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
- The archived memory notes live in:

```text
obsolete/src/analysis/memory_updates.md
```

Needed:

- Decide what memory term belongs in active query/state vocabulary.
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
22 passed
```
