# Tomorrow Task View: Active Paper Driver

This is the resume point for the next session.

## Completed This Session

1. Removed fallback summary synthesis heuristics.
   - Deleted provider-level synthetic summary hook from driver flow.
   - Summary creation now only comes from recursive MayCall results:
     `Must` when callee query is reachable, `NotMay` when completed and not
     reachable.

2. Enforced assertion-primitive call behavior.
   - `may_assert` calls are summary-exempt in the interprocedural driver.
   - They are handled by transition effects only; no call-summary projection,
     creation, or reuse for `may_assert`.

3. Reworked alpha-renaming/binding at call boundaries.
   - Formal/actual and retval/lhs are now substitutions, not added equality
     conjuncts.
   - Projected caller-shaped call queries normalize back to callee-boundary
     symbols before summary persistence checks.

4. Removed boundary sanitize pass.
   - The edge-local atom scrub pass was removed.
   - Current projection is shared-symbol based (still approximate).

5. Moved query transformation logic out of CLI wiring.
   - Added `src/analysis/call_projection.rs` with:
     - caller-to-callee query projection,
     - callsite renaming/substitution/havoc,
     - projected-query normalization for summaries.
   - `main.rs` now delegates call projection to this analysis module.

6. Centralized predicate symbol rewrite utilities.
   - Moved symbol substitution/symbol collection helpers into
     `src/analysis/formula.rs` as reusable analysis-level utilities.
   - Added comments explaining why these belong in analysis, not CLI.

7. Added/updated diagnostics and tests.
   - Driver logs summary-rule rejection reasons on call edges.
   - Driver logs unresolved internal-call context.
   - Added regression that `may_assert` does not participate in summary flow.
   - Moved call-projection tests into `analysis::call_projection`.

## Current Baseline

- Active architecture remains under `src/analysis`.
- New analysis module:

```text
src/analysis/call_projection.rs
```

- Current unit-test baseline:

```text
cargo test
# 40 passed
```

- Smoke baseline:

```text
make -C tests smoke
# passes
```

## Known Behavior: `paper_section2_fig1_not_may`

Running:

```sh
CRICK_LOG='main=debug,main::analysis::driver=debug' MAY_MUST_SKIP_DOT=1 \
cargo run --bin main -- tests/out/paper_section2_fig1_not_may.bc --max-steps 20000
```

still yields `UNKNOWN`.

Current observed chain:

- projected call query at `e10` now appears caller-shaped:
  `post=%11 < 0`;
- normalized query for summary storage becomes callee-boundary:
  `post=retval_g < 0`;
- a `Must` summary is created for `g`;
- summary reuse fails at later call obligations because summary precondition is
  not covered by current `Omega_n1`;
- unresolved internal call is marked, driving `UNKNOWN`.

## Immediate Next Work

1. Resolve summary-pre / `Omega_n1` mismatch for repeated call sites.
   - Investigate whether the stored `Must` summary pre should be generalized or
     projected differently at callee entry.
   - Add targeted tests for repeated same-callee calls with different caller
     SSA contexts.

2. Replace vacuous-post fallback with semantic return-demand projection.
   - Current fallback remains `retval_<callee> < 0`.
   - Next step: derive post from caller demand over return relation.

3. Implement explicit `--assert` selection in active driver.

4. Continue strengthening transition/image precision in SMT transfer/oracle.

## Files To Start With

- `src/analysis/call_projection.rs`
- `src/analysis/driver.rs`
- `src/analysis/formula.rs`
- `src/analysis/rules.rs`
- `src/main.rs`
- `src/analysis/design.md`
- `src/analysis/analysis_flow.md`

## Commands To Re-Establish Context

```sh
cargo fmt
cargo test
make -C tests smoke
```

Focused repro:

```sh
CRICK_LOG='main=debug,main::analysis::driver=debug' MAY_MUST_SKIP_DOT=1 \
cargo run --bin main -- tests/out/paper_section2_fig1_not_may.bc --max-steps 20000
```
