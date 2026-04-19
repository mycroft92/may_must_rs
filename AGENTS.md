# AGENTS.md

This file is the first stop for future coding-agent sessions in this
repository. Read it before changing code.

## Session Startup

At the start of a new session, read these files in order:

1. `README.md`
2. `TODO.md`
3. `TASKVIEW.md`
4. `AGENTS.md`
5. `src/analysis/analysis_flow.md`
6. `src/analysis/summary_store_design.md`
7. `src/analysis2/design.md`

Then inspect the relevant Rust modules before editing. For paper-shaped rule
work, start with:

```text
src/analysis2/rules.rs
src/analysis2/state.rs
src/analysis2/cfg.rs
src/analysis2/oracle.rs
src/analysis2/llvm_adapter.rs
src/analysis2/transfer.rs
src/analysis2/summaries.rs
src/analysis2/driver.rs
src/analysis2/formula.rs
```

For the existing SMT-analysis work, start with:

```text
src/analysis/may_must_rules.rs
src/analysis/summary_store.rs
src/analysis/smt_engine.rs
src/analysis/transfer.rs
src/analysis/smt_path.rs
src/analysis/predicates.rs
src/analysis/state.rs
src/smt/solver.rs
```

The default CLI still uses:

```text
src/analysis/may_must.rs
```

Treat `may_must.rs` as the working toy/reference implementation. The
experimental SMT path is selected with `--engine smt` and currently covers
direct embedded `may_assert` queries only.

`src/analysis2` is scaffold-only and intentionally independent from
`src/analysis`. Use it when the task is to map the paper rules one-to-one.
Do not import `crate::analysis` from `analysis2`.

## Current Architecture

The intended module boundaries are:

```text
paper proof rules        -> src/analysis/may_must_rules.rs
summary storage/search   -> src/analysis/summary_store.rs
query orchestration      -> src/analysis/smt_engine.rs
LLVM instruction meaning -> src/analysis/transfer.rs
path state               -> src/analysis/smt_path.rs
formula vocabulary       -> src/analysis/predicates.rs
SMT symbol encoding      -> src/analysis/state.rs
raw Z3 operations        -> src/smt/solver.rs
default toy analyzer     -> src/analysis/may_must.rs
```

Do not blur these boundaries without a concrete reason.

The paper-shaped `analysis2` boundaries are:

```text
named SMASH rules      -> src/analysis2/rules.rs
Pi_n / Omega_n / Ne    -> src/analysis2/state.rs
P / n / e / Gamma_e    -> src/analysis2/cfg.rs
predicate vocabulary   -> src/analysis2/formula.rs
set/transition queries -> src/analysis2/oracle.rs
LLVM bridge            -> src/analysis2/llvm_adapter.rs
edge transfer model    -> src/analysis2/transfer.rs
procedure summaries    -> src/analysis2/summaries.rs
summary orchestration  -> src/analysis2/driver.rs
```

Keep the core paper modules (`cfg`, `formula`, `state`, `rules`, `summaries`,
`driver`, `oracle`) free of LLVM and Z3 details. LLVM specifics should stay in
`llvm_adapter.rs` and `transfer.rs`.

## Flow Rules

The SMT-backed analysis should follow this high-level flow:

```text
analyze_query(graph, query)
  1. ask SummaryStore for an applicable Must summary
  2. ask SummaryStore for an applicable NotMay summary
  3. if neither applies, execute the function body
  4. if a feasible target is found, create a Must summary
  5. if all supported paths finish without target, create a NotMay summary
  6. if unsupported/undecidable, return Unknown
```

Summary lookup should read as paper-rule application:

```text
SummaryStore::find_applicable_must
  -> may_must_rules::applicable_must_summary
      -> must_pre
      -> must_post

SummaryStore::find_applicable_not_may
  -> may_must_rules::applicable_not_may_summary
      -> not_may_pre
      -> not_may_post
```

Current named obligations:

```text
MustPre:    summary.pre entails query.pre
MustPost:   summary.post intersects query.post

NotMayPre:  query.pre entails summary.pre
NotMayPost: query.post entails summary.post
```

These directions mirror the current implementation and remain marked for review
against the SMASH paper before relying on the SMT path as the default engine.

## Rule Placement

For the paper-shaped track, prefer `src/analysis2/rules.rs`. Its rule names
should correspond directly to the SMASH paper, for example:

```text
MUST-POST                  -> must_post_edge
NOTMAY-PRE                 -> not_may_pre_edge
MUST-POST-USE-SUMMARY      -> must_post_use_summary
NOTMAY-PRE-USE-SUMMARY     -> not_may_pre_use_summary
```

In that tree:

```text
Gamma_e  -> PaperEdge::gamma
Omega_n  -> PaperAnalysisState::omega(node)
Pi_n     -> PaperAnalysisState::partition(node)
theta    -> RuleConclusion::AddOmega
beta     -> RuleConclusion::RefineAndAddMayEdge
```

The older `src/analysis/may_must_rules.rs` is currently a summary-applicability
facade for the SMT experiment, not the full intraprocedural paper rule layer.

`may_must_rules.rs` should contain named paper proof obligations only.

It may:

- call `Formula::entails_in`;
- call `Formula::intersects_in`;
- inspect `FunctionSummary`, `SmtQuery`, `SummaryKind`, and `SummaryTarget`;
- return structured rule-check results.

It must not:

- run a CFG worklist;
- inspect LLVM instructions directly;
- own raw Z3 solver operations;
- store summaries;
- create summaries;
- implement LLVM transfer semantics.

`summary_store.rs` should search cached summaries and delegate rule decisions
to `may_must_rules.rs`.

`smt_engine.rs` should decide when to apply summaries, execute functions, and
record new `Must`/`NotMay` summaries.

`transfer.rs` should only model LLVM instruction semantics over `SmtPathState`.

## Summary Policy

Persist only:

```text
Must   : there exists a witness path
NotMay : no supported path reaches the queried target
```

Do not add persistent May summaries. May analysis is an internal process that
can eventually produce a NotMay proof. A saved May fact is too weak to answer
the top-level query.

Summaries should use function-boundary vocabulary:

```text
SummaryPhase::Pre
SummaryPhase::Post
Pre.param_i
Post.ret
Pre.mem
Post.mem
```

Do not persist summaries in terms of local temporary SSA names unless that is
explicitly part of a short-lived construction step.

## Transfer Policy

Use one forward transfer layer:

```text
state_before_instruction -> state_after_instruction
```

Do not create separate pre-transfer and post-transfer implementations.
`SummaryPhase::Pre` and `SummaryPhase::Post` are function-boundary concepts,
not per-instruction transfer modes.

Current SMT transfer subset:

```text
alloca/store/load as a simple stack-memory map
add
sub
mul
icmp
unconditional br
conditional br with SMT pruning
scalar ret
```

Unsupported instructions should produce `UNKNOWN`, not an unsound safe result.

Memory caveat: the executable SMT path deliberately uses a temporary
`HashMap<pointer-key, IntTerm>` in `SmtPathState`. `StateEncoding` has
versioned SMT-array memory helpers, but the worklist does not use them yet.
Do not treat the current `alloca`/`store`/`load` support as alias-aware or
summary-ready memory semantics.

## Assertion Policy

Embedded assertions should be normalized conceptually as:

```text
target = AssertionViolation(assert_id)
violation condition = !assert_arg
```

For an assertion query, the SMT engine should check:

```text
path_condition & !assert_arg & query.post
```

Outcomes:

```text
SAT      -> record Must
UNSAT    -> continue this path
UNKNOWN  -> return Unknown
```

Assertion-target handling belongs in `smt_engine.rs`, not in `transfer.rs`.

## Documentation Guidelines

Keep documentation current as the architecture changes.

Use these destinations:

```text
README.md
  User-facing project status, how to run, current capabilities, and limitations.

TODO.md
  Backlog and implementation checklist. Mark what exists versus what remains.

TASKVIEW.md
  Resume document for the next session. Keep it concrete and ordered.

src/analysis/analysis_flow.md
  Paper-to-code mapping and top-level analysis flow.

src/analysis/summary_store_design.md
  Query/summary/store design details and applicability caveats.

src/analysis2/design.md
  Paper-shaped scaffold map for Pi, Omega, Gamma_e, summaries, and rule names.

AGENTS.md
  Agent/session instructions and stable engineering guardrails.
```

When adding a new analysis concept:

1. Put the implementation in the narrowest correct module.
2. Add focused unit tests.
3. Update `TODO.md` if it changes the backlog.
4. Update `TASKVIEW.md` if it changes the next-session plan.
5. Update `analysis_flow.md` or `summary_store_design.md` if it changes the
   paper-to-code mapping.
6. Update `README.md` only when user-facing behavior, architecture status, or
   run instructions change.

Do not overclaim. Clearly distinguish:

```text
implemented and CLI-active
implemented but scaffold-only
planned
unsupported and returns Unknown
```

## Verification Commands

Run after code changes:

```sh
cargo fmt
cargo test
```

Run when touching CLI behavior, graph construction, LLVM wrapping, tests, or
smoke-test assumptions:

```sh
make -C tests smoke
```

Use offline cargo only when needed:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

## Guardrails

- Keep `src/analysis/may_must.rs` stable until the SMT engine has independent
  regression coverage.
- Prefer `UNKNOWN` over unsound `SAFE`.
- Keep generated `.ll`, `.bc`, and DOT files out of source control.
- Keep C test inputs in `tests/`; generated artifacts belong in `tests/out/`.
- Add abstractions only when they make the paper-to-code mapping clearer or
  remove real duplication.
- Keep implementation close to the SMASH paper, but only fill gaps required by
  the current milestone.
