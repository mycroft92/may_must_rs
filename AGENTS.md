# AGENTS.md

This file is the first stop for future coding-agent sessions in this
repository. Read it before changing code.

## Session Startup

At the start of a new session, read these files in order:

1. `README.md`
2. `TODO.md`
3. `TASKVIEW.md`
4. `AGENTS.md`
5. `src/analysis/design.md`
6. `src/analysis/analysis_flowq.md`

If the task touches the archived implementation, also read:

1. `obsolete/src/analysis/analysis_flow.md`
2. `obsolete/src/analysis/summary_store_design.md`
3. `obsolete/src/analysis/memory_updates.md`

Then inspect the relevant Rust modules before editing.

For active paper-shaped work, start with:

```text
src/analysis/rules.rs
src/analysis/state.rs
src/analysis/cfg.rs
src/analysis/oracle.rs
src/analysis/llvm_adapter.rs
src/analysis/transfer.rs
src/analysis/summaries.rs
src/analysis/driver.rs
src/analysis/formula.rs
```

For archived-reference work only, start with:

```text
obsolete/src/analysis/analysis_flow.md
obsolete/src/analysis/summary_store_design.md
obsolete/src/analysis/memory_updates.md
obsolete/src/analysis/
src/smt/solver.rs
```

## Current Architecture

The active implementation is the paper-shaped tree in `src/analysis`.

The intended module boundaries are:

```text
named SMASH rules      -> src/analysis/rules.rs
Pi_n / Omega_n / N_e   -> src/analysis/state.rs
P / n / e / Gamma_e    -> src/analysis/cfg.rs
predicate vocabulary   -> src/analysis/formula.rs
set/transition queries -> src/analysis/oracle.rs
LLVM bridge            -> src/analysis/llvm_adapter.rs
edge transfer model    -> src/analysis/transfer.rs
procedure summaries    -> src/analysis/summaries.rs
summary orchestration  -> src/analysis/driver.rs
```

Keep the core paper modules (`cfg`, `formula`, `state`, `rules`, `summaries`,
`driver`, `oracle`) free of LLVM and Z3 details. LLVM specifics should stay in
`llvm_adapter.rs` and `transfer.rs`.

The archived implementation now lives under:

```text
obsolete/src/analysis
```

Do not move archived concepts back into `src/analysis` unless there is a
deliberate migration step.

## Current CLI

`src/main.rs` now drives the paper-shaped tree directly:

```text
LLVM bitcode
  -> llvm_utils::program_graph::generate_program_graph
  -> analysis::llvm_adapter::adapt_function_graph
  -> analysis::driver::PaperDriver::run_intraprocedural
```

Current default query policy:

```text
one target assertion per query
current CLI policy = first embedded may_assert(...)
post = assert_violation(site) && !assert_arg
```

Only the selected target site is turned into `assert_violation(site)`;
non-target `may_assert(...)` calls stay as ordinary call effects.

`--assert` is not implemented in the active driver.

## Flow Rules

The active intraprocedural flow is:

```text
run_intraprocedural(procedure, query)
  1. initialize Pi_n and Omega_n from the query
  2. enqueue (edge, source region, destination region) obligations
  3. apply MUST-POST to grow Omega_n
  4. apply NOTMAY-PRE to split Pi_n and record may edges
  5. requeue obligations affected by Omega growth or partition refinement
  6. stop at REACHABLE, obligation limit, or worklist exhaustion
```

Current initialization:

```text
Omega_entry = query.pre
Pi_exit     = { query.post, !query.post }
other Pi_n  = { true }
```

Current requeue policy:

```text
Omega growth at node n -> enqueue outgoing obligations from n
Pi split at node n     -> enqueue incoming and outgoing obligations touching n
```

## Rule Placement

Rule names in `src/analysis/rules.rs` should match the paper directly:

```text
MUST-POST                  -> must_post_edge
NOTMAY-PRE                 -> not_may_pre_edge
MUST-POST-USE-SUMMARY      -> must_post_use_summary
NOTMAY-PRE-USE-SUMMARY     -> not_may_pre_use_summary
```

In the active tree:

```text
Gamma_e  -> PaperEdge::gamma
Omega_n  -> PaperAnalysisState::omega(node)
Pi_n     -> PaperAnalysisState::partition(node)
theta    -> RuleConclusion::AddOmega
beta     -> RuleConclusion::RefineAndAddMayEdge
```

`rules.rs` may:

- inspect `PaperEdge`, `ProcedureSummary`, and `ReachabilityQuery`;
- call `PredicateOracle` and `TransitionOracle`;
- return structured rule applications and conclusions.

`rules.rs` must not:

- inspect raw LLVM instruction wrappers directly;
- own Z3 solver operations;
- run the CFG worklist;
- store summaries;
- implement LLVM transfer semantics.

## Summary Policy

Persist only:

```text
Must   : there exists a witness path
NotMay : no supported path reaches the queried target
```

Do not add persistent May summaries.

The active `SummaryTable` is part of the paper tree, but summary use is not
yet wired into call-edge execution. Keep summary types aligned with the paper
even before that integration exists.

## Transfer Policy

The active transfer boundary is:

```text
TransitionOracle
  backed by
LlvmTransitionOracle
```

Keep the design split:

```text
LLVM IR / FunctionGraph      -> llvm_adapter.rs
EdgeId -> LlvmEdgeMetadata   -> llvm_adapter.rs
metadata -> guard/effect     -> transfer.rs
paper rules consume Post/Pre -> rules.rs
```

Do not collapse this boundary by making `rules.rs` parse LLVM instructions.

## Documentation Guidelines

Keep documentation current as the architecture changes.

Use these destinations:

```text
README.md
  User-facing project status, how to run, current capabilities, and limits.

TODO.md
  Backlog and implementation checklist. Mark what exists versus what remains.

TASKVIEW.md
  Resume document for the next session. Keep it concrete and ordered.

src/analysis/design.md
  Paper-to-code map for Pi, Omega, Gamma_e, summaries, and rule names.

src/analysis/analysis_flowq.md
  Flow-oriented paper mapping, module correspondence, and SMT layering notes.

AGENTS.md
  Agent/session instructions and stable engineering guardrails.
```

Archived notes stay under `obsolete/src/analysis`.

When adding a new active analysis concept:

1. Put the implementation in the narrowest correct module.
2. Add focused unit tests.
3. Update `TODO.md` if it changes the backlog.
4. Update `TASKVIEW.md` if it changes the next-session plan.
5. Update `src/analysis/design.md` if it changes the paper-to-code mapping.
6. Update `README.md` when user-facing behavior or run instructions change.

Do not overclaim. Clearly distinguish:

```text
implemented and CLI-active
implemented but not wired
archived reference code
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
smoke assumptions:

```sh
make -C tests smoke
```

Use offline cargo only when needed:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

## Guardrails

- Prefer `UNKNOWN` over unsound success claims.
- Keep generated `.ll`, `.bc`, and DOT files out of source control.
- Keep C test inputs in `tests/`; generated artifacts belong in `tests/out/`.
- Keep the active implementation close to the paper and fill only the gaps the
  current milestone needs.
- Treat `obsolete/src/analysis` as reference material, not active code.
