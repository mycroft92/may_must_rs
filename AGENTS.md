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
6. `src/analysis/analysis_flow.md`

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


## Current CLI

`src/main.rs` drives the paper-shaped tree directly:

```text
LLVM bitcode
  -> llvm_utils::program_graph::generate_program_graph
  -> analysis::llvm_adapter::adapt_function_graph
  -> analysis::oracle::SmtPredicateOracle
  -> analysis::transfer::SmtLlvmTransitionOracle
  -> analysis::driver::PaperDriver::run_interprocedural
```

Current default query policy:

```text
for each embedded may_assert(site):
  job 1 (site):      post = assert_violation(site)
  job 2 (violation): post = assert_violation(site) && !assert_arg
  verdict = unreachable | true when reached | violation reachable | unknown
```

During transition, the targeted site is interpreted in mode:

```text
SiteReachability -> assert_violation(site)
Violation        -> assert_violation(site) && !assert_arg
```

`--assert` is not implemented in the active driver.

## Flow Rules

The active flow is interprocedural with local intraprocedural worklists:

```text
run_interprocedural(query)
  1. try top-level summary applicability
  2. initialize local Pi_n and Omega_n from the query
  3. enqueue (edge, source region, destination region) obligations
  4. on internal call edge:
       try summary-use rules
       else project callee query (MayCall), recurse, and create Must/NotMay summary
       then retry summary-use rules
  5. on non-call or unresolved external edge:
       apply MUST-POST / NOTMAY-PRE
  6. requeue obligations affected by Omega growth or partition refinement
  7. stop at REACHABLE, UNKNOWN (limit/unresolved internal call), or exhaustion
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

The active `SummaryTable` is part of the paper tree, and summary use is wired
into call-edge execution inside the interprocedural driver.
Summary creation and reuse are active for `Must` and `NotMay`.
Keep summary types aligned with the paper while extending coverage.

## Transfer Policy

The active transfer boundary is:

```text
TransitionOracle
  backed by
SmtLlvmTransitionOracle (CLI default)
LlvmTransitionOracle    (syntactic/fallback)
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

src/analysis/analysis_flow.md
  Flow-oriented paper mapping, module correspondence, and SMT layering notes.

AGENTS.md
  Agent/session instructions and stable engineering guardrails.
```


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
- Annotate every deliberate approximation-heavy site with an
  `APPROX_HEAVY:` code comment so it is auditable and removable.
- Do not read `obsolete` folder at all 
- Keep generated `.ll`, `.bc`, and DOT files out of source control.
- Keep C test inputs in `tests/`; generated artifacts belong in `tests/out/`.
- Keep the active implementation close to the paper and fill only the gaps the
  current milestone needs.
