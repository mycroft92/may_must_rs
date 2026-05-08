# AGENTS.md

Read this file before changing code in this repository.

We are still pursuing the same paper-level goal: given an assertion and a
program, either show that the assertion site is unreachable or show that the
assertion condition always holds on reachable executions. The implementation
shape changed, so do not assume the older `cfg/state/loops/transfer`
paper-tree is still the active code path.

Paper reference:

https://dl.acm.org/doi/10.1145/1707801.1706307

## Session Startup

At the start of a new session, read these files in order:

1. `README.md` (or `Readme.md` if that is the branch-local spelling)
2. `TODO.md`
3. `TASKVIEW.md`
4. `AGENTS.md`
5. `src/analysis/design.md`
6. `src/analysis/analysis_flow.md`

Then inspect the relevant Rust modules before editing.

If the session goal is to reconstruct or audit the milestone from scratch,
also read `Reproducer.md`.

For active analysis work, start with:

```text
src/analysis/abstract_cfg.rs
src/analysis/adapter.rs
src/analysis/backward.rs
src/analysis/driver.rs
src/analysis/formula.rs
src/analysis/node_summary.rs
src/analysis/oracle.rs
src/analysis/providers.rs
src/analysis/rules.rs
src/analysis/source.rs
src/analysis/summaries.rs
src/llvm_utils/program_graph.rs
```

## Active Architecture

The active implementation is the current `src/analysis` tree:

```text
raw LLVM wrapper/query boundary          -> src/llvm_utils/llvm_wrap.rs
raw LLVM instruction graph               -> src/llvm_utils/program_graph.rs
assertion text translation               -> src/assertions/translation.rs
formula / term vocabulary                -> src/analysis/formula.rs
abstract CFG + transfer semantics        -> src/analysis/abstract_cfg.rs
LLVM graph -> abstract CFG lowering      -> src/analysis/adapter.rs
per-node reach/state summaries           -> src/analysis/node_summary.rs
local backward propagation rules         -> src/analysis/rules.rs
acyclic assertion checking               -> src/analysis/backward.rs
SMT feasibility / implication queries    -> src/analysis/oracle.rs
summary/provider seam                    -> src/analysis/providers.rs
summary table data structures            -> src/analysis/summaries.rs
module orchestration + summary reuse     -> src/analysis/driver.rs
source location value type               -> src/analysis/source.rs
raw Z3 lowering                          -> src/smt/solver.rs
```

Keep LLVM-specific querying in `llvm_utils`. Keep raw solver details in
`smt/solver.rs`. Keep solver policy in `analysis/oracle.rs`.

`adapter.rs` is the lowering boundary from `FunctionGraph` to the active
semantic model. `abstract_cfg.rs` owns the CFG and transfer semantics used by
the checker. `backward.rs` and `rules.rs` should stay focused on analysis
logic, not LLVM parsing.

## Current Behavioral Boundaries

Implemented and CLI-active:

- integer and boolean reasoning
- integer-array memory slice for `alloca` / `load` / `store` / `gep`
- `phi` lowering on incoming edges
- branch-guard lowering on edges
- direct-call return-summary inference/reuse
- acyclic backward checking
- multi-exit normalization
- best-effort unsupported reporting in the CLI

Implemented but not wired:

- assertion text translation
- manual/external summary providers
- source-coordinate reporting from LLVM debug info

Unsupported and should remain honest:

- loops / cyclic CFGs
- floating-point lowering
- loop invariants and loop summaries
- broader cast/instruction coverage beyond the current subset

Prefer `UNKNOWN` over an unsound proof claim.

## Development Direction

- Treat the current abstract-CFG pipeline as the active baseline.
- Do not document or extend removed architecture as if it were still live.
- When broadening support, keep the semantic layers aligned:
  `formula.rs`, `abstract_cfg.rs`, `adapter.rs`, `oracle.rs`, and
  `smt/solver.rs` should evolve together.
- For loops, decide the sound strategy before coding. Right now the checker is
  intentionally acyclic only.

Important organization rule:

- when a new concept is logically independent, split it into a new focused
  module instead of flattening more code into an existing file
- only keep code together when the coupling is real and separation would be
  artificial

When adding a new active analysis concept:

1. Put the implementation in the narrowest correct module.
2. Add focused unit tests.
3. Add a short module-level doc comment when the module intent changes.
4. Update `TODO.md` if the backlog changes.
5. Update `TASKVIEW.md` if the next-session plan changes.
6. Update `src/analysis/design.md` if the architecture mapping changes.
7. Update `README.md` when CLI behavior or support boundaries change.
8. If the task is complete and the user did not say otherwise, commit and push
   the branch after verification.

## Verification Commands

Run after code changes:

```sh
cargo fmt
cargo test
```

Run when touching CLI behavior, LLVM graph construction, lowering, or smoke
assumptions:

```sh
make -C tests smoke
```

If the smoke harness is unavailable on the branch, say so clearly and fall
back to the available Rust verification commands.

## Guardrails

- Prefer `UNKNOWN` over unsound success claims.
- Mark heavy approximations with `APPROX_HEAVY:` comments.
- Do not read `obsolete/`.
- Keep generated `.ll`, `.bc`, and DOT files out of source control.
- Keep C test inputs in `tests/`; generated artifacts belong in `tests/out/`.
