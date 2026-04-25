
# AGENTS.md

This file is the first stop for future coding-agent sessions in this
repository. Read it before changing code. We are implementing the following paper on LLVM IR programs:

https://dl.acm.org/doi/10.1145/1707801.1706307

## Session Startup

At the start of a new session, read these files in order (create an initial version if not present):

1. `README.md` (or `Readme.md` if that is the current file in the branch)
2. `TODO.md`
3. `TASKVIEW.md`
4. `AGENTS.md`
5. `src/analysis/design.md`
6. `src/analysis/analysis_flow.md`

Then inspect the relevant Rust modules before editing.

If the session goal is to reconstruct or audit the implemented milestone from
scratch, also read `Reproducer.md`.

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
## Idea
We are try to prove or counter with evidence that: given an assertion and a program, either the assertion is unreachable (vacuous true) or is reachable and always `true` under reachable conditions. We perform both forward and backward analyses of the LLVM IR program.


## Architecture

The active implementation is the paper-shaped tree in `src/analysis`.

The intended module boundaries are:

```text
raw LLVM program graph                  -> src/llvm_utils/program_graph.rs
assertion frontend lowering             -> src/assertions/translation.rs
named SMASH rules                       -> src/analysis/rules.rs
Pi_n / Omega_n / N_e and path summaries -> src/analysis/state.rs
P / n / e / Gamma_e                     -> src/analysis/cfg.rs
predicate vocabulary                    -> src/analysis/formula.rs
set/sat/evidence queries                -> src/analysis/oracle.rs
LLVM decoding and lowering              -> src/analysis/llvm_adapter.rs
normalized step relations               -> src/analysis/transfer.rs
procedure summaries                     -> src/analysis/summaries.rs
summary orchestration                   -> src/analysis/driver.rs
```

Keep the core paper modules (`cfg`, `formula`, `state`, `rules`, `summaries`,
`driver`, `oracle`) free of LLVM and Z3 details. LLVM specifics should stay in
`llvm_utils` and `llvm_adapter.rs`. `transfer.rs` should consume a normalized
effect/instruction layer produced by `llvm_adapter.rs`, not raw
`llvm_wrap::Instruction` handles.

`llvm_adapter.rs` should lower one procedure into the paper `cfg` plus
pre-normalized `node_effects` and `edge_effects` for `transfer.rs`.

Track path predicates in `state.rs`, not in `cfg.rs`. `cfg.rs` should only
store edge-local relations/guards (`Gamma_e`). The accumulated path summary for
the current analysis frontier belongs in `state.rs`.

Lower ordinary branch conditions into `cfg.rs` edge relations, not into the
normalized transfer-effect stream. Lower `phi` nodes as predecessor-specific
normalized assignments on incoming edges. Reserve `Assume`-style transfer
effects for extra trusted refinements such as user-supplied contracts.

`oracle.rs` is the only place that should answer satisfiability, implication,
or evidence/model queries against the SMT solver. Other modules may build
formulas but should not own solver policy.

Before loop invariants exist, use a `max_step` engine as the temporary loop
policy:

- `state.rs` should be able to carry the visit-count or bounded-progress facts
  needed by that engine.
- `driver.rs` should enforce the revisit bound and decide when exploration
  stops because the temporary loop budget is exhausted.
- `transfer.rs` should stay local to one normalized step; it should not own the
  global loop bound policy.

When we replace bounded loop handling with loop invariants:

- `llvm_adapter.rs` should identify the relevant loop structure in the lowered
  CFG, such as headers, latches, backedges, or SCC-based loop regions.
- `transfer.rs` should encode one-iteration semantic steps, not invent
  invariants.
- `state.rs` should store candidate/header facts and the accumulated path
  summaries those candidates summarize.
- `oracle.rs` should check initiation, inductiveness, and evidence queries for
  invariant candidates.
- `summaries.rs` should be the home of loop invariant extraction/refinement and
  reusable loop summaries.
- `driver.rs` should orchestrate when invariant generation/checking runs and
  when a loop summary is accepted into the analysis.

The program graph generation is written in `llvm_utils` directory.
If an LLVM/function graph has multiple exits, lower it to a single paper exit
by creating one synthetic exit node and adding trivial (`true`) edges from each
real exit to that synthetic exit.

Do not generate summaries for `may_assert` call edges. If possible do not even generate the call edges for it, instead we generate the assertion `true =>(not-May) PathCondition /\  !(assert_expression)`.

## Development idea
- We first develop this for straightline programs, then for programs with single procedures, then finally when function calls are present. 
- To deal with loops, first implement a `max_step` engine where we wont revisit an instruction/edge for more than that number. Only after that is stable should we replace it with loop summary generation / loop invariant extraction in `summaries.rs`, checked through `oracle.rs`, and orchestrated by `driver.rs`.
- Clearly notate in TASKVIEW which phase of the development we are in.
- Add examples from the paper as targets for each of these goals. 
- Do not add fallback summary generations ever. Instead let the analysis discover them automatically as the development progresses.

Current reproduced branch milestone is earlier than the later driver/summaries
plan above:

- CLI-active code stops at LLVM graph generation and DOT dumping.
- `src/analysis/formula.rs`, `state.rs`, `cfg.rs`, `transfer.rs`, and
  `llvm_adapter.rs` are implemented but not wired into a forward/backward
  driver yet.
- `transfer.rs` currently uses one normalized
  `TransferEffect::Assign { target, value }` effect plus `Assume`,
  `Obligation`, `Call`, and `Nop`.
- the curated fixture corpus lives under `tests/flow/`.
- `make -C tests smoke` currently compiles that corpus and runs the graph CLI
  over the resulting bitcode files.


When adding a new active analysis concept:

1. Put the implementation in the narrowest correct module.
2. Add focused unit tests.
3. Add a short module-level doc comment that states the module intention and the paper notation or definition it implements.
4. Update `TODO.md` if it changes the backlog.
5. Update `TASKVIEW.md` if it changes the next-session plan.
6. Update `src/analysis/design.md` if it changes the paper-to-code mapping.
7. Update `README.md` or `Readme.md` when user-facing behavior or run instructions change.
8. If the task is complete and the user did not say otherwise, commit and push the branch after verification.

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

If the current branch does not yet contain the smoke harness, state that
clearly and fall back to the available Rust verification commands.

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
