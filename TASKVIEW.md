# Tomorrow Task View: Active Paper Driver

This is the resume point for the next session.

## Current Working Baseline

- `src/analysis` is now the active analysis tree.
- The old toy analyzer and experimental SMT path were moved to:

```text
obsolete/src/analysis
obsolete/src/analysis.rs
```

- The CLI now runs the paper-shaped interprocedural driver:

```sh
cargo run --bin main -- <bitcode.bc>
```

- `--assert` is not implemented in the active driver.
- The active query builder currently uses the first embedded `may_assert(...)`
  as the single target assertion and encodes its violation as:

```text
assert_violation(site) && !assert_arg
```

- Only that selected target site is treated as a violation target; other
  `may_assert(...)` calls stay as ordinary call effects.
- MayCall boundary projection now strips edge-local atoms (`... @eK`) so call
  summaries are not polluted with caller-edge SSA effects.
- When a projected call postcondition is vacuous, the active fallback now uses
  a return-boundary predicate of the shape:

```text
retval_<callee> < 0
```

  (current heuristic; not the final semantic projection design).
- For Figure-1 style non-negative-return callees, the current provider also
  synthesizes a direct not-may summary:

```text
true => (NotMay) retval_<callee> < 0
```

  (shape-based heuristic; this is not yet a general semantic proof engine).
- Initial memory modeling is now started in the SMT predicate oracle:
  memory atoms are interpreted with integer-array `select/store`.
- Explicit target selection is not implemented yet.
- Current test status:

```sh
cargo test
# 34 passed

make -C tests smoke
# passes
```

## What The Active Tree Contains

The active paper-shaped modules are:

```text
src/analysis/vocabulary.rs   -> procedure, node, edge, and region IDs
src/analysis/formula.rs      -> solver-independent predicates
src/analysis/oracle.rs       -> PredicateOracle / TransitionOracle traits + SMT predicate oracle
src/analysis/llvm_adapter.rs -> FunctionGraph -> (PaperProcedure, metadata)
src/analysis/cfg.rs          -> PaperProcedure, PaperEdge, Gamma_e
src/analysis/state.rs        -> Pi_n, Omega_n, regions, may edges
src/analysis/summaries.rs    -> ReachabilityQuery, ProcedureSummary, SummaryTable
src/analysis/transfer.rs     -> LlvmTransitionOracle, SmtLlvmTransitionOracle, LlvmEdgeTransfer
src/analysis/rules.rs        -> named paper rules
src/analysis/driver.rs       -> interprocedural orchestration + local worklist
src/analysis/design.md       -> paper-to-code map
```

The current driver already has:

```text
answer_from_summaries
run_intraprocedural
run_interprocedural
MayCall recursion + summary creation
call-edge summary reuse inside local worklists
```

The worklist unit is:

```text
(edge, source region, destination region)
```

Current rule use inside the worklist:

```text
MUST-POST   -> grows Omega_n
NOTMAY-PRE  -> splits Pi_n and records may edges
```

## What Is Archived

The following are archived only and should not be treated as active behavior:

```text
obsolete/src/analysis/may_must.rs
obsolete/src/analysis/summary_store.rs
obsolete/src/analysis/may_must_rules.rs
obsolete/src/analysis/predicates.rs
obsolete/src/analysis/smt_path.rs
obsolete/src/analysis/analysis_flow.md
obsolete/src/analysis/summary_store_design.md
obsolete/src/analysis/memory_updates.md
```

Use them for reference only when porting ideas into the active tree.

## Immediate Next Work

1. Tighten interprocedural behavior toward paper parity.
   - Formalize the alternation schedule beyond the current pragmatic
     summary/apply/recurse loop.
   - Improve recursion handling beyond depth/stack cutoffs.
   - Keep unresolved internal calls mapped to `UNKNOWN`, never unsound
     `NOT REACHED`.

2. Keep target selection honest while doing interprocedural work.
   - Current stopgap: first embedded `may_assert(...)`.
   - Next real step: resolve one explicit target assertion from the CLI/query.

3. Strengthen the active oracle path.
   - Keep improving `SmtPredicateOracle` and `SmtLlvmTransitionOracle`.
   - Move from Boolean-atom encoding toward structured scalar/memory terms.
   - Strengthen transition image reasoning beyond current guard/effect
     conjunctions.
   - Make `theta subset Post(Gamma_e, source)` and
     `Pre(Gamma_e, target) subset beta` more faithful.
   - Keep LLVM metadata extraction in `llvm_adapter.rs`; do not put solver
     setup there.

4. Replace the current call-post fallback heuristic with semantic return
   projection.
   - Current stopgap for vacuous projected postconditions:

```text
retval_<callee> < 0
```

   - Next step: derive call-post predicates from real caller demand and callee
     return semantics (including `<`, `<=`, `>`, `>=`, and equality constraints).
   - Keep summary predicates in procedure-boundary vocabulary, not caller-edge
     SSA atoms.
   - Retire the current shape-based direct not-may synthesis once transition
     semantics can prove the same obligations.

5. Clarify memory in paper terms.
   - Decide what memory object should live in the active state/query language.
   - Extend the initial integer-array encoding into transition/query/summaries
     with stable memory-version naming.
   - Port only the useful ideas from `obsolete/src/analysis/memory_updates.md`.
   - Keep the active tree paper-readable while doing it.

6. Expand LLVM coverage when needed by the active driver.
   - calls with summaries
   - `phi`
   - `switch`
   - `getelementptr`
   - casts/conversions
   - richer return/query handling

## Commands To Re-Establish Context

Run unit tests:

```sh
cargo test
```

Generate bitcode and readable LLVM IR:

```sh
make -C tests ir
```

Run the active smoke test:

```sh
make -C tests smoke
```

Run the current driver directly:

```sh
cargo run --bin main -- tests/out/smash_must.bc
```

## Files To Start With Tomorrow

- `src/analysis/analysis_flow.md`
- `src/analysis/design.md`
- `src/analysis/driver.rs`
- `src/analysis/rules.rs`
- `src/analysis/state.rs`
- `src/analysis/cfg.rs`
- `src/analysis/oracle.rs`
- `src/analysis/llvm_adapter.rs`
- `src/analysis/transfer.rs`
- `src/analysis/summaries.rs`
- `src/main.rs`

Use the archived tree only when you need old implementation ideas:

- `obsolete/src/analysis/analysis_flow.md`
- `obsolete/src/analysis/summary_store_design.md`
- `obsolete/src/analysis/memory_updates.md`

## First Concrete Commit Next Session

1. Add one end-to-end multi-call smoke case (`main -> f -> g`) that exercises:
   call projection, summary creation, and summary reuse in one run.
2. Add an explicit regression for unresolved internal calls returning `UNKNOWN`.
3. Strengthen projection logic so argument/global matching is symbol-aware, not
   substring-based.
4. Keep `cargo test` and `make -C tests smoke` green.
