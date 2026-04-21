Experimental LLVM may/must analysis work. MIT Licensed.

## Current Status

The active implementation now lives in `src/analysis` and follows the paper's
vocabulary directly:

- `P`, `n`, `e`, and `Gamma_e`;
- `Pi_n`, `Omega_n`, and `N_e`;
- named rules such as `MUST-POST` and `NOTMAY-PRE`.

The older executable analyzers were not deleted. They were moved to:

```text
obsolete/src/analysis
obsolete/src/analysis.rs
```

That archived tree is reference material only. It is no longer compiled or
wired into the CLI.

## How To Run

Generate LLVM IR and bitcode from the C test inputs:

```sh
make -C tests ir
```

Run the active paper-shaped interprocedural driver on a bitcode file:

```sh
cargo run --bin main -- tests/out/smash_must.bc
```

Bound per-query obligation processing:

```sh
cargo run --bin main -- tests/out/smash_must.bc --max-steps 50000
```

Run the current smoke test:

```sh
make -C tests smoke
```

Run unit tests:

```sh
cargo test
```

If Cargo cannot access the network and the dependency cache is already present,
use:

```sh
CARGO_FLAGS=--offline make -C tests smoke
```

Every run writes DOT graphs to `graph_dot/<input-stem>/`.

## Current CLI Behavior

The binary adapts LLVM `FunctionGraph`s into paper-shaped procedures and then
runs the interprocedural driver in `src/analysis/driver.rs`.

For each embedded `may_assert(...)` site, the CLI now runs two checks:

```text
1) site reachability:      assert_violation(site)
2) violation reachability: assert_violation(site) && !assert_arg
```

The transition layer supports this with two target modes:

- `SiteReachability`: the targeted `may_assert` edge emits `assert_violation(site)`;
- `Violation`: the targeted `may_assert` edge emits
  `assert_violation(site) && !assert_arg`.

The CLI reports a per-site verdict:

- `ASSERTION UNREACHABLE`
- `ASSERTION TRUE WHEN REACHED`
- `ASSERTION VIOLATION REACHABLE`
- `UNKNOWN`

and returns one of:

- `REACHABLE`
- `NOT REACHED`
- `UNKNOWN`

followed by basic worklist statistics.

`--assert` is not implemented in the active paper driver yet.

## Active Architecture

The primary tree is:

```text
src/analysis/cfg.rs          -> PaperProcedure, PaperEdge, Gamma_e
src/analysis/formula.rs      -> Predicate vocabulary
src/analysis/state.rs        -> Pi_n, Omega_n, regions, may edges
src/analysis/rules.rs        -> named SMASH rules
src/analysis/oracle.rs       -> PredicateOracle, TransitionOracle
src/analysis/llvm_adapter.rs -> LLVM FunctionGraph -> paper procedure + metadata
src/analysis/call_projection.rs -> call-boundary query projection/renaming
src/analysis/transfer.rs     -> metadata-backed transition oracles
src/analysis/summaries.rs    -> reachability queries and summaries
src/analysis/driver.rs       -> interprocedural orchestration + local worklist
src/analysis/design.md       -> paper-to-code map
```

The intended split is:

```text
paper logic      -> cfg, formula, state, rules, summaries, driver, oracle
LLVM adaptation  -> llvm_adapter
edge semantics   -> transfer
raw solver layer -> src/smt/solver.rs
archived code    -> obsolete/src/analysis
```

The current driver shape is:

```text
FunctionGraph
  -> adapt_function_graph(...)
  -> ReachabilityQuery
  -> PaperDriver::run_interprocedural(...)
       summary applicability check
       MayCall recursion on internal call edges
       summary creation (Must / NotMay)
       local worklist over (edge, source region, destination region)
       MUST-POST and NOTMAY-PRE in each procedure
```

## What Is Implemented

- explicit paper-shaped CFG, state, summary, and rule modules;
- Option A LLVM adapter with external `EdgeId -> LlvmEdgeMetadata`;
- SMT-backed `PredicateOracle` over active `Predicate` formulas;
- initial SMT memory semantics in `SmtPredicateOracle` for
  `store/load`-shaped atoms using `Array[Int -> Int]`;
- SMT-backed LLVM transition oracle over transfer-derived guard/effect predicates;
- interprocedural driver (`run_interprocedural`) with:
  summary applicability, call-query projection, MayCall recursion, summary
  creation, and call-edge summary reuse via
  `MUST-POST-USE-SUMMARY` / `NOTMAY-PRE-USE-SUMMARY`;
- call-query projection/renaming now lives in `analysis::call_projection`;
- call-query instantiation now renames call-instance locals/retvals, applies
  formal/actual and retval/lhs substitutions, and havocs global/memory-shaped
  post symbols at the caller boundary;
- projected caller-shaped queries are normalized back to callee-boundary
  symbols before summary creation/reuse checks;
- projected call postconditions still use a return-boundary fallback target
  `retval_<callee> < 0` when projection becomes vacuous;
- fallback summary synthesis heuristics were removed; summaries are created only
  from recursive query results (`Must` / `NotMay`);
- per-procedure local worklist over `(edge, source region, destination region)`;
- CLI wiring to the active paper driver;
- unit tests for the paper-shaped modules;
- smoke coverage for direct bug and direct safe cases.

Current unit-test baseline:

```text
cargo test
40 passed
```

## What Is Not Yet Implemented

- full SMASH alternation strategy (current implementation uses a pragmatic
  summary/apply/recurse loop, not the full paper schedule);
- richer SMT transition/image semantics beyond current Boolean-atom encoding;
- full memory modeling in paper-state/query/summaries
  (current array semantics are atom-level and still lightweight);
- richer call-query projection semantics beyond the current boundary heuristic
  (symbol-membership projection + `retval_<callee> < 0` fallback);
- explicit CLI target-selection (`--assert`) in the active driver;
- command-line `--assert` queries in the paper driver;
- rich LLVM coverage (`phi`, `switch`, `getelementptr`, casts, calls with
  summaries, globals, heap, arrays, structs);
- richer witness/proof evidence for created summaries.

Recommended next milestone:

```text
strengthen SMT transition/predicate encodings and call projection precision
```

The repository should still not be described as a full SMASH implementation.
The current version is interprocedural and summary-aware, but still
approximation-heavy.

## Archived Implementation

The previous development line is preserved under `obsolete/src/analysis`. That
tree still contains the old toy analyzer, the old SMT-oriented path, and the
older analysis notes.

It is intentionally left intact for reference, but it is not part of the
active build.
