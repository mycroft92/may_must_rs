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

Run the active paper-shaped driver on a bitcode file:

```sh
cargo run --bin main -- tests/out/smash_must.bc
```

Bound the intraprocedural obligation worklist:

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
runs the intraprocedural driver in `src/analysis/driver.rs`.

For each function, the CLI currently chooses a single target assertion by
taking the first embedded `may_assert(...)`. The query postcondition is that
target site's violation predicate:

```text
assert_violation(edge) && !assert_arg
```

Only that selected site is encoded as an assertion-violation target during the
transition step. Other `may_assert(...)` calls remain ordinary call effects.

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
src/analysis/transfer.rs     -> metadata-backed transition oracles
src/analysis/summaries.rs    -> reachability queries and summaries
src/analysis/driver.rs       -> summary reuse + intraprocedural worklist
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
  -> PaperDriver::run_intraprocedural(...)
       worklist element = (edge, source region, destination region)
       MUST-POST        = grows Omega_n
       NOTMAY-PRE       = splits Pi_n and records may edges
```

## What Is Implemented

- explicit paper-shaped CFG, state, summary, and rule modules;
- Option A LLVM adapter with external `EdgeId -> LlvmEdgeMetadata`;
- SMT-backed `PredicateOracle` over active `Predicate` formulas;
- SMT-backed LLVM transition oracle over transfer-derived guard/effect predicates;
- intraprocedural worklist over `(edge, source region, destination region)`;
- CLI wiring to the active paper driver;
- unit tests for the paper-shaped modules;
- smoke coverage for direct bug and direct safe cases.

Current unit-test baseline:

```text
cargo test
26 passed
```

## What Is Not Yet Implemented

- summary use across call edges;
- summary creation and reuse as a full interprocedural lifecycle;
- richer SMT transition/image semantics beyond current Boolean-atom encoding;
- memory modeling in paper-state terms;
- full interprocedural may/must query flow from the paper;
- explicit target selection when a function has multiple embedded assertions;
- command-line `--assert` queries in the paper driver;
- rich LLVM coverage (`phi`, `switch`, `getelementptr`, casts, calls with
  summaries, globals, heap, arrays, structs);
- richer witness/proof evidence for created summaries.

Recommended next milestone:

```text
call-edge summary reuse + summary creation
```

That is the first step that moves the active tree from an intraprocedural
paper skeleton toward a real interprocedural SMASH-style implementation.

The repository should not be described as a full SMASH implementation yet.

## Archived Implementation

The previous development line is preserved under `obsolete/src/analysis`. That
tree still contains the old toy analyzer, the old SMT-oriented path, and the
older analysis notes.

It is intentionally left intact for reference, but it is not part of the
active build.
