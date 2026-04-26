# Analysis Flow

## Implemented Flow

```text
LLVM bitcode
  -> llvm_wrap
  -> program_graph::generate_program_graph
  -> optional DOT dump
  -> optional driver::analyze_function_graph_simple
```

## Implemented But Not Wired

```text
FunctionGraph
  -> llvm_adapter::adapt_function_graph
     -> cfg::Cfg
     -> node_effects
     -> edge_effects
  -> transfer::apply_effects
  -> state::AnalysisState
  -> oracle::Oracle feasibility / implication queries
  -> driver::analyze_adapted_procedure_simple
  -> rules::{figure5..figure10}
  -> summaries::SummaryTables
```

## Important Ownership Rules

- branch conditions become `CfgEdge::relation`
- phi nodes become predecessor-specific edge assignments
- accumulated path summaries are refined and merged in `state.rs`
- satisfiability and implication queries live only in `oracle.rs`
- named declarative rules live in `rules.rs`
- summary facts live in `summaries.rs`
- `transfer.rs` interprets only normalized effects:
  - `Assign`
  - `Alloca`
  - `GetElementPtr`
  - `Load`
  - `Store`
  - `Assume`
  - `Obligation`
  - `Call`
- `driver.rs` currently explores one bounded path at a time and checks each
  obligation independently against the current path formula
- repeated loop traversals are cut off by the temporary per-edge `max_step`
  budget in `driver.rs`
- impure calls havoc the currently tracked integer-array memory regions
- false assertions already carry a symbolic driver-collected evidence trace,
  but solver model/evidence queries still do not exist yet in the active flow

## Current Rule API

The implemented rule layer is declarative, not yet scheduled by a full driver.

- `rules::ReachabilityQuery`
  is the paper query `⟨ϕ1 ?⇒_P ϕ2⟩`
- `rules::ProcedureFrame`
  stores the working carriers for one procedure/query pair
- `rules::figure5` through `rules::figure10`
  expose the named rule entry points with paper-facing parameters
- `summaries::SummaryTables`
  stores reusable `¬may ⇒ P` and `must ⇒ P` facts

Today the caller must still provide:

- candidate `β` formulas for `NOTMAY_PRE`
- candidate `θ` formulas for `MUST_POST`
- local-variable projection closures for summary creation

Those inputs will come from the future driver and the lowered transfer/effect
layer. The rule module intentionally does not guess them.

## Conservative Checks

Two rule-level checks deserve explicit mention:

- `VERIFIED` and `CREATE_NOTMAYSUMMARY` use an abstract path search over
  partition regions instead of a concrete execution engine
- solver `Unknown` is treated conservatively as "the premise may still hold" for
  overlap/path checks, which prevents unsound proofs

## Current Driver Slice

`driver.rs` currently implements a smaller, executable slice than the paper
driver:

- it supports one procedure at a time
- it bounds loop exploration by per-edge `max_step`
- it supports local integer-array memory
- it treats calls conservatively: unconstrained returns plus memory havoc unless
  the callee is inferred memory-pure
- it uses `transfer.rs` plus SMT feasibility checks to explore concrete branch
  paths and report explicit per-assertion `true` / `false` / `unknown`
  outcomes

That is enough to run simple straightline, branchy, and bounded-loop assertion
tests, but it is still a temporary bridge to the future rule-driven scheduler.

## Next Wiring Steps

1. Add `driver.rs` to orchestrate the implemented figure modules.
2. Connect lowered effects to rule-premise generation (`β`, `θ`, and call summaries).
3. Add CLI query integration for assertions.
4. Replace temporary `max_step` handling with loop summaries / invariants.
