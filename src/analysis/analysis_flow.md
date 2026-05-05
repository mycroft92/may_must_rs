# Analysis Flow

## Implemented Flow

```text
LLVM bitcode
  -> llvm_wrap
  -> program_graph::generate_program_graph
  -> optional DOT dump
  -> optional driver::analyze_function_graph_simple
  -> optional driver::analyze_function_graph_rules
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
  -> driver::{analyze_adapted_procedure_simple, analyze_adapted_procedure_rules}
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
- `driver.rs` currently offers two executable slices:
  - a bounded path explorer that checks obligations against the current path
    formula
  - a local rule scheduler that rewrites each assertion into a synthetic
    violation-exit query and runs Figure 5/6/7 over it
- repeated loop traversals are cut off by the temporary per-edge `max_step`
  budget in the bounded slice of `driver.rs`
- impure calls havoc the currently tracked integer-array memory regions
- false assertions already carry a symbolic driver-collected evidence trace,
  and `--rule-check` now replays one local rule-driven witness plus the final
  SMT model for false results

## Current Rule API

The implemented rule layer is now partially scheduled by `driver.rs`.

- `rules::ReachabilityQuery`
  is the paper query `⟨ϕ1 ?⇒_P ϕ2⟩`
- `rules::ProcedureFrame`
  stores the working carriers for one procedure/query pair
- `rules::figure5` through `rules::figure10`
  expose the named rule entry points with paper-facing parameters
- `summaries::SummaryTables`
  stores reusable `¬may ⇒ P` and `must ⇒ P` facts

Today the remaining caller/driver work is:

- broader candidate `β` formulas beyond the current rewritten memory/havoc slice
- broader candidate `θ` formulas beyond the current rewritten memory/havoc slice
- local-variable projection closures for summary creation

The current driver already computes the scalar acyclic `Assign` / `Assume`
subset of `β` / `θ` and rewrites the current integer-array memory plus
impure-call-havoc slice into that scalar form. The remaining pieces belong to
the future summary-aware driver work.

## Conservative Checks

Two rule-level checks deserve explicit mention:

- `VERIFIED` and `CREATE_NOTMAYSUMMARY` use an abstract path search over
  partition regions instead of a concrete execution engine
- solver `Unknown` is treated conservatively as "the premise may still hold" for
  overlap/path checks, which prevents unsound proofs

## Current Driver Slice

`driver.rs` currently implements a smaller, executable slice than the paper
driver:

- bounded slice:
  - it supports one procedure at a time
  - it bounds loop exploration by per-edge `max_step`
  - it supports local integer-array memory
  - it treats calls conservatively: unconstrained returns plus memory havoc
    unless the callee is inferred memory-pure
  - it uses `transfer.rs` plus SMT feasibility checks to explore concrete
    branch paths and report explicit per-assertion `true` / `false` /
    `unknown` outcomes
- rule-driven slice:
  - it supports one procedure at a time
  - it currently requires an acyclic CFG
  - it builds one query-specific synthetic violation exit per assertion
  - it computes scalar `β` / `θ` candidates from normalized `Assign` /
    `Assume` effects and `Gamma_e`
  - it rewrites the current `Alloca` / `GetElementPtr` / `Load` / `Store` and
    impure-call-havoc slice into a path-expanded scalar query before those
    rules run
  - it schedules local Figure 5/6/7 rules plus `IMPL_LEFT` / `IMPL_RIGHT`
  - it also replays one feasible violating path through that query CFG and
    prints the final SMT model

That is enough to run straightline and branchy rule-driven unit tests plus the
broader bounded-loop temporary checker, but summary-driven calls and loop
invariants still remain for the future driver.

## Next Wiring Steps

1. Extend the current rule scheduler to Figures 8-10 call/summary rules.
2. Connect lowered memory/call effects to richer `β` / `θ` generation.
3. Replace temporary `max_step` handling with loop summaries / invariants.
4. Extend rule-driven witnesses to summary, memory, and loop-aware queries.
