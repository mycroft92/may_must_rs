# Analysis Flow

## Implemented Flow

```text
LLVM bitcode
  -> llvm_wrap
  -> program_graph::generate_program_graph
  -> optional DOT dump
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
  - `Assume`
  - `Obligation`
  - `Call`
- evidence/model queries still do not exist yet in the active flow

## Next Wiring Steps

1. Add `driver.rs` to orchestrate the implemented figure modules.
2. Connect lowered effects to rule-premise generation (`β`, `θ`, and call summaries).
3. Add CLI query integration for assertions.
4. Add temporary `max_step` handling before loop summaries.
