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
```

## Important Ownership Rules

- branch conditions become `CfgEdge::relation`
- phi nodes become predecessor-specific edge assignments
- accumulated path summaries are refined and merged in `state.rs`
- satisfiability and implication queries live only in `oracle.rs`
- `transfer.rs` interprets only normalized effects:
  - `Assign`
  - `Assume`
  - `Obligation`
  - `Call`
- evidence/model queries still do not exist yet in the active flow

## Next Wiring Steps

1. Add the named paper rule layer.
2. Wire backward `NOTMAY-PRE` and forward `MUST-POST`.
3. Add CLI query integration for assertions.
4. Add temporary `max_step` handling before loop summaries.
