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
```

## Important Ownership Rules

- branch conditions become `CfgEdge::relation`
- phi nodes become predecessor-specific edge assignments
- accumulated path summaries are refined and merged in `state.rs`
- `transfer.rs` interprets only normalized effects:
  - `Assign`
  - `Assume`
  - `Obligation`
  - `Call`
- satisfiability and evidence queries do not exist yet in the active flow;
  `oracle.rs` remains future work

## Next Wiring Steps

1. Add an oracle boundary over `formula.rs` and `smt::solver`.
2. Add forward propagation over `Cfg + effects + state`.
3. Add CLI query integration for assertions.
4. Add temporary `max_step` handling before loop summaries.
