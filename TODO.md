# TODO

## Current Backlog

- add an oracle boundary over `analysis::formula` and `smt::solver`
- wire a forward may pass over `Cfg + node_effects + edge_effects + AnalysisState`
- add a backward/preimage path after the forward pass has settled
- add CLI assertion selection instead of graph-generation-only execution
- add temporary `max_step` loop bounding
- extend LLVM adapter coverage beyond the current scalar/integer subset
- decide how call results and interprocedural summaries should enter the paper model
