# Analysis Flow

## End-to-End Flow

1. `llvm_utils::program_graph::generate_program_graph`
   builds one raw instruction graph per defined function.

2. `program_graph.rs`
   removes `may_assert` from the visible instruction graph and records each
   assertion as an `AssertSite`.

3. `analysis::adapter::adapt[_with_purity_and_summaries]`
   lowers one `FunctionGraph` into:
   - an `AbstractCfg`
   - a list of lowered assertion sites
   - instruction-to-node bookkeeping

4. `analysis::driver`
   optionally infers and reuses direct-call return summaries across the module.

5. `analysis::backward::analyze`
   checks one assertion site:
   - require an acyclic CFG via `topological_order()`
   - initialize node summaries
   - propagate reachability forward
   - seed the negated assertion obligation at the assertion node
   - propagate backward state to the entry
   - ask `oracle.rs` whether the entry summary is feasible

6. `analysis::oracle`
   lowers formulas into Z3 through `smt::solver` and answers:
   - bug witness feasibility
   - proof feasibility / implication queries

7. `main.rs`
   prints one procedure report and final verdict per function.

## Lowering Notes

- Branch conditions become edge guards.
- `phi` nodes become predecessor-specific edge assignments.
- Multiple concrete exits become one synthetic exit.
- `zext i1 -> i32` lowers through `bool_to_int`.
- Memory uses integer arrays plus `select` / `store`.
- Unsupported procedures are reported, not silently accepted.

## Loop Behavior Today

- Loops survive graph generation and lowering.
- The checker stops at cyclic CFG detection.
- Result: assertions in cyclic procedures are currently reported as
  unsupported/`UNKNOWN`.
