# Analysis Flow

## End-to-End Flow

1. `llvm_utils::program_graph::generate_program_graph`
   builds one raw instruction graph per defined function.

2. `program_graph.rs`
   removes `may_assert` and `may_assume` from the visible instruction graph,
   recording each assertion as an `AssertSite` and each assumption as an
   `AssumeSite`.

2.5. `common::alias_analysis::run_alias_analysis`
   runs field-sensitive, flow-insensitive Andersen alias analysis on the full
   module (called once by the driver before the summary loop, and once per
   function by `analyze_with_summaries`).  The `AliasResult` is threaded into
   all `adapt_with_purity_and_summaries` calls.

3. `analysis::adapter::adapt[_with_purity_and_summaries]`
   lowers one `FunctionGraph` into:
   - an `AbstractCfg`
   - a list of lowered assertion sites
   - instruction-to-node bookkeeping
   `resolve_memory_effects` uses the `AliasResult` as a fallback when the local
   `PointerEnv` cannot resolve a `PointerStore` or `PointerLoad` target.
   `lower_assumes` injects each `AssumeSite` as `TransferEffect::Assume(cond)`
   on the nearest CFG node; the backward WP then conjoins `cond` (not implies)
   to exclude infeasible violation traces.

4. `analysis::driver`
   infers and reuses direct-call return summaries across the module, and
   precomputes/cache loop invariants for cyclic procedures.

5. `analysis::backward::analyze`
   checks one assertion site:
   - if acyclic, analyze directly
   - if cyclic, precompute or search for an accepted loop invariant
   - initialize node summaries
   - propagate reachability forward
   - seed the negated assertion obligation at the assertion node
   - run the reach/state fixpoint
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
- The driver first discovers algorithmic candidates for cyclic procedures.
- The backward checker can then validate algorithmic, CHC, Houdini, template,
  and optional LLM candidates.
- If no candidate is accepted, assertions in cyclic procedures remain
  unsupported/`UNKNOWN`.
