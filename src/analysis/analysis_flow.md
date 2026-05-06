# Analysis Flow

## Implemented Flow

```text
LLVM bitcode
  -> llvm_wrap
  -> program_graph::generate_program_graph
  -> optional DOT dump
  -> optional driver::analyze_function_graph_simple
  -> optional driver::analyze_function_graphs_rules_with_purity_best_effort
```

## Implemented Rule Flow

```text
Vec<FunctionGraph>
  -> llvm_adapter::adapt_function_graph_with_purity
     -> AdaptedProcedure { cfg, summary_structure, loops, node_effects, edge_effects, interface, assertions }
  -> driver::RuleModuleEngine
     -> build_base_rule_procedure per function
     -> build_assertion_query_procedure per assertion
     -> rewrite_rule_query_procedure for the current memory/call-havoc slice
     -> rules::{figure5..figure10}
     -> summaries::{SummaryRepository, SummaryProvider}
     -> oracle::Oracle feasibility / implication / model queries
     -> per-procedure RuleProcedureReport values
```

## Important Ownership Rules

- branch conditions become `CfgEdge::relation`
- phi nodes become predecessor-specific edge assignments
- accumulated path summaries are refined and merged in `state.rs`
- satisfiability and implication queries live only in `oracle.rs`
- named declarative rules live in `rules.rs`
- summary facts live in `summaries.rs`
- loop regions and the acyclic condensation order live in `cfg.rs`
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
  - an interprocedural rule scheduler that rewrites each assertion into a
    synthetic violation-exit query and runs the currently supported Figure
    5-10 slice over it
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
- richer summary projection/elimination beyond the current syntactic interface slice
- loop invariant verification and loop-aware summary scheduling

The current driver already computes the scalar acyclic `Assign` / `Assume`
subset of `β` / `θ`, rewrites the current integer-array memory plus
impure-call-havoc slice into that scalar form, alpha-renames and substitutes
summary interfaces at call sites, maps supported call queries back to callee
interfaces, and now keeps loop SCCs as explicit summary regions. The remaining
pieces belong to the broader future driver work.

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
  - it analyzes one module at a time so summaries can be shared across calls
  - it currently requires an acyclic summary structure
  - it builds one query-specific synthetic violation exit per assertion
  - it also builds one base summary-capable rule procedure per analyzed
    function
  - it computes scalar `β` / `θ` candidates from normalized `Assign` /
    `Assume` effects and `Gamma_e`
  - it rewrites the current `Alloca` / `GetElementPtr` / `Load` / `Store` and
    impure-call-havoc slice into a path-expanded scalar query before those
    rules run
  - it schedules the currently supported Figure 5-10 rules, including summary
    reuse, subquery enqueueing, and discovered summary recording
  - it instantiates summaries at call sites through alpha-renamed interface
    substitution over actual arguments, scalar return targets, and visible
    memory ports
  - it already extracts loop regions and the condensation DAG that future
    invariant generation will consume
  - it also replays one feasible violating path through that query CFG and
    prints the final SMT model

That is enough to run straightline and branchy rule-driven unit tests plus the
broader bounded-loop temporary checker, but loop invariants and richer summary
interfaces still remain for the future driver.

## Next Wiring Steps

1. Add oracle-backed verification/adoption for loop invariant candidates over the extracted loop regions.
2. Connect lowered memory/call effects to richer `β` / `θ` generation and projection.
3. Add the opt-in candidate-provider path for future LLM or imported summaries/invariants.
4. Replace temporary `max_step` handling with loop summaries / invariants.
