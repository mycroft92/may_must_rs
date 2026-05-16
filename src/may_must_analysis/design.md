# Analysis Design

## Current Pipeline

The active implementation is:

`FunctionGraph -> AdaptedProcedure(AbstractCfg) -> backward analysis`

This is a lighter-weight shape than the older planned paper tree. The code no
longer routes through separate live `cfg`, `state`, `loops`, and `transfer`
modules. Instead:

- `abstract_cfg.rs` owns the CFG plus transfer semantics
- `adapter.rs` owns LLVM lowering into that CFG
- `backward.rs` and `rules.rs` own the current proof/search logic
- `driver.rs` owns module orchestration and call-summary reuse

## Module Responsibilities

`formula.rs`

- typed terms and formulas
- rational values
- integer-array memory terms
- SMT model payload type
- helper `bool_to_int` term for lowered LLVM casts

`abstract_cfg.rs`

- node and edge identifiers
- abstract nodes and edges
- transfer effects (including `HavocRegions` for targeted region havocing)
- weakest-precondition / strongest-postcondition helpers
- single-exit normalization
- topological-order and back-edge helpers used by the cyclic checker

`alias_analysis.rs`

- field-sensitive, flow-insensitive Andersen points-to analysis
- run once per module (or per function) before lowering
- produces `AliasResult` mapping each SSA pointer to its abstract locations
- consumed by `resolve_memory_effects` to resolve pointer operations the
  local `PointerEnv` cannot handle

`adapter.rs`

- lowers a raw `FunctionGraph` into `AdaptedProcedure`
- records assertion sites
- maps `phi` nodes to predecessor-edge assignments
- lowers branches to edge guards
- rewrites memory effects through the integer-array model, using `AliasResult`
  as a fallback for unresolved `PointerStore`/`PointerLoad` operations
- infers memory-pure functions
- infers direct-call return summaries and reuses them

`node_summary.rs`

- per-node reachability and backward state summaries

`rules.rs`

- propagation rules used by the current checker
- forward reach propagation (`must_post`)
- backward state propagation (`notmay_pre`)
- final verified / bug-found queries

`backward.rs`

- orchestrates one assertion query on one procedure CFG
- uses direct backward checking for acyclic procedures
- for cyclic procedures, reuses precomputed invariants or searches
  algorithmic/CHC/Houdini/template/LLM candidates
- seeds the obligation at the assertion node
- runs summary-aware reach/state fixpoint propagation

`oracle.rs`

- SMT feasibility and implication checks
- model rendering for bug reports

`providers.rs`

- seam for external/manual summaries
- loop-invariant / LLM context plumbing

`summaries.rs`

- reusable summary-table data structures
- includes cached loop invariants used for reporting and reuse

`driver.rs`

- module-level orchestration
- runs whole-module alias analysis before the summary loop
- fixed-point style return-summary accumulation
- loop-invariant precomputation and caching
- report construction for procedures

## Current Soundness Boundary

The current checker is intentionally limited.

- Integer/boolean procedures are the supported core.
- Direct-call reasoning works only through the current inferred/manual
  return-summary slice.
- Cyclic procedures are only handled when the checker accepts a loop invariant;
  otherwise they remain `UNKNOWN`.
- Floating-point procedures are reported as unsupported and therefore
  `UNKNOWN`.
