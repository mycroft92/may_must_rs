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
- transfer effects
- weakest-precondition / strongest-postcondition helpers
- single-exit normalization
- topological-order check used to reject cyclic CFGs

`adapter.rs`

- lowers a raw `FunctionGraph` into `AdaptedProcedure`
- records assertion sites
- maps `phi` nodes to predecessor-edge assignments
- lowers branches to edge guards
- rewrites memory effects through the integer-array model
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

- orchestrates one assertion query on one acyclic CFG
- rejects cyclic CFGs early
- seeds the obligation at the assertion node
- runs forward reach, then backward state propagation

`oracle.rs`

- SMT feasibility and implication checks
- model rendering for bug reports

`providers.rs`

- seam for external/manual summaries
- loop-invariant hook exists as a placeholder only

`summaries.rs`

- reusable summary-table data structures
- not currently the main CLI-active storage path

`driver.rs`

- module-level orchestration
- fixed-point style return-summary accumulation
- report construction for procedures

## Current Soundness Boundary

The current checker is intentionally limited.

- Acyclic integer/boolean procedures are the supported core.
- Direct-call reasoning works only through the current inferred/manual
  return-summary slice.
- Loops are preserved in the CFG but not analyzed; cyclic procedures return
  `UNKNOWN`.
- Floating-point procedures are reported as unsupported and therefore
  `UNKNOWN`.
