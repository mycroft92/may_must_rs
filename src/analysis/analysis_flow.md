# Analysis Flow

This file is the flow-heavy companion to `src/analysis/design.md`.

`design.md` captures the stable module map. This document explains how a query
is supposed to move through the active codebase, how that corresponds to the
paper notation, and where SMT encoding should eventually sit.

The filename is intentionally `analysis_flowq.md` because that is the active
request for this repository.

## 1. Current Active Flow

The active code path is:

```text
main.rs
  -> llvm_utils::program_graph::generate_program_graph(...)
  -> analysis::llvm_adapter::adapt_function_graph(...)
  -> build ReachabilityQuery
  -> analysis::transfer::LlvmTransitionOracle
  -> analysis::driver::PaperDriver::run_intraprocedural(...)
  -> analysis::rules::{must_post_edge, not_may_pre_edge}
```

In paper vocabulary, this is currently:

```text
LLVM bitcode
  -> procedure P with nodes n and edges e
  -> edge relation placeholders Gamma_e
  -> query <pre, post>
  -> intraprocedural rule loop over (e, phi1, phi2)
  -> update Omega_n and Pi_n
```

What is active today:

- explicit `P`, `n`, `e`, `Gamma_e` containers;
- explicit `Pi_n`, `Omega_n`, and may edges `N_e`;
- explicit named rule functions;
- LLVM metadata-backed transition approximation;
- one target assertion per query.

What is not active yet:

- interprocedural summary-driven call handling;
- summary creation lifecycle;
- SMT-backed predicate reasoning;
- SMT-backed transition images;
- paper-level memory;
- full may/must alternation loop from the paper.

## 2. File-To-Paper Correspondence

### `src/analysis/vocabulary.rs`

Owns the small identifiers that let the rest of the tree stay in paper
notation:

```text
ProcedureName -> procedure P
NodeId        -> node n
EdgeId        -> edge e
RegionId      -> partition region / abstract state block
```

### `src/analysis/formula.rs`

Owns solver-independent predicates:

```text
Predicate -> phi, beta, theta, query pre/post, summary pre/post
```

This file is intentionally not Z3-specific. The paper rules speak in sets and
relations; this file keeps that vocabulary abstract.

### `src/analysis/cfg.rs`

Owns the paper-shaped control-flow graph:

```text
PaperProcedure -> P
PaperEdge      -> e
PaperEdge::gamma -> Gamma_e
entry/exit     -> distinguished entry/exit nodes of P
```

This is the first paper-shaped container after LLVM has been adapted.

### `src/analysis/state.rs`

Owns the mutable analysis state:

```text
Partition at node n      -> Pi_n
Must-reachable states    -> Omega_n
May abstract edges       -> N_e
Region                   -> phi_i inside Pi_n
```

This is the file that should stay closest to the paper's abstract state.

### `src/analysis/summaries.rs`

Owns procedure-boundary objects:

```text
ProcedureSummary         -> function summary
SummaryKind::Must        -> must summary
SummaryKind::NotMay      -> not-may summary
ReachabilityQuery        -> query Q
query.pre/query.post     -> boundary pre/post predicates
target_assertion         -> currently selected assertion site
```

When the implementation becomes fully interprocedural, this file remains the
boundary vocabulary for procedure calls.

### `src/analysis/rules.rs`

Owns named paper rule functions:

```text
must_post_edge           -> MUST-POST
not_may_pre_edge         -> NOTMAY-PRE
must_post_use_summary    -> MUST-POST-USE-SUMMARY
not_may_pre_use_summary  -> NOTMAY-PRE-USE-SUMMARY
```

The rule inputs correspond directly to the paper:

```text
edge.gamma      -> Gamma_e
omega_n1        -> Omega_n1
source_region   -> phi1
dest_region     -> phi2
theta           -> chosen under-approximate post image
beta            -> chosen over-approximate pre image
```

This file must stay solver-agnostic and LLVM-agnostic.

### `src/analysis/oracle.rs`

Owns the abstract reasoning boundary used by `rules.rs`:

```text
PredicateOracle::is_empty / intersects / subset
  -> paper set tests over predicates

TransitionOracle::post_under_approx
  -> choose theta subset Post(Gamma_e, source)

TransitionOracle::pre_over_approx
  -> choose beta with Pre(Gamma_e, target) subset beta
```

This file is where solver-backed reasoning plugs into the rule layer without
changing the rule APIs.

## 2.5. What `TransitionOracle` Actually Does

`TransitionOracle` is the paper-facing interface for edge semantics.

It does **not** own the CFG, the analysis worklist, summary storage, or the
solver backend itself. Its job is narrower:

```text
given an edge e with relation Gamma_e
and a predicate over source or target states
return the transition fact that the paper rule needs next
```

In practice that means it answers exactly two questions.

### A. Forward question for `MUST-POST`

The rule needs some:

```text
theta subset Post(Gamma_e, source)
```

So `TransitionOracle::post_under_approx(edge, source)` must:

1. interpret `edge` as the transition relation `Gamma_e`;
2. interpret `source` as a set of states before the edge;
3. compute or choose a `theta` that is definitely reachable after that edge.

The important word is:

```text
under-approximate
```

If `theta` says a state is reachable after the edge, that claim should be
sound for the analysis model. `theta` is allowed to be too small. It must not
invent impossible successor states.

Current example:

```text
source = Omega_n1 ∩ phi1
edge   = branch-true edge for condition %c
theta  = source && %c && take_branch(e)
```

Later SMT-backed example:

```text
theta(s_post) :=
  exists s_pre .
    source(s_pre) ∧ Gamma_e(s_pre, s_post)
```

possibly followed by a chosen abstraction.

### B. Backward question for `NOTMAY-PRE`

The rule needs some:

```text
Pre(Gamma_e, target) subset beta
```

So `TransitionOracle::pre_over_approx(edge, target)` must:

1. interpret `edge` as the transition relation `Gamma_e`;
2. interpret `target` as a set of states after the edge;
3. compute or choose a `beta` that safely contains all predecessors that could
   reach `target` through this edge.

The important word is:

```text
over-approximate
```

If a predecessor can really reach `target` via `Gamma_e`, it must be inside
`beta`. `beta` is allowed to be too large. It must not exclude real
predecessors.

Current example:

```text
target = phi2
edge   = false branch of br %c
beta   = !%c
```

Later SMT-backed example:

```text
beta(s_pre) :=
  exists s_post .
    Gamma_e(s_pre, s_post) ∧ target(s_post)
```

possibly followed by abstraction.

### Why The Rules Need This Interface

The paper rules should not care whether `Gamma_e` is handled by:

- a syntactic LLVM approximation;
- a symbolic executor;
- a Z3 encoding;
- predicate abstraction over a chosen vocabulary.

They only need the contracts:

```text
post_under_approx -> a safe theta for MUST-POST
pre_over_approx   -> a safe beta for NOTMAY-PRE
```

That is why `TransitionOracle` exists separately from `PredicateOracle`.

`PredicateOracle` answers set questions about already-built predicates:

```text
is_empty?
intersects?
subset?
```

`TransitionOracle` constructs the next transition-related predicate the rule
needs:

```text
theta from Gamma_e and source
beta  from Gamma_e and target
```

### What `TransitionOracle` Should Know About

It is reasonable for a concrete `TransitionOracle` implementation to know:

- LLVM edge metadata;
- symbolic pre/post state variables;
- SMT encodings of instructions;
- abstraction choices for `theta` and `beta`.

### What `TransitionOracle` Should Not Own

It should not own:

- `Pi_n` or `Omega_n`;
- summary tables;
- the interprocedural driver;
- rule scheduling;
- CLI target resolution.

Those belong to `state.rs`, `summaries.rs`, `driver.rs`, and `main.rs`.

### Where SMT Fits

An SMT-backed implementation would use `TransitionOracle` as the place where:

```text
Gamma_e(s_pre, s_post)
```

is actually encoded and queried.

That still does **not** mean `llvm_adapter.rs` should do SMT work. The clean
split remains:

```text
llvm_adapter.rs -> identify edge e and attach metadata
transfer.rs     -> describe edge semantics / relation shape
smt layer       -> encode Gamma_e and solve post/pre queries
TransitionOracle -> expose the result to rules.rs
```

### `src/analysis/llvm_adapter.rs`

Owns LLVM-to-paper adaptation only:

```text
FunctionGraph                -> PaperProcedure
LLVM edge                    -> EdgeId
EdgeId -> LlvmEdgeMetadata   -> external metadata table
```

This file should never own Z3 operations. It only translates LLVM structure
into stable paper-shaped identities and metadata.

### `src/analysis/transfer.rs`

Owns LLVM-backed transition modeling:

```text
LlvmEdgeTransfer            -> metadata -> guard/effect semantics
LlvmTransitionOracle        -> TransitionOracle implementation
edge_guard(...)             -> branch-side guard
edge_effect(...)            -> current edge effect approximation
```

Conceptually, this file is the LLVM-specific helper that approximates
`Gamma_e`-based reasoning. Today it is syntactic. Later it should be backed by
symbolic state and SMT, while still serving `TransitionOracle`.

### `src/analysis/driver.rs`

Owns orchestration:

```text
PaperDriver                 -> top-level analysis driver
answer_from_summaries(...)  -> summary applicability stage
run_intraprocedural(...)    -> local worklist over (e, phi1, phi2)
```

Current rule loop:

```text
MUST-POST   -> grow Omega_n
NOTMAY-PRE  -> refine Pi_n and add may edges
```

This file is the closest thing to the paper's algorithmic control loop.

### `src/analysis/design.rs`

This file only exists so editor/doc navigation exposes the active design note.
It is not an algorithmic part of the implementation.

### `src/analysis.rs`

This is the crate-level module boundary for the active paper-shaped tree.

### `src/main.rs`

Owns CLI orchestration:

```text
bitcode file -> function graphs -> adapted procedure -> query -> driver
```

This file is not part of the paper's reasoning rules. It is the entry-point
plumbing that chooses which procedure/query to run.

### `src/smt/solver.rs`

Owns raw Z3 mechanics:

```text
Z3Interface        -> low-level solver operations
SmtEncodingContext -> symbol ownership and cached Z3 terms
```

This file is not the paper-level oracle by itself. It is the backend utility
that a future SMT encoding/oracle layer should use.

## 3. Where SMT Should Enter

The active tree does not yet have an SMT encoding layer in `src/analysis`.
That is why the current rules are still backed by `SyntacticOracle` and the
syntactic `LlvmTransitionOracle`.

The clean layering is:

```text
formula.rs / state.rs
  -> analysis-level vocabulary

smt encoding layer
  -> Predicate / state / Gamma_e into Z3 terms

oracle implementation
  -> emptiness / subset / intersection / post / pre

rules.rs
  -> unchanged paper rules
```

The important point is that `llvm_adapter.rs` should not set up SMT directly.
It should only provide stable edge metadata.

Likewise, `transfer.rs` should not own the raw solver lifecycle. It should
describe or help build edge semantics that a solver-backed oracle can query.

## 4. Do We Need A Separate `smt_oracle`?

Not necessarily as a separate file or type name.

What is required is:

1. a way to encode `Predicate` and symbolic state into Z3;
2. a way to answer `PredicateOracle` queries;
3. a way to answer `TransitionOracle` queries.

So there are two clean designs.

### Option A: one combined SMT object

```text
SmtOracle
  implements PredicateOracle
  implements TransitionOracle
```

This is sufficient if the implementation stays readable.

### Option B: split encoding from oracle

```text
SmtEncoding
  -> owns Predicate/state/Gamma_e encoding

SmtPredicateOracle
  -> emptiness / subset / intersection

SmtTransitionOracle
  -> post_under_approx / pre_over_approx
```

This is better if state encoding and transition encoding become large.

The crucial distinction is:

```text
formula -> SMT encoding
```

is not enough on its own, because the paper rules also need:

```text
Post(Gamma_e, ...)
Pre(Gamma_e, ...)
```

So if by "formula SMT one" you mean only:

```text
Predicate -> Z3 Bool
```

then no, that is not sufficient for a full implementation.

If instead you mean:

```text
one SMT-backed module that encodes both predicates and transition images
and implements both oracle traits
```

then yes, that is sufficient. You do not need a separately named
`smt_oracle.rs` if one module can own both responsibilities cleanly.

## 5. Recommended Next SMT Shape

The clean next step is:

```text
src/analysis/smt_encoding.rs
```

with responsibilities:

```text
StateVars / phase-local symbolic variables
Predicate -> Z3 Bool encoding
Gamma_e / edge relation encoding
helpers for existential post-image and pre-image queries
```

Then either:

```text
src/analysis/oracle.rs
  keep traits only

src/analysis/smt_encoding.rs
  implement one SmtOracle for both traits
```

or:

```text
src/analysis/smt_oracle.rs
  wrap SmtEncodingContext and implement the traits
```

The file split is a code-organization choice. The paper-level need is the
trait behavior, not the filename.

## 6. Recommended Next Implementation Order

If the goal is to move toward a real SMT-backed implementation without
confusing the paper mapping:

1. keep `llvm_adapter.rs` metadata-only;
2. keep `rules.rs` unchanged;
3. add a structured SMT encoding layer under `src/analysis`;
4. make that layer implement `PredicateOracle` first;
5. then make it implement `TransitionOracle`;
6. only after that strengthen call-summary handling and memory.

That keeps the rule layer stable while the reasoning engine underneath becomes
real.
