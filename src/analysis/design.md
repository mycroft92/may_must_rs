# Active Paper-Shaped Analysis

`src/analysis` is the active implementation. Its job is to keep the SMASH
paper's objects and rules visible in code, then connect them cleanly to LLVM.

For the flow-oriented companion, including SMT layering guidance, see:

```text
src/analysis/analysis_flow.md
```

The older mixed implementation was moved to:

```text
obsolete/src/analysis
```

That archived tree is still useful for reference, but it is not part of the
active build.

## Boundary

The active core modules stay paper-shaped:

```text
cfg.rs
formula.rs
state.rs
rules.rs
summaries.rs
driver.rs
oracle.rs
```

LLVM-specific adaptation belongs in:

```text
llvm_adapter.rs
transfer.rs
```

The core paper modules should not depend on LLVM wrapper types or raw Z3
operations.

## Paper Symbols

| Paper symbol | Meaning | active location |
|---|---|---|
| `P` | procedure | `cfg::PaperProcedure` |
| `n` | CFG node | `vocabulary::NodeId` |
| `e = <n1,n2>` | CFG edge | `cfg::PaperEdge` |
| `Γ_e` | concrete transition relation for edge `e` | `PaperEdge::gamma` |
| `Π_n` | partition at node `n` | `state::Partition` |
| `φ` | region/predicate over states | `formula::Predicate` / `state::Region` |
| `Ω_n` | under-approx must-reachable states at node `n` | `state::PaperAnalysisState::omega` |
| `N_e` | may edge set between regions | `state::MayEdge` |
| `θ` | under-approx post image added to `Ω_n2` | `rules::RuleConclusion::AddOmega` |
| `β` | over-approx preimage used to split a source region | `rules::RuleConclusion::RefineAndAddMayEdge` |
| must summary | existential procedure summary | `summaries::ProcedureSummary` with `SummaryKind::Must` |
| not-may summary | proof of unreachability | `summaries::ProcedureSummary` with `SummaryKind::NotMay` |

## Rule Placement

Named paper rules live in:

```text
src/analysis/rules.rs
```

Current explicit functions:

```text
must_post_edge
not_may_pre_edge
must_post_use_summary
not_may_pre_use_summary
applicable_must_summary
applicable_not_may_summary
create_must_summary
create_not_may_summary
```

The important distinction is:

```text
must_post_edge = paper transition rule
Omega_n1 + Gamma_e -> theta -> Omega_n2
```

not a summary-overlap shortcut.

## Option A: External Edge Metadata

The active tree uses Option A:

```text
PaperEdge remains LLVM-agnostic.
LLVM facts live in an external EdgeId -> metadata table.
TransitionOracle consumes that metadata table.
```

This split is implemented by:

```text
src/analysis/llvm_adapter.rs
  FunctionGraph -> (PaperProcedure, LlvmEdgeRegistry)

src/analysis/transfer.rs
  LlvmTransitionOracle + SmtLlvmTransitionOracle + LlvmEdgeTransfer
```

### Why this split

1. `rules.rs` stays readable against paper notation.
2. LLVM parsing and branch-arm decoding stay out of proof-rule code.
3. The transition layer can be strengthened without changing rule APIs.
4. A future SMT-backed transition model can reuse the same paper-shaped rules.

### What metadata contains

`LlvmEdgeMetadata` stores enough edge-local facts for transition synthesis:

```text
edge_id, from, to
opcode
instruction text
assignment variable
callee
operands
branch condition
branch successor index
```

## Current Transition Approximation

`transfer.rs` currently exposes two transition oracles over the same metadata:

```text
LlvmTransitionOracle     -> syntactic guard/effect composition
SmtLlvmTransitionOracle  -> same composition with SMT emptiness filtering
```

Both currently use:

- `guard(edge)`: branch-condition based for conditional branches and `true`
  otherwise;
- `effect(edge)`: symbolic atom derived from opcode and operands.

This is scaffolding, not the final semantic precision.

## Driver Shape

`driver::PaperDriver` currently has:

```text
answer_from_summaries(query)
run_intraprocedural(procedure, query)
run_interprocedural(query)
```

The local worklist unit is:

```text
(edge, source region, destination region)
```

Current rule use:

```text
MUST-POST   -> grows Omega_n
NOTMAY-PRE  -> splits Pi_n and records a may edge
call edges with summaries
  -> MUST-POST-USE-SUMMARY / NOTMAY-PRE-USE-SUMMARY
internal calls without an applicable summary
  -> project callee query (MayCall), recurse, create summary, retry summary rules
```

Current MayCall projection notes:

```text
projected call pre/post currently strip edge-local atoms (e.g. "... @eK")
vacuous projected call post -> fallback target atom "retval_<callee> < 0"
Figure-1 shape heuristic -> synthesize NotMay summary: true => retval_<callee> < 0
```

This keeps summaries in a procedure-boundary vocabulary, but it is still a
heuristic and not yet the final semantic projection design.

Current initialization:

```text
Omega_entry = query.pre
Pi_exit     = { query.post, !query.post }
other Pi_n  = { true }
```

Current requeue policy:

```text
Omega growth at node n -> enqueue outgoing obligations from n
Pi split at node n     -> enqueue incoming and outgoing obligations touching n
```

## Current CLI Mapping

`src/main.rs` currently does:

```text
bitcode
  -> generate_program_graph
  -> adapt_function_graph
  -> build default query
  -> run_interprocedural
```

The current default query builder is still provisional. It targets a single
embedded `may_assert(...)` by taking the first one and builds:

```text
assert_violation(site) && !assert_arg
```

Only that selected target site is encoded as `assert_violation(site)` inside
the transition layer. Other `may_assert(...)` calls remain ordinary call
effects.

The remaining limitation is target selection: the active CLI still chooses the
first embedded assertion automatically.

## Next Implementation Steps

1. Resolve one explicit target assertion per query instead of taking the first
   embedded site.
2. Strengthen `SmtPredicateOracle` beyond Boolean atom encoding.
3. Strengthen `SmtLlvmTransitionOracle` beyond the current syntactic
   guard/effect composition.
4. Replace the current MayCall heuristics
   (`retval_<callee> < 0` fallback + shape-based direct not-may synthesis)
   with semantic return-demand projection derived from caller constraints.
5. Introduce a paper-level memory object in active state/query vocabulary.
6. Expand LLVM coverage only as the active driver demands it.
