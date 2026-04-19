# analysis2: Paper-Shaped Scaffold

`src/analysis2` is intentionally separate from `src/analysis`.

The current `analysis` tree is executable and useful, but it mixes paper
concepts with implementation concerns: SMT path states, LLVM transfer helpers,
summary lookup, and CLI behavior.  `analysis2` exists so we can rebuild the
algorithm in the paper's vocabulary first and only later connect it to LLVM,
Z3, or the old analyzer.

## Boundary

`analysis2` must not import from:

```text
crate::analysis
```

It may later have adapters from LLVM or SMT modules, but the core rule modules
should stay paper-shaped.

`analysis2` core modules should also stay independent from LLVM wrapper types:

```text
cfg.rs
formula.rs
state.rs
rules.rs
summaries.rs
driver.rs
oracle.rs
```

LLVM-specific adaptation belongs in dedicated bridge modules.

## Paper Symbols

| Paper symbol | Meaning | analysis2 location |
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
src/analysis2/rules.rs
```

The initial functions are:

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

The important distinction from the existing `analysis/may_must_rules.rs` is
that `analysis2::rules::must_post_edge` is the paper's transition rule:

```text
Ω_n1 + Γ_e -> θ -> Ω_n2
```

It is not merely a cached-summary postcondition overlap check.

## Oracles

The paper rules ask set questions:

```text
is_empty(φ)
φ1 ⊆ φ2
φ1 ∩ φ2 != {}
θ ⊆ Post(Γ_e, source)
Pre(Γ_e, target) ⊆ β
```

`analysis2` keeps these abstract:

```text
oracle::PredicateOracle
oracle::TransitionOracle
```

The included `SyntacticOracle` is only for scaffold tests.  A later SMT-backed
oracle can reuse the same rule functions without changing the paper-level
types.

## Option A: External Edge Metadata

The current implementation uses Option A from the design discussion:

```text
PaperEdge remains LLVM-agnostic.
LLVM facts live in an external EdgeId -> metadata table.
TransitionOracle consumes that metadata table.
```

New modules:

```text
src/analysis2/llvm_adapter.rs
  FunctionGraph -> (PaperProcedure, LlvmEdgeRegistry)

src/analysis2/transfer.rs
  LlvmTransitionOracle + LlvmEdgeTransfer
```

### Why this split

1. `rules.rs` stays directly readable against paper notation.
2. LLVM parsing concerns (opcode decoding, operand naming, branch-arm
   direction) are isolated from proof-rule code.
3. The transition layer can be swapped later without changing rule APIs.
4. The same rule code can be reused with a future SMT-backed transition model.

### What metadata contains

`LlvmEdgeMetadata` stores enough edge-local facts for transition synthesis:

```text
edge_id, from, to
opcode
instruction text
assignment variable (if any)
callee (if call)
operands
branch condition (if branch)
branch successor index
```

### Current transition approximation

`transfer.rs` currently provides a conservative syntactic model:

```text
theta = source ∧ guard(edge) ∧ effect(edge)
beta  = guard(edge)
```

where:

- `guard(edge)` is branch-condition based for conditional branches and `true`
  otherwise;
- `effect(edge)` is a symbolic atom derived from opcode and operands.

This is scaffolding, not final semantic precision.  It keeps the rule-level
interfaces stable while transfer precision is improved.

## Driver Shape

`driver::PaperDriver` currently implements only the deterministic summary
reuse order:

```text
1. applicable must summary -> yes
2. applicable not-may summary -> no
3. otherwise intraprocedural analysis is needed
```

The intraprocedural driver should eventually own a worklist over:

```text
Π_n
Ω_n
N_e
```

and call the named rules in `rules.rs`.

## Next Implementation Steps

1. Add an explicit `IntraproceduralState` worklist that iterates over edges and
   regions.
2. Apply `must_post_edge` and update `Ω_n2`.
3. Apply `not_may_pre_edge` and split `Π_n1`.
4. Add call-edge handling through `must_post_use_summary` and
   `not_may_pre_use_summary`.
5. Improve `analysis2::transfer` from syntactic guard/effect atoms toward
   stronger SMT-backed post/pre approximations.
6. Add an SMT-backed `PredicateOracle`.
7. Add an adapter from `llvm_utils::program_graph::FunctionGraph` into
   `analysis2::cfg::PaperProcedure` (now present in `llvm_adapter.rs`) and
   expand opcode coverage.
8. Only after the paper-shaped engine is understandable, consider wiring it
   behind a new CLI engine switch.
