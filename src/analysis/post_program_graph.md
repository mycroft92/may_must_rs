# After `program_graph`: Assertion-to-Result Flow

This document explains what happens after
`llvm_utils::program_graph::generate_program_graph` has produced one
`Vec<FunctionGraph>`.

Scope:

- input: a program already converted into `FunctionGraph`s
- question: given one assertion in that program, how do we reach `true`,
  `false`, or `unknown`?
- active path: the default rule-driven checker in `src/analysis/driver.rs`

This is the current implementation, not the final paper-complete design.

## 1. Starting Point

After `program_graph` runs, the analysis has:

- one `FunctionGraph` per LLVM procedure
- instruction vertices and edges
- `may_assert` sites already separated from ordinary call edges
- enough LLVM-facing structure to lower into the paper-shaped analysis

At this point the active driver no longer reasons directly on raw LLVM
instructions. It first lowers each `FunctionGraph` into the analysis-specific
representation in `src/analysis`.

## 2. Module Preparation

The CLI passes the whole `Vec<FunctionGraph>` into
`driver::analyze_function_graphs_rules_with_purity_best_effort_with_options`.

Before any one assertion is solved, the driver computes a conservative
module-level memory-purity set with
`llvm_adapter::infer_memory_pure_functions`.

That set answers one narrow question:

- if procedure `f` is called, does `f` preserve tracked memory, or must the
  caller assume memory havoc?

The purity result affects call lowering later.

## 3. Per-Function Lowering into `AdaptedProcedure`

Each `FunctionGraph` is lowered by
`llvm_adapter::adapt_function_graph_with_purity` into an `AdaptedProcedure`.

That lowering does six things.

### 3.1 Build the paper CFG

The adapter creates a `cfg::Cfg`:

- one paper entry node
- one paper node per visible instruction
- copied control-flow edges
- branch conditions lowered onto CFG edges as `Gamma_e`

If the original function has multiple exits, `Cfg::ensure_single_exit()` adds
one synthetic exit node and trivial `true` edges from the old exits.

### 3.2 Lower node and edge effects

LLVM instructions are normalized into `transfer::TransferEffect`s.

Examples:

- arithmetic / comparisons -> `Assign`
- `alloca` -> `Alloca`
- `gep` -> `GetElementPtr`
- `load` -> `Load`
- `store` -> `Store`
- ordinary calls -> `Call`

Important ownership split:

- branch conditions stay on CFG edges
- `phi` nodes become predecessor-specific edge assignments
- trusted refinements would be `Assume`

### 3.3 Lower assertions

`may_assert` is not kept as an ordinary call summary edge.

Instead the adapter records an `AdaptedAssertionSite` and lowers the negated
assertion into an `Obligation` attached to the relevant CFG node.

So conceptually the lowered meaning is:

```text
“the bad state is reachable here if path-condition ∧ !(assertion) is feasible”
```

### 3.4 Recover the procedure interface

The adapter records the current summary/call interface:

- scalar formal parameter names
- optional scalar return slot
- visible caller-owned memory roots

Visible memory roots are the pointer-shaped values that must survive procedure
boundaries, because summaries may refer to them.

### 3.5 Recover loop structure

The adapter calls `loops::extract_loops` and `loops::summary_structure`.

This produces:

- explicit loop SCCs as `LoopRegion`
- an acyclic condensation DAG as `SummaryStructure`

Today loops are extracted structurally, but cyclic procedures are still
rejected by the active rule path until verified loop summaries exist.

### 3.6 Package the result

The lowered procedure is stored as:

```text
AdaptedProcedure {
  cfg,
  node_effects,
  edge_effects,
  interface,
  assertions_by_node,
  loops,
  summary_structure,
  ...
}
```

## 4. Rule Engine Initialization

The driver constructs one `RuleModuleEngine` for the whole module.

This matters because summaries are shared across procedures.

During initialization the engine:

- stores one `PreparedRuleProcedure` per procedure
- creates one reusable base summary-capable procedure per function
- creates one `SummaryRepository`
- creates one `Oracle`

## 5. Summary Generator Configuration

Before solving assertions, the engine configures one `loops::SummaryGenerator`.

Current behavior:

- default: internal `KnasterTarskiLoopSummaryGenerator`
- optional: external JSON summary catalog from the CLI
- if external summaries are enabled: use
  `loops::FallbackSummaryGenerator(external, internal)`

That means the external route is opt-in, but missing external entries do not
disable the built-in path.

After configuration, the engine asks the generator for:

- function summaries
- loop summaries

Returned function summaries are stored immediately in `SummaryRepository`.

Returned loop summaries are currently only stabilized structurally through the
internal Knaster-Tarski wrapper and then recorded as loop-invariant
candidates. They are not yet used to discharge cyclic procedures.

## 6. Build the Base Summary Procedure

For each function the engine builds a reusable base procedure with
`build_base_rule_procedure`.

This procedure:

- copies the lowered CFG
- removes assertion obligations
- keeps ordinary transfer effects
- remains `summary_capable = true`

This is the procedure used when:

- creating reusable `must` summaries
- creating reusable `¬may` summaries
- mapping call subqueries into callee space

## 7. Expand One Assertion into a Reachability Query

When the engine analyzes procedure `P`, it sorts all `AdaptedAssertionSite`s
by stable assertion id and handles them one by one.

For one assertion site, the driver builds a dedicated query procedure with
`build_assertion_query_procedure`.

This is the critical transformation.

### 7.1 Copy the original lowered procedure

The driver copies:

- the CFG
- node effects, except `Obligation`
- edge effects

### 7.2 Add a synthetic violation exit

The driver adds one fresh node:

```text
__assert{id}_violation
```

Then it adds one edge from the assertion node to that violation node with edge
relation equal to the lowered bad condition:

```text
site.obligation = path-local form of !(assertion)
```

So the query is no longer “check an obligation at this node.”
It becomes:

```text
“can the program reach the synthetic violation exit?”
```

### 7.3 Normalize the query

The query procedure is single-exit normalized again and marked
`summary_capable = false`, because assertion queries are solved for a verdict,
not exported as reusable procedure summaries.

### 7.4 Query object

The current rule query itself is:

```text
ReachabilityQuery {
  procedure = "P#assertN",
  precondition = true,
  postcondition = true
}
```

That looks trivial, but it is correct because the actual bad condition now
lives on the synthetic violation edge.

## 8. Rewrite the Query into the Current Scalar Rule Slice

The active rule engine cannot yet consume every lowered effect directly.

So before running the named rules, the driver rewrites the assertion query with
`rewrite_rule_query_procedure`.

This uses `RuleRewriteState`.

### 8.1 Memory model during rewrite

The rewrite state tracks:

- visible memory roots
- pointer bindings
- current symbolic memory arrays
- memory epoch for havoc

Visible interface memory starts as:

- `root$mem_in`
- `root$offset`

### 8.2 Effect rewriting

The rewrite turns memory-heavy effects into the current scalar rule slice.

Examples:

- `Alloca` only updates pointer bindings
- `GetElementPtr` only updates pointer offsets
- `Load` becomes `Assign(target := select(memory, offset))`
- `Store` updates the symbolic memory term with `store(...)`

For calls:

- scalar and boolean arguments are copied
- pointer arguments are resolved into:
  - canonical region
  - effective offset
  - `memory_before`
  - `memory_after`

If the call is impure, the rewrite currently havocs tracked memory
conservatively before later loads are lowered.

### 8.3 Materialize visible post-memory

At concrete exits, the rewrite emits assumptions of the form:

```text
root$mem_out == current_memory(root)
```

This is how procedure summaries can later refer to visible post-state memory.

## 9. Reject Unsupported Shapes Early

Before solving, the rule path checks the rewritten query.

Current important rejection:

- if the query `SummaryStructure` still has loops, return
  `DriverError::CyclicRuleProcedure`

So loops are known structurally, but not yet proved through invariants.

## 10. Solve the Query with the Paper Rules

`RuleModuleEngine::solve_query` is the executable heart of the current
implementation.

### 10.1 Initialize paper carriers

The engine creates one `rules::ProcedureFrame` and applies:

- `figure5::INIT_PI_NE`
- `figure6::INIT_OMEGA`

So the current analysis state is:

- `Π_n`
- `Ω_n`
- `N_e`
- the active reachability query

### 10.2 Fixed scheduling loop

Each round currently does:

1. check `BUGFOUND`
2. check `VERIFIED`
3. apply one `MUST_POST` round
4. apply one `NOTMAY_PRE` round
5. apply closure rules (`IMPL_LEFT`, `IMPL_RIGHT`)
6. apply call-summary reuse
7. enqueue and solve call subqueries

If no rule changes the frame, the loop stops.

### 10.3 What the oracle does

Every semantic premise goes through `oracle::Oracle`:

- feasibility
- disjointness / overlap
- implication
- final witness model queries

The rule modules do not talk to the SMT solver directly.

## 11. Interprocedural Calls

When a rewritten query contains a supported call, two things can happen.

### 11.1 Reuse already-known summaries

If the repository already contains summaries for the callee, the driver
instantiates them at the call site:

- alpha-rename callee interface names
- substitute actual scalar/boolean arguments
- substitute visible memory input/output ports
- optionally substitute the return slot

Then it tries the Figure 10 summary-use rules.

### 11.2 Ask new subqueries

If the current caller state suggests the callee matters, the driver forms new
subqueries with:

- `figure8::MAY_CALL`
- `figure9::MUST_CALL`
- `figure10::MAY_MUST_CALL`

Those queries are mapped from caller symbols back into the callee interface and
queued. The engine then solves them recursively through the same rule path.

## 12. Summary Creation

When a solved query belongs to a base procedure rather than an assertion query,
the engine may record a reusable summary:

- final `No` -> `figure8::CREATE_NOTMAYSUMMARY`
- final `Yes` -> `figure9::CREATE_MUSTSUMMARY`
- final `Unknown` -> no summary

Before storage, the summary is projected to the callee-visible interface:

- formals
- optional return
- visible `mem_in` / `mem_out`
- visible offsets

## 13. Convert Query Judgement into Assertion Result

Once the synthetic violation query is solved:

- `QueryJudgement::Yes` means the violation exit is reachable
  -> assertion result is `false`
- `QueryJudgement::No` means the violation exit is unreachable
  -> assertion result is `true`
- `QueryJudgement::Unknown`
  -> assertion result is `unknown`

So the final assertion answer is derived from reachability of the synthetic bad
exit, not from directly checking the original source assertion at runtime.

## 14. Witness Generation for `false`

If the final query judgement is `Yes`, the driver builds a
`RuleWitnessTrace`.

That witness is currently reconstructed from the lowered assertion query CFG:

- replay one feasible violating path
- collect generated formulas along the path
- ask the oracle for the final feasible model

This is the user-facing evidence currently printed for failing rule-check
results.

## 15. Procedure-Level Aggregation

A function may contain multiple assertions.

The final `RuleProcedureReport` aggregates them as:

- if any assertion is `false` -> procedure judgement `Yes`
- else if any assertion is `unknown` -> procedure judgement `Unknown`
- else -> procedure judgement `No`

Interpretation:

- `Yes` means “a bug was found”
- `No` means “all lowered assertions were proved safe on the supported slice”
- `Unknown` means “the current implementation could not decide at least one”

## 16. Current Important Approximations

The main things to keep in mind while reading current results are:

- cyclic procedures are still rejected by the rule path
- memory is integer-array only
- impure calls still use conservative memory havoc when no stronger summary is
  available
- projection is still syntactic, not full quantifier elimination
- external generators may provide loop/function summaries, but loop summaries
  are not yet used to discharge cyclic procedures

## 17. Short Version

Once `program_graph` is built, the current implementation does this:

1. lower each `FunctionGraph` into `AdaptedProcedure`
2. recover CFG, effects, assertions, interface memory ports, and loop regions
3. initialize the module-level rule engine and summary generator
4. build one reusable base procedure per function
5. turn each assertion into a synthetic “bad exit reachable?” query
6. rewrite the current memory/call slice into the scalar rule fragment
7. run the Figure 5-10 scheduler with SMT-backed premises
8. reuse or discover interprocedural summaries as needed
9. convert final reachability judgement into `true` / `false` / `unknown`
10. if `false`, emit a rule witness and SMT model
