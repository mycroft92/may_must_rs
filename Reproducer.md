# Reproducer Prompt

Copy the prompt below into a coding-agent session if you want to reproduce the
current implemented milestone from the point where LLVM program graph
generation already exists and is the active code path.

## Prompt

You are working in this repository on the paper-shaped may-must analysis
implementation. Start from the milestone where `src/llvm_utils/program_graph.rs`
exists and is the active implementation, but the paper-shaped analysis tree is
either missing or incomplete.

Your job is to reproduce exactly the currently implemented milestone in this
repository. Do not go beyond it.

### Goal

Build the repository up to this exact state:

- LLVM intraprocedural program graph generation is correct and tested
- parsed assertions can be translated into a paper-shaped formula language
- formulas can be lowered to Z3 through the local SMT wrapper
- a paper oracle can check feasibility and implication over formulas/path summaries
- named paper rules from Figures 5-10 are implemented as explicit APIs
- paper summary tables exist for `¬may ⇒ P` and `must ⇒ P`
- a paper-shaped state layer exists for path summaries, obligations, facts, and
  temporary bounded-progress counters
- a paper-shaped LLVM-independent CFG exists
- the CFG supports synthetic single-exit normalization
- an LLVM-independent transfer layer exists over normalized local effects
- an LLVM adapter lowers the current LLVM instruction graph into:
  - the paper CFG
  - edge-local branch relations
  - normalized node effects
  - normalized edge effects for `phi`
- `may_assert` lowers to negated obligations, not call summaries
- a curated C fixture corpus exists under `tests/flow/` together with a small
  `make -C tests smoke` harness that builds those fixtures into bitcode
- the architecture/docs clearly separate:
  - raw LLVM graph generation
  - parser/frontend lowering
  - paper-core formula, state, CFG, and oracle modules
  - paper rule and summary modules
  - normalized transfer semantics
  - LLVM-specific adapter lowering
  - still-planned rule/driver/summary work

Stop there.

### Do Not Implement Yet

Do not implement any of the following:

- forward driver wiring
- backward driver wiring beyond the minimal oracle boundary
- loop invariant extraction
- the `max_step` engine
- memory modeling beyond explicitly rejecting unsupported instructions
- floating-point transfer semantics beyond explicitly rejecting unsupported
  instructions
- interprocedural summaries or call-result semantics

If a feature depends on any of those, leave it documented as planned or not yet
wired.

### Constraints

- Keep code minimal and understandable.
- Keep paper-core modules LLVM-independent.
- Keep parser-specific logic out of `src/analysis`.
- Prefer `Unknown` over unsound claims.
- Do not read the `obsolete` directory.
- Do not create fallback summaries.
- Do not generate summary/call edges for `may_assert`.
- If an LLVM/function graph has multiple exits, lower it to one synthetic paper
  exit with trivial `true` edges from each real exit.
- Add focused unit tests for each implemented piece.
- Add short module-level doc comments explaining each analysis module’s role and
  the paper notation it maps to.
- Keep unsupported features explicit adapter/transfer errors rather than silent
  no-ops.

### Starting Assumption

Assume the repo already contains:

- `src/llvm_utils/program_graph.rs`
- `src/llvm_utils/llvm_wrap.rs`
- `src/assertions/exp.rs`
- `src/smt/solver.rs`

You should build everything else needed on top of that.

### Required Work

#### 1. Fix and lock down LLVM program graph generation

Work primarily in:

- `src/llvm_utils/program_graph.rs`
- `src/llvm_utils/llvm_wrap.rs` only if needed

Required behavior:

- Build sequential edges inside each basic block.
- Add successor edges from terminator instructions to successor basic blocks.
- Skip noise calls such as `printf` and `putchar`.
- Detect `may_assert` calls.
- Record the single `may_assert` argument instruction in
  `FunctionGraph::asserts`.
- Do not emit a node or call edge for `may_assert`.
- Gracefully skip declaration-only functions so a module with declarations does
  not fail graph generation.

Required tests:

- branch terminator successor edges exist
- `may_assert` is recorded but not emitted as a node
- declaration-only modules are handled cleanly

#### 2. Add the paper formula layer

Create:

- `src/analysis/formula.rs`
- `src/analysis/mod.rs` if needed

Implement:

- `Sort`
- `Var`
- `Term`
- `Formula`
- `Predicate = Formula`
- `FormulaError`
- lowering from `Formula` into `src/smt/solver.rs`

Scope:

- boolean, integer, and real sorts
- arithmetic terms: add, sub, mul, div, neg
- boolean connectives: not, and, or, implies
- relational formulas: equality and comparisons

Required tests:

- SAT integer constraint lowering
- UNSAT contradictory constraint lowering
- boolean implication lowering
- rejection of non-boolean atoms
- rejection of mixed-sort equalities/comparisons

#### 3. Add assertion-to-formula translation

Create:

- `src/assertions/translation.rs`

Purpose:

- translate `src/assertions/exp.rs` syntax into `src/analysis/formula.rs`

Requirements:

- support lowering for expressions, statements, and assertions
- add local sort inference
- support seeded sort assignments for ambiguous cases
- reject unsupported or ambiguous expressions explicitly
- keep all parser-specific sort inference outside `src/analysis`

Required tests:

- integer assertion translation
- real-context translation with integer literal promotion
- bare boolean variable translation
- ambiguous equality rejection without seeds
- seeded sort resolution for ambiguous equality

#### 4. Add analysis docs and module skeletons

Create or update:

- `src/analysis/mod.rs`
- `src/analysis/design.md`
- `src/analysis/analysis_flow.md`
- `src/analysis/state.rs`

Requirements:

- module comments must say what each module is intended to hold
- module comments must mention the paper mapping
- docs must distinguish:
  - implemented and CLI-active
  - implemented but not wired
  - planned
  - unsupported

The docs must clearly say:

- `formula.rs` is implemented
- parser-to-formula translation lives outside `src/analysis`
- the current milestone is still intraprocedural
- `may_assert` should become an obligation later, not a call summary

#### 5. Add the paper state layer

Implement `src/analysis/state.rs` as a minimal paper-core state module.

Required contents:

- a path-summary carrier for `Pi_n`
- an obligation carrier for `Omega_n`
- a tracked-facts carrier for the current concrete interpretation of `N_e`
- a per-node state object
- top-level analysis state storage keyed by CFG node id
- visit/progress counters for the future temporary `max_step` engine

Required behavior:

- entry states can start reachable
- fresh non-entry node states can start unreachable
- path refinement on the same path uses conjunction
- path merging at the same node uses disjunction
- facts and obligations can be accumulated and collapsed back into conjunctions
- analysis state can create/access node states and track node/edge visit counts

Required tests:

- path-summary refinement conjoins guards
- path-summary join disjoins incoming paths
- tracked facts and obligations collapse to conjunctions
- node state stores summaries, facts, and obligations
- analysis state tracks nodes and visit counters

#### 6. Add the paper CFG layer

Create:

- `src/analysis/cfg.rs`

Implement a minimal LLVM-independent CFG with:

- `CfgNodeId`
- `CfgEdgeId`
- `CfgNode`
- `CfgEdge`
- `Cfg`

Required behavior:

- explicit entry node
- tracked exit nodes
- predecessor/successor helpers
- incoming/outgoing edge helpers
- `CfgEdge::relation: Formula` as the current carrier for `Gamma_e`
- default trivial edges use `Formula::True`

Required single-exit normalization:

- if there are multiple exits, create one synthetic exit node
- add trivial `true` edges from each concrete exit to the synthetic exit
- keep the synthetic node explicit in the data model
- if there is already one exit, keep it
- if there are no exits, return an error

Required tests:

- entry/exit tracking
- predecessor/successor lookup
- edge relation storage
- unknown-node rejection
- synthetic exit creation
- single-exit no-op behavior
- missing-exit rejection

#### 7. Add the transfer layer

Create:

- `src/analysis/transfer.rs`

Implement a minimal LLVM-independent transfer layer over normalized local
semantic effects.

Required effect language:

- `Assign { target, value }`
  where `value` is either a numeric `Term` or a Boolean `Formula`
- `Assume(Formula)`
- `Obligation(Formula)`
- `Nop`
- `Call { callee }`

Required behavior:

- keep ordinary branch guards out of the effect stream; they belong on CFG
  edges
- treat `phi` as adapter-lowered assignments, not as transfer-layer LLVM logic
- turn assignments into remembered equalities/equivalences
- refine path summaries with `Assume`
- accumulate obligations separately from facts
- reject unsupported calls in phase 1

Required tests:

- arithmetic assignment produces an equality fact
- predicate assignment produces boolean equivalence
- assumptions refine path summaries
- obligations remain separate from facts
- sequencing composes local effects
- bad-sort assignments are rejected
- calls are rejected as unsupported

#### 8. Add the LLVM adapter layer

Create:

- `src/analysis/llvm_adapter.rs`

Implement a lowering from `llvm_utils::program_graph::FunctionGraph` into:

- `cfg: Cfg`
- `node_effects: BTreeMap<CfgNodeId, Vec<TransferEffect>>`
- `edge_effects: BTreeMap<CfgEdgeId, Vec<TransferEffect>>`
- a stable instruction-to-node mapping for later wiring/tests

Required lowering rules:

- ordinary branch conditions become `CfgEdge::relation`
- `phi` nodes become predecessor-specific edge assignments
- `may_assert` becomes `TransferEffect::Obligation(¬asserted_formula)` on the
  defining node
- normal calls survive as `TransferEffect::Call`
- multiple real exits must be normalized through `Cfg::ensure_single_exit()`
- reject unsupported memory-heavy or floating-point instructions explicitly

Required LLVM wrapper support:

- add only the minimum helper(s) needed for adapter lowering
- current branch needs instruction-parent basic block lookup
- unnamed LLVM basic blocks must still produce a stable label token for phi
  matching

Required supported subset for the adapter:

- integer arithmetic: `add`, `sub`, `mul`, `sdiv`, `udiv`
- boolean/predicate ops: `icmp`, `and`, `or`, `xor`
- control flow: `br`, `ret`, `phi`
- plain `call`

Required tests:

- branch guards lower to CFG edge relations
- phi merges lower to predecessor-specific edge effects
- `may_assert` lowers to a negated obligation
- non-`may_assert` calls survive as normalized `Call` effects
- multiple returns yield one synthetic exit
- unsupported memory instructions are rejected
- compile and lower the supported C fixtures successfully
- compile and reject the unsupported C fixtures explicitly

#### 9. Add a curated C fixture corpus and smoke harness

Create:

- `tests/flow/`
- `tests/README.md`
- `tests/Makefile`
- `tests/out/.gitignore`

Purpose:

- give the entire LLVM graph -> adapter -> transfer -> future driver flow a
  stable set of small C programs to exercise

Requirements for fixture style:

- compile with `clang -emit-llvm -c -O1 -fno-inline -I.`
- prefer SSA-friendly scalar code that lowers to the currently supported subset
- include both positive and negative fixtures

Required positive fixtures:

- straight-line integer arithmetic + `may_assert`
- boolean comparisons + `and/or`
- branch + helper calls + phi merge
- plain non-assert call
- multiple concrete exits
- one loop fixture for future `max_step` work

Required negative fixtures:

- pointer/memory load-store case
- floating-point comparison case

Required smoke harness behavior:

- `make -C tests smoke` must compile all fixtures into `tests/out/.../*.bc`
- generated bitcode stays out of source control
- document why the chosen compile flags preserve the current supported shape

#### 10. Update repository docs

Update:

- `AGENTS.md`
- `Readme.md` if that is the branch file, otherwise `README.md`
- `TODO.md`
- `TASKVIEW.md`
- `Reproducer.md`

The final docs must say:

- the paper-core modules stay LLVM-independent
- `cfg.rs` stores edge-local guards only
- accumulated path predicates belong in `state.rs`
- `transfer.rs` operates on normalized effects produced by `llvm_adapter.rs`
- `llvm_adapter.rs` lowers one procedure into `cfg + node_effects + edge_effects`
- `oracle.rs` should later own SMT satisfiability/evidence queries
- multi-exit lowering uses one synthetic exit
- `may_assert` is not summarized as a call edge
- the next tasks are forward-pass wiring, CLI assertion integration, oracle
  queries, and then `max_step`
- the tests fixture corpus lives under `tests/flow/`
- `make -C tests smoke` is now a real branch command

### Expected Final File Set

At minimum, by the end you should have created or updated:

- `src/llvm_utils/program_graph.rs`
- `src/llvm_utils/llvm_wrap.rs`
- `src/analysis/mod.rs`
- `src/analysis/formula.rs`
- `src/analysis/state.rs`
- `src/analysis/cfg.rs`
- `src/analysis/transfer.rs`
- `src/analysis/llvm_adapter.rs`
- `src/assertions/translation.rs`
- `src/analysis/design.md`
- `src/analysis/analysis_flow.md`
- `AGENTS.md`
- `Readme.md` or `README.md`
- `TODO.md`
- `TASKVIEW.md`
- `Reproducer.md`
- `tests/Makefile`
- `tests/README.md`
- `tests/flow/*.c`
- `tests/out/.gitignore`

### Required Verification

Run:

```sh
cargo fmt
cargo test -- --test-threads=1
make -C tests smoke
```

Do not invent smoke results; if fixture compilation fails, fix the fixture or
its compile harness.

### Exact Stopping Point

You are done when all of the following are true:

- program graph generation is corrected and tested
- formula syntax and Z3 lowering exist and are tested
- assertion-to-formula translation exists and is tested
- `state.rs` exists and tracks path summaries, obligations, facts, and
  progress counters
- CFG exists and synthetic single-exit normalization is tested
- `transfer.rs` exists, is documented, and is tested
- `llvm_adapter.rs` exists, lowers the supported LLVM subset, and is tested
- the curated C fixtures compile through `make -C tests smoke`
- supported fixtures lower cleanly and unsupported fixtures fail explicitly
- docs describe the current paper mapping accurately
- there is still no forward driver/fixpoint/oracle path using the lowered CFG

Do not continue into forward state propagation, oracle queries, CLI assertion
wiring, or bounded loop execution.

### Expected Status After Reproduction

The repository should then honestly describe itself as:

- implemented and CLI-active:
  - LLVM program graph generation
  - C fixture smoke compilation under `tests/`
- implemented but not wired:
  - assertion parser
  - assertion-to-formula translation
  - formula syntax
  - formula-to-Z3 lowering
  - paper state layer
  - paper CFG
  - transfer relations over normalized effects
  - LLVM adapter lowering into paper CFG/effects
- planned:
  - oracle queries
  - forward may analysis
  - backward/must analysis
  - `max_step` loop handling
  - loop invariants and summaries
