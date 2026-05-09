# REPRODUCER

Terse rebuild spec. Goal: regenerate this repo's `src/analysis/`,
`src/smt/`, `src/llvm_utils/program_graph.rs`, and `src/main.rs` to match
the current state, starting from a tree where `src/llvm_utils/llvm_wrap.rs`,
`src/expressions/`, `src/assertions/`, and the test fixtures exist.

## 0. Cargo.toml

```toml
[package]
name = "llvm_reader"
version = "0.1.0"
edition = "2021"

[dependencies]
llvm-sys = "180"
libc = "0.2"
env_logger = "0.11"
log = "0.4"
clap = { version = "4.5", features = ["cargo"] }
thiserror = "2.0.16"
dot = "0.1.4"
chumsky = { features = ["pratt"], version = "0.11" }
ariadne = "0.5.1"
z3 = "0"
z3-sys = "0"
psm = "=0.1.27"

[[bin]]
name = "main"
path = "src/main.rs"

[env]
Z3_SYS_Z3_HEADER = "/usr/include/z3.h"
```

No tokio. No serde. No async-trait.

## 1. Module map

```
src/main.rs                        CLI: --no-dot, --show-summaries, --debug-invariants;
                                   analyze_module_with_provider.
src/smt.rs                         pub mod chc; pub mod solver;
src/smt/solver.rs                  SmtScope with 3-second Z3 timeout; model_bindings
                                   probes formula-mentioned Select indices; formula_to_z3,
                                   term_to_z3_int exposed.
src/smt/chc.rs                     HornModel, CallRef, ChcSession; CHC fixedpoint for
                                   recursive summary inference.
src/analysis/mod.rs                pub mod for every module below.
src/analysis/formula.rs            or_all/and_all with deduplication + True/False short-circuit;
                                   collect_select_indices (new).
src/analysis/source.rs             UNCHANGED.
src/analysis/abstract_cfg.rs       AbstractCfg + AbstractNode{pre,transfer,post}
                                   + TransferEffect (incl PointerStore/PointerLoad/MemoryStore)
                                   + TransferFn(wp,sp) + PointerEnv
                                   + detect_back_edges + topological_order_excluding.
src/analysis/node_summary.rs       NodeSummary{node,reach,state} combined().
src/analysis/adapter.rs            FunctionGraph → AbstractCfg + AssertionSite[]
                                   + WriteEffectSummary + ReturnSummary{write_effects}
                                   + CallSummaryRegistry + ext_region_name/obs_name
                                   + build_horn_model + collect_callee_names
                                   + integer/float cast lowering (SExt/ZExt/Trunc/BitCast).
src/analysis/oracle.rs             Oracle{feasibility,implies,check_summary,check_chc_property};
                                   feasibility_with_model collects Select indices from formula.
src/analysis/rules.rs              RuleEngine{init,must_post,notmay_pre,must_post_usesummary,
                                   notmay_pre_usesummary,notmay_pre_pruned,run_to_fixpoint,
                                   verified,bugfound} + N_e blocked_edges.
src/analysis/loops.rs              LoopInfo + detect_loops + algorithmic_candidates +
                                   sort_innermost_first + check_loop_invariant
                                   (initiation + inductiveness + exit-closure).
src/analysis/backward.rs           analyze / analyze_with_tables (loop-aware,
                                   preliminary backward pass for exit-closure) +
                                   compute_preliminary_backward_states +
                                   run_backward + render_result + pretty_formula.
src/analysis/summaries.rs          NotMaySummary/MustSummary/SummaryTables (carrier).
src/analysis/providers.rs          CandidateProvider + NoProvider + ManualProvider.
src/analysis/llm_provider.rs       LlmBackend + StubLlmBackend + LlmCandidateProvider
                                   + FullLoopContext + RecursiveContext
                                   + build_loop_invariant_prompt + build_recursive_summary_prompt.
src/analysis/driver.rs             ProcedureReport + SafetyVerdict + ModuleReport
                                   + analyze_module_with_provider (phases 0–1b–2)
                                   + analyze_with_summaries + infer_chc_summaries
                                   + recursive_functions (Kosaraju SCC).
src/llvm_utils/program_graph.rs    FunctionGraph gains pointer_param_indices:Vec<usize>;
                                   NOISE_CALLS filters printf/putchar from vertices.
```

## 2. Changes to abstract_cfg.rs

### Extra TransferEffect variants

```rust
PointerStore { target_slot: String, value_ptr: String }  // Nop in wp/sp
PointerLoad  { target_ptr:  String, source_slot: String } // Nop in wp/sp
MemoryStore  { region: String, offset: Term, value: Term }
// wp(MemoryStore(r,o,v))(post) = post[Memory::Var(r) ↦ Store(Memory::Var(r),o,v)]
```

### New methods

```rust
pub fn topological_order_excluding(excluded: &BTreeSet<CfgEdgeId>)
    -> Option<Vec<CfgNodeId>>
// Kahn's algorithm ignoring excluded edges.  Returns None if remaining graph is cyclic.

pub fn detect_back_edges(&self) -> Vec<(CfgEdgeId, CfgNodeId, CfgNodeId)>
// Iterative DFS.  Returns (edge_id, latch, header) for each back-edge.
```

`topological_order()` delegates to `topological_order_excluding(&BTreeSet::new())`.

## 3. program_graph.rs

`FunctionGraph` gains `pub pointer_param_indices: Vec<usize>`.
Built in `FunctionGraph::new` by checking `TypeKind::Pointer` on each param.

`NOISE_CALLS = &["printf", "putchar"]` — these instructions are excluded from
`vertices` so the analysis never sees them as nodes.

## 4. formula.rs changes

### or_all / and_all (modified)

Both now deduplicate items via `Vec::contains` (syntactic `PartialEq`):

```rust
pub fn or_all<I>(formulas: I) -> Self
// Skips False items; flattens nested Or; deduplicates; short-circuits to True.

pub fn and_all<I>(formulas: I) -> Self
// Skips True items; flattens nested And; deduplicates; short-circuits to False.
```

Deduplication prevents formula blowup in the backward fixpoint: repeated
backward passes no longer accumulate identical disjuncts in state[n].
Short-circuiting `and_all` to `False` and `or_all` to `True` reduces oracle calls.

### collect_select_indices (new)

```rust
pub fn collect_select_indices(formula: &Formula) -> Vec<i64>
// Walks the formula/term tree and returns every integer constant c
// appearing as the index in a Term::Select(_, Term::Int(c)) node.
// Used by the oracle to probe array regions at formula-mentioned indices.
```

## 5. adapter.rs

### Cast instruction lowering (new)

```rust
InstructionOpcode::SExt | InstructionOpcode::ZExt | InstructionOpcode::Trunc =>
    Some(Assign { target, value: source })
// Identity: all integer widths collapse to Sort::Int.

InstructionOpcode::FPExt | InstructionOpcode::FPTrunc
| InstructionOpcode::SIToFP | InstructionOpcode::UIToFP
| InstructionOpcode::FPToSI | InstructionOpcode::FPToUI =>
    None  // APPROX_HEAVY: result variable unconstrained.

InstructionOpcode::BitCast | InstructionOpcode::AddrSpaceCast =>
    None  // APPROX_HEAVY: pointer alias lost; loads/stores through result are Nop.
```

SExt identity is required for GEP offsets: `-O0` IR sign-extends the loop
counter from i32 to i64 before passing it to GEP.

### Other types and flow (unchanged from prior spec)

```rust
pub struct WriteEffectSummary { param_index, ext_region_name, obs_name, relation: Formula }
pub struct ReturnSummary { function, formal_parameters, retval_name, relation, write_effects }
pub struct CallSummaryRegistry { summaries: BTreeMap, next_call_site: Cell<usize> }
pub fn ext_region_name(fn, idx) -> String  // "fn$__ext_idx"
pub fn ext_obs_name(fn, idx) -> String     // "fn$__ext_idx_obs"
```

`adapt_with_purity_and_summaries` flow: lower instructions → branch guards →
phi-as-edge-effects → may_assert → ensure_single_exit →
`resolve_memory_effects` (returns final PointerEnv) →
`apply_pending_write_effects`.

`summary_assume_for_call` emits `Obligation(R)` (NOT `Assume(R)`).

`compute_return_summary` uses backward wp, seeds `state[exit] =
wp(exit.transfer)(retval == retval_obs)`.

## 6. smt/solver.rs

### SmtScope::new (modified)

```rust
pub fn new() -> Self {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", 3000);  // 3-second cap; Unknown is treated conservatively
    solver.set_params(&params);
    Self { solver, ..Self::default() }
}
```

### model_bindings (signature change)

```rust
pub fn model_bindings(&self, extra_indices: &[i64]) -> Option<SmtModel>
// Always probes index 0; also probes every index in extra_indices.
// If all probed values are the same: emits ArrayDefault(value).
// If values differ per index: emits one scalar entry per index as
//   Var::int("region[idx]") so counterexamples are index-specific.
```

### Exposed helpers (unchanged)

```rust
pub fn formula_to_z3(&mut self, formula: &Formula) -> Result<Bool, FormulaError>
pub fn term_to_z3_int(&mut self, term: &Term) -> Result<Int, FormulaError>
```

## 7. smt/chc.rs (unchanged structure)

```rust
pub struct CallRef { callee, actual_args: Vec<Term>, result_var: String, result_sort }
pub struct HornModel { function, params: Vec<(String,Sort)>, retval_var, summary_formula, call_refs }
pub struct ChcSession { fp: Fixedpoint, predicates: BTreeMap<String,FuncDecl> }
impl ChcSession {
    pub fn new(models: &[&HornModel]) -> Self
    pub fn check_property(&self, function, model, property) -> Validity
}
pub fn default_property_templates(retval_name) -> Vec<Formula>
pub fn param_relative_templates(retval_name, params) -> Vec<Formula>
```

## 8. oracle.rs (modified)

```rust
pub fn feasibility_with_model(&self, formula: &Formula) -> Result<FeasibilityReport, OracleError>
// Now calls collect_select_indices(formula) before checking.
// Passes the indices to scope.model_bindings(&extra_indices).
// All other callers (feasibility, implies, check_summary) unchanged.

pub fn check_chc_property(&self, model, callee_models, property) -> Validity
// Unchanged.
```

## 9. rules.rs (unchanged since prior spec)

```rust
pub struct RuleEngine<'a> {
    cfg: &'a AbstractCfg,
    summaries: BTreeMap<CfgNodeId, NodeSummary>,
    blocked_edges: BTreeSet<CfgEdgeId>,
}

pub fn block_edge(&mut self, edge)
pub fn must_post(edge)
pub fn notmay_pre(edge)
pub fn notmay_pre_pruned(edge, oracle)
pub fn notmay_pre_usesummary(edge, tables, oracle)
pub fn must_post_usesummary(edge, tables)
pub fn run_to_fixpoint(order, tables, oracle) -> Result<usize,_>
// Safety cap = |edges|+1 iterations.
```

## 10. loops.rs (extended)

```rust
pub struct LoopInfo {
    header: CfgNodeId, latch: CfgNodeId, back_edge: CfgEdgeId,
    body: BTreeSet<CfgNodeId>, exit_edges: Vec<CfgEdgeId>,
    back_edge_guard: Formula,
}

pub fn detect_loops(cfg) -> Vec<LoopInfo>
// Back-edge analysis. Body = BFS backward from latch to header.
// exit_edges = edges from body nodes to non-body nodes.

pub fn algorithmic_candidates(loop_info, cfg) -> Vec<Formula>
// Sources: back-edge guard + header→body edge guards + exit-edge guards
//          + body ICmp Assign predicates (for -O0 IR where icmp is a node).
// For each (counter, bound) pair: generates i≥0, i≤bound, 0≤i≤bound.
// From body Assign effects: i≥lb for constant initialisations.

pub fn sort_innermost_first(loops: &[LoopInfo]) -> Vec<usize>
// Lᵢ < Lⱼ iff Lᵢ.body ⊂ Lⱼ.body (proper subset).

pub type InnerInvariants<'a> = &'a [(CfgNodeId, Formula)];
// (inner_header, accepted_invariant) pairs for loops strictly inside this one.

pub fn check_loop_invariant(
    loop_info, cfg, candidate, oracle,
    inner_invariants: InnerInvariants<'_>,
    exit_postconditions: &[(CfgEdgeId, Formula)],
) -> bool
```

### Three oracle checks

**1. Initiation** (backward WP from header to entry):

```
seed:    init_state[header] = ¬candidate
action:  backward WP through non-back-edge path to cfg.entry()
check:   oracle.feasibility(init_state[entry]) == Infeasible  →  PASS
```

Uses backward WP (not forward SP) to correctly handle memory-based counters:
`wp(MemoryStore(stack, 0, 0))(¬(select(stack,0)≥0))` evaluates to False via
array-theory substitution.

**2. Inductiveness** (guard-free body WP):

```
normalize:  candidate_mem = header.transfer.wp(candidate)
seed:       body_wp[latch] = back_edge.transfer.wp(candidate_mem)
action:     backward WP through body edges (guards replaced by True)
check:      oracle.implies(candidate_mem, body_wp[header]) == Valid  →  PASS
```

Normalizing via `header.transfer.wp` converts raw SSA names to memory form so
both sides of the implication speak the same variable language.
Guards are dropped so inductiveness only checks assignments, not the loop condition.
Inner loop headers are seeded with their accepted invariants (black-box treatment).

**3. Exit-closure** (skipped when `exit_postconditions` is empty):

```
for each (exit_edge_id, postcond) in exit_postconditions
    where exit_edge_id ∈ loop_info.exit_edges:
    exit_guard = cfg.edge(exit_edge_id).guard
    check:  oracle.feasibility(candidate_mem ∧ exit_guard ∧ postcond) == Infeasible  →  PASS
```

`postcond` = `state[exit_target]` from the preliminary backward pass — the
violation precondition at the loop exit, expressed in memory form.
Checks that the invariant (in memory form) combined with the loop-exit
condition cannot coexist with a violation path. Rejects invariants that are
valid but irrelevant to the specific assertion being proved.

## 11. backward.rs (extended)

```rust
pub fn analyze(cfg, site, oracle) -> Result<AssertionResult, BackwardError>
// Delegates to analyze_with_tables with empty SummaryTables.

pub fn analyze_with_tables(cfg, site, oracle, tables) -> Result<...>
// Fast path: topological_order() succeeds → run_backward directly.
// Cyclic CFG path:
//   1. detect_loops(cfg); compute excluded = {all back-edges}.
//   2. order = topological_order_excluding(excluded).
//   3. preliminary_states = compute_preliminary_backward_states(cfg, site, order, excluded).
//      Gives state[v] for every node; state[loop_exit_target] = violation precondition.
//   4. sort_innermost_first; for each loop (innermost first):
//      a. Build exit_postconditions from preliminary_states[exit_target].
//      b. Build inner_invariants from already-accepted inner loops.
//      c. Try algorithmic_candidates → check_loop_invariant (all 3 checks).
//   5. If all loops accepted: run_backward(order, excluded, accepted_invariants).
//   6. If any loop rejected: Err(CyclicCfgUnsupported).

fn compute_preliminary_backward_states(
    cfg, site, order: &[CfgNodeId], blocked: &BTreeSet<CfgEdgeId>
) -> Result<BTreeMap<CfgNodeId, Formula>, BackwardError>
// Seeds state[site.node] = wp(site.transfer)(¬obligation).
// Single backward notmay_pre pass (no must_post, no tables).
// Returns state formula per node; used for exit-closure postconditions.

fn run_backward(cfg, site, oracle, tables, order, blocked, loop_invariants)
// Blocks all edges in `blocked` (adds to N_e).
// Seeds reach[header] ∧= invariant for each accepted loop invariant.
// Seeds assertion state.
// Calls engine.run_to_fixpoint(order, tables, oracle).
// Decides bugfound → verified → Unknown.
```

## 12. summaries.rs (unchanged)

```rust
pub struct NotMaySummary { precondition: Formula, postcondition: Formula }
pub struct MustSummary   { precondition: Formula, postcondition: Formula }
pub struct SummaryTables { notmay: BTreeMap<..>, must: BTreeMap<..> }
    init_notmay, init_must, notmay(name)->&[..], must(name)->&[..],
    add_notmay (dedup), add_must (dedup).
```

`SummaryTables::default()` returns empty tables.

## 13. providers.rs (unchanged)

```rust
trait CandidateProvider {
    fn function_summary(&self, callee: &str) -> Option<ReturnSummary> { None }
    fn loop_invariant(&self, ctx: &LoopContext) -> Vec<Formula> { Vec::new() }
}
struct NoProvider;
struct ManualProvider { function_summaries: BTreeMap<String,ReturnSummary> }
    new, with_function_summary(builder), add_function_summary
impl CandidateProvider for ManualProvider { fn function_summary → cloned }
```

## 14. llm_provider.rs (unchanged)

```rust
pub struct FullLoopContext { base: LoopContext, header_wp, variable_sorts,
                             body_effects_text, back_edge_guard }
pub struct RecursiveContext { function, formal_parameters, current_relation,
                              caller_entry_formula }
pub trait LlmBackend: Send + Sync { fn propose(&self, prompt: &str) -> Option<String> }
pub struct StubLlmBackend;   // always None
pub fn stub_backend() -> Box<dyn LlmBackend>
pub fn build_loop_invariant_prompt(ctx: &FullLoopContext) -> String
pub fn build_recursive_summary_prompt(ctx: &RecursiveContext) -> String
pub fn parse_candidate(raw: &str, seeds: &BTreeMap<String,Sort>) -> Option<Formula>
pub struct LlmCandidateProvider { backend, max_proposals, manual_summaries }
    propose_loop_invariants(ctx, seeds) -> Vec<Formula>
    propose_recursive_summary(ctx) -> Option<ReturnSummary>
impl CandidateProvider for LlmCandidateProvider
```

## 15. driver.rs (unchanged)

```rust
pub struct ProcedureReport { procedure, assertions: Vec<AssertionResult>, failures: Vec<String> }
    verdict() -> SafetyVerdict
pub enum SafetyVerdict { Safe, Unsafe, Unknown }
pub struct ModuleReport { reports, summaries: SummaryTables,
                          computed_summaries: BTreeMap<String,ReturnSummary> }

pub fn analyze_function_graph(graph, oracle)
pub fn analyze_module(graphs, memory_pure, oracle)
pub fn analyze_module_with_provider(graphs, memory_pure, provider, oracle) -> Result<ModuleReport,_>
pub fn analyze_with_summaries(graph, memory_pure, registry, tables, oracle)
pub fn analyze_function_graph_with_purity(graph, memory_pure, oracle)

fn infer_chc_summaries(graphs, memory_pure, recursive, oracle, registry)
fn recursive_functions(graphs) -> BTreeSet<String>   // Kosaraju two-pass DFS
```

### analyze_module_with_provider phases

```
Phase 0:  provider-supplied extern summaries (callees not in graphs).
Phase 1:  bottom-up fixpoint for non-recursive functions (backward wp).
Phase 1b: infer_chc_summaries for recursive SCCs (Z3 Spacer).
          Populate SummaryTables: Must{True, relation}, NotMay{True, ¬relation}.
Phase 2:  analyze_with_summaries per graph (tables → run_to_fixpoint with
          N_e + summary-guided pruning + loop invariant search).
```

## 16. main.rs

```rust
// CLI flags: --no-dot, --show-summaries, --debug-invariants
// --debug-invariants: sets loop_invariant target to Debug level.
// Calls analyze_module_with_provider(&graphs, &memory_pure, &NoProvider, &oracle).
// print_module_report:
//   Per procedure: "[N assertions, M instructions | K loops | recursive]"
//   Assertions: render_result (judgement + counterexample).
//   Notes: loop invariant failure → "algorithmic invariant generation tried..."
//          recursive → "recursive procedure — summary is over-approximate"
//   --show-summaries: return + write-effect formulas.
//   Module verdict: SAFE / UNSAFE / UNKNOWN.
```

## 17. Verification

```sh
cargo fmt
cargo test -- --test-threads=1    # 84 tests, all pass

make -C tests ir                  # rebuild fixture bitcode if .c sources change

# Acyclic fixtures
cargo run --bin main -- --no-dot tests/out/straight_line_assert.bc
# → assertion #1 Verified, SAFE

cargo run --bin main -- --no-dot tests/out/multi_exit.bc
# → both assertions Verified, SAFE

cargo run --bin main -- --no-dot tests/out/float_compare.bc
# → no assertions, SAFE

# Inter-procedural fixtures
cargo run --bin main -- --no-dot tests/out/paper_section2_fig1_not_may.bc
# → g SAFE, section2_example1_not_may assertion #1 Verified, Module SAFE

# Loop fixtures (all three checks: initiation + inductiveness + exit-closure)
cargo run --bin main -- --no-dot tests/out/loop_counter.bc
# → subject assertion #1 Verified, Module SAFE

# Array/cast fixture (tests SExt/BitCast lowering; complex formulas — result Unknown)
cargo run --bin main -- --no-dot tests/out/array_program.bc
# → main: assertions go into backward analysis; verdict Unknown (loop invariants
#   accepted but array-content formulas too complex for algorithmic invariants)
```

## 18. Test inventory (84 tests)

- `formula.rs`: 6
- `oracle.rs`: 4
- `node_summary.rs`: 5
- `abstract_cfg.rs`: 10
- `summaries.rs`: 3
- `rules.rs`: 7  (+4 N_e / usesummary tests)
- `loops.rs`: 4
- `backward.rs`: 3
- `adapter.rs`: 5
- `driver.rs`: 7
- `llm_provider.rs`: 4
- `providers.rs`: 3
- `source.rs`: 2
- `smt::solver`: 4
- `smt::chc`: 2
- `assertions::translation`: 5
- `expressions::exp`: 3
- `llvm_utils::program_graph`: 4
- `llvm_utils::llvm_wrap`: 0
(sum: 84)

## 19. What is intentionally absent

- Bounded path explorer / `--simple-check` (deleted).
- `max_step` loop bounding (deleted).
- Exit-closure check without assertion context: when `exit_postconditions` is
  empty (e.g. LLM provider calling `check_loop_invariant` directly), the
  exit-closure step is skipped. Wire `compute_preliminary_backward_states`
  output through the LLM provider to enable it.
- Loop invariants stored in `SummaryTables` for callers to reuse.
- LLM wiring into the driver's Phase 1b for loop invariants (scaffolded in
  `llm_provider.rs`; `LlmCandidateProvider::propose_loop_invariants` exists).
- `indirectbr` terminators: all listed destinations treated as unreachable.
- Pointer-typed phi nodes: memory bindings at join points lost.
- Float-integer cast identity (SIToFP/FPToSI lowered as Nop, result unconstrained).
- FRem floating-point remainder (raises `UnsupportedFloatingPointInstruction`).
- Floating-point memory (float alloca/store/load).
- Richer SmtModel per-index enumeration for non-constant Select indices
  (only integer constants in `Term::Int(c)` positions are probed).
- Full bidirectional inter-procedural interplay (paper §3): current driver
  does a single bottom-up sweep, not the paper's N_e-driven cross-procedure cycle.
- Recursive-fixpoint widening (user to specify approach).
- LLM HTTP backend (user provides; docs/llm_integration.md describes the trait).
