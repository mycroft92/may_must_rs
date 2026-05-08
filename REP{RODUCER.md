# REPRODUCER

Terse rebuild spec for a lower-intelligence model. Goal: regenerate
`src/analysis/`, `src/main.rs`, and `Cargo.toml` to match this repo's
current state, starting from a tree where `src/llvm_utils/program_graph.rs`,
`src/llvm_utils/llvm_wrap.rs`, `src/smt/solver.rs`, `src/expressions/`,
`src/assertions/`, and the test fixtures already exist.

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
src/main.rs                       CLI: parse bitcode, run analyze_module, print verdict.
src/analysis/mod.rs               pub mod abstract_cfg/adapter/backward/driver/formula/
                                  node_summary/oracle/providers/rules/source/summaries.
src/analysis/formula.rs           UNCHANGED. Formula/Term/Memory/Var/Sort/SmtModel.
src/analysis/source.rs            UNCHANGED. SourceLocation { file, line, column }.
src/analysis/abstract_cfg.rs      AbstractCfg + AbstractNode{pre,transfer,post}
                                  + TransferEffect + TransferFn (wp,sp) + PointerEnv
                                  + SourceLocation re-export from source.
src/analysis/node_summary.rs      NodeSummary{node,reach,state} with combined()
                                  short-circuit on False.
src/analysis/adapter.rs           FunctionGraph -> AbstractCfg + AssertionSite[]
                                  + ReturnSummary + CallSummaryRegistry
                                  + compute_return_summary + collect_callee_names.
src/analysis/oracle.rs            Oracle{feasibility,feasibility_with_model,implies,
                                  check_summary}. No loop-invariant API.
src/analysis/rules.rs             RuleEngine{init,must_post,notmay_pre,verified,
                                  bugfound} + Judgement{Verified,BugFound{model},Unknown}.
src/analysis/backward.rs          analyze(cfg,site,oracle) -> AssertionResult; render_result.
src/analysis/summaries.rs         NotMaySummary, MustSummary, SummaryTables (unused stub).
src/analysis/providers.rs         CandidateProvider trait + NoProvider + ManualProvider.
src/analysis/driver.rs            analyze_function_graph, analyze_module,
                                  analyze_module_with_provider, ProcedureReport,
                                  SafetyVerdict{Safe,Unsafe,Unknown}.
```

## 2. abstract_cfg.rs

Imports: `Formula, Memory, Term, Var` from `formula`, `BTreeMap, BTreeSet, HashMap`,
`fmt`, `thiserror::Error`.

Types:
- `CfgNodeId(pub usize)`, `CfgEdgeId(pub usize)` — Copy/Hash/Ord/Default.
- `SourceLocation { file: String, line: u32, column: u32 }` with `new`, `Display`,
  and `From<source::SourceLocation>` impl.
- `CallMemoryEffect { PreservesMemory, HavocMemory }`.
- `AssignValue { Term(Term), Predicate(Formula) }`.
- `TransferEffect`:
  - `Assign { target: Var, value: AssignValue }`
  - `Alloca { target: String, region: String }`
  - `GetElementPtr { target: String, base: String, offset: Term }`
  - `Load { target: Var, source: String }`
  - `Store { target: String, value: Term }`
  - `MemoryStore { region: String, offset: Term, value: Term }` — resolved store
  - `Assume(Formula)`
  - `Obligation(Formula)`
  - `Nop`
  - `Call { callee: String, memory_effect: CallMemoryEffect }`
- `TransferFn { effects: Vec<TransferEffect> }`. Methods:
  - `new(effects)`, `identity() = default`, `is_identity()`.
  - `wp(post: &Formula) -> Formula`: fold effects in REVERSE order through `wp_one`.
  - `sp(pre: &Formula) -> Formula`: fold effects FORWARD through `sp_one`.
  - `pointer_resolution() -> PointerEnv`: walk effects, bind Alloca and GEP into env.
- `PointerEnv { bindings: HashMap<String, PointerBinding> }` with `bind`, `get`.
  `PointerBinding { region: String, offset: Term }`.
- `NodeKind { Entry, Normal, Exit, SyntheticExit }`.
- `AbstractNode { id, label, kind, source_location, transfer, pre: Formula,
  post: Formula }`. pre/post init True; analysis mutates.
- `AbstractEdge { id, source, target, guard: Formula, effects: Vec<TransferEffect> }`
  with `transfer() -> TransferFn::new(effects.clone())`.
- `AbstractCfg { nodes: BTreeMap<CfgNodeId, AbstractNode>, edges: BTreeMap, entry,
  concrete_exits: BTreeSet, exit: Option, next_node, next_edge }`. Methods:
  - `new(entry_label)` inserts node id 0 as Entry with identity transfer.
  - `entry()`, `exit()`, `node(id)`, `node_mut(id)`, `edge(id)`, `nodes()`,
    `edges()`, `node_ids()`, `edge_ids()`.
  - `add_node(label, transfer) -> CfgNodeId`.
  - `set_entry_transfer(transfer)`.
  - `set_source_location(id, loc)`.
  - `mark_exit(id)`: sets kind=Exit if not entry, adds to concrete_exits.
  - `add_edge(source, target, guard, effects) -> CfgEdgeId`.
  - `append_edge_effects(id, effects)`.
  - `successors`, `predecessors`, `outgoing_edges`, `incoming_edges`.
  - `ensure_single_exit() -> CfgNodeId`: if 1 concrete exit -> use it; if many ->
    add `__synthetic_exit` (SyntheticExit kind, identity transfer) with trivial-True
    edges from each real exit; if 0 -> Err(MissingExit).
  - `topological_order() -> Option<Vec<CfgNodeId>>`: Kahn's algorithm; returns None
    on cycle.
- `CfgError { UnknownNode{id}, UnknownEdge{id}, MissingExit }`.

`wp_one(effect, post)`:
- `Nop`, `Alloca`, `GetElementPtr`, `Call`, `Load`, `Store` -> post.clone()
  (Load/Store are no-ops because the resolution pre-pass rewrites them to
  Assign(Select(...)) and MemoryStore; unresolved fall-throughs are sound but
  weak).
- `Assign{target, value}` -> substitute target in post; for `AssignValue::Term`
  use `substitute_var_in_formula(target, term, post)`; for `AssignValue::Predicate`
  use `substitute_bool_var_in_formula(target, predicate, post)`.
- `Assume(c)` -> `Formula::implies(c, post)`.
- `Obligation(c)` -> `Formula::and(c, post)`.
- `MemoryStore{region, offset, value}` -> substitute Memory::Var(region) in post
  with Memory::store(Memory::var(region), offset, value), via
  `substitute_memory_var_in_formula`.

`sp_one(effect, pre)`:
- `Nop`, all memory/pointer effects -> pre.clone().
- `Assign{target, AssignValue::Term(t)}` -> `pre ∧ (target == t)`.
- `Assign{target, AssignValue::Predicate(p)}` -> `pre ∧ (target ⇔ p)`.
- `Assume(c)`, `Obligation(c)` -> `pre ∧ c`.

Substitution helpers walk Formula/Term/Memory recursively. Provide:
- `substitute_var_in_formula(target: &Var, replacement: &Term, formula) -> Formula`
- `substitute_var_in_term(target, replacement, term) -> Term`
- `substitute_var_in_memory(target, replacement, memory) -> Memory`
- `substitute_bool_var_in_formula(target, replacement: &Formula, formula) -> Formula`
- `substitute_memory_var_in_formula(region: &str, replacement: &Memory, formula) -> Formula`
- `substitute_memory_var_in_term`, `substitute_memory_var_in_memory`.

For numeric atoms `Eq/Lt/Le/Gt/Ge`, substitute_bool_var_in_formula clones unchanged
(numeric assignments don't reach boolean carriers there).

Tests: wp of assignment substitutes; wp of Assume gives implication; wp of
Obligation gives conjunction; wp composes in REVERSE order; sp of assignment
adds equality; topological_order accepts DAGs and rejects cycles; synthetic
exit for multi-exit; pointer_resolution chains Alloca+GEP.

## 3. node_summary.rs

```rust
NodeSummary { node: CfgNodeId, reach: Formula, state: Formula }
NodeSummary::unreachable(node) = { reach: False, state: False }
NodeSummary::entry(node)       = { reach: True,  state: False }
combined() = if reach==False || state==False { False } else { Formula::and(reach, state) }
join_reach(&Formula) = reach |= incoming  (uses Formula::or)
join_state(&Formula) = state |= incoming
```

## 4. oracle.rs

```rust
Feasibility { Feasible, Infeasible, Unknown }
Validity    { Valid,    Invalid,    Unknown }
FeasibilityReport { feasibility: Feasibility, model: Option<SmtModel> }
Oracle (default unit struct)
OracleError { Formula(#[from] FormulaError) }

Oracle::new() -> Self
Oracle::feasibility(formula) = drop the model from feasibility_with_model.
Oracle::feasibility_with_model(formula):
    let scope = SmtScope::new(); scope.assert_formula(formula)?;
    match scope.check() {
        Sat -> Feasible + scope.model_bindings(),
        Unsat -> Infeasible + None,
        Unknown -> Unknown + scope.model_bindings(),
    }
Oracle::check_summary(NodeSummary) = feasibility_with_model(summary.combined()).
Oracle::implies(assumptions, conclusion):
    let counterexample = assumptions ∧ ¬conclusion;
    feasibility(counterexample) -> Valid (Unsat) / Invalid (Sat) / Unknown.
```

No `check_initiation`/`check_inductiveness`/`check_post`/`verify_invariant` — those
belong to the loop milestone.

## 5. rules.rs

```rust
Judgement { Verified, BugFound { model: Option<SmtModel> }, Unknown }
RuleError { UnknownEdge{edge}, UnknownNode{node}, Oracle(#[from] OracleError) }

RuleEngine<'a> { cfg: &'a AbstractCfg, summaries: BTreeMap<CfgNodeId, NodeSummary> }
RuleEngine::new(cfg)
RuleEngine::cfg(), summaries(), summary(id), summary_mut(id)

init():
    for each id in cfg.node_ids():
        summaries[id] = if id == entry { NodeSummary::entry(id) } else { NodeSummary::unreachable(id) };

set_state(node, formula): summaries[node].state = formula.

must_post(edge_id):  // forward path-condition propagation
    let edge = cfg.edge(edge_id)?.clone();
    let propagated = summaries[edge.source].reach ∧ edge.guard;
    summaries[edge.target].join_reach(&propagated);

notmay_pre(edge_id):  // backward state propagation; state is PRE-state at node
    let edge = cfg.edge(edge_id)?.clone();
    let target_state = summaries[edge.target].state.clone();        // pre at m
    let edge_pre = edge.transfer().wp(&target_state);                // wp through edge
    let post_at_source = edge.guard ∧ edge_pre;                      // post at n
    let pre_at_source = cfg.node(edge.source)?.transfer.wp(&post_at_source);
    summaries[edge.source].join_state(&pre_at_source);

verified(entry, oracle) -> bool: oracle.check_summary(&summaries[entry]).feasibility == Infeasible.
bugfound(entry, oracle) -> Option<Option<SmtModel>>:
    match oracle.check_summary(...) { Feasible -> Some(model), _ -> None }.
```

## 6. backward.rs

```rust
AssertionResult { site_id, site_label, judgement, entry_summary, assertion_summary }
BackwardError { CyclicCfgUnsupported, Rule(RuleError), Oracle(OracleError) }

analyze(cfg, site, oracle):
    let order = cfg.topological_order().ok_or(CyclicCfgUnsupported)?;
    let mut engine = RuleEngine::new(cfg); engine.init();
    // forward must_post over outgoing edges, topo order
    for n in &order { for e in cfg.outgoing_edges(*n) { engine.must_post(e)?; } }
    // seed assertion: state[node] = wp(node.transfer)(¬obligation)
    let neg = Formula::not(site.obligation.clone());
    let pre_at_assertion = cfg.node(site.node)?.transfer.wp(&neg);
    engine.set_state(site.node, pre_at_assertion)?;
    // backward notmay_pre over incoming edges, REVERSE topo order
    for n in order.iter().rev() { for e in cfg.incoming_edges(*n) { engine.notmay_pre(e)?; } }
    // decide
    let bug = engine.bugfound(cfg.entry(), oracle)?;
    let judgement = if let Some(model) = bug { BugFound{model} }
                    else if engine.verified(cfg.entry(), oracle)? { Verified }
                    else { Unknown };
    Ok(AssertionResult { ... entry_summary, assertion_summary })

render_result(&AssertionResult) -> String:
    "  assertion #N (label)\n    reach: <entry_summary.reach>\n    state: <entry_summary.state>\n
     judgement: Verified|Unknown|BugFound\n    [for BugFound: model lines]"
```

## 7. summaries.rs

```rust
type ProcedureName = String;
NotMaySummary { precondition: Formula, postcondition: Formula }   // Hash+Eq
MustSummary  { precondition: Formula, postcondition: Formula }    // Hash+Eq
SummaryTables { notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
                must:   BTreeMap<ProcedureName, Vec<MustSummary>> }
methods: new, init_notmay, init_must, notmay(name)->&[..],
         must(name)->&[..], add_notmay(name, summary)->bool (dedup),
         add_must(name, summary)->bool (dedup).
```

Carrier only; not yet consumed by any driver.

## 8. providers.rs

```rust
LoopContext { function: String, loop_id: usize }   // placeholder

trait CandidateProvider {
    fn function_summary(&self, callee: &str) -> Option<ReturnSummary> { None }   // TRUSTED
    fn loop_invariant(&self, ctx: &LoopContext) -> Vec<Formula> { Vec::new() }   // CANDIDATE
}

NoProvider;          impl CandidateProvider for NoProvider {}
ManualProvider { function_summaries: BTreeMap<String, ReturnSummary> }
ManualProvider::new, with_function_summary(builder), add_function_summary,
function_summaries() getter.
impl CandidateProvider for ManualProvider {
    fn function_summary(&self, callee) -> Option<ReturnSummary> {
        self.function_summaries.get(callee).cloned()
    }
}
```

Tests: NoProvider returns nothing; ManualProvider returns inserted summary;
ManualProvider misses unknown callees.

## 9. adapter.rs (LLVM lowering)

### Public types

```rust
AdaptedProcedure { name, cfg: AbstractCfg, assertions: Vec<AssertionSite>,
                   instruction_nodes: HashMap<Instruction, CfgNodeId> }
AssertionSite { id, node, source_location, location, obligation: Formula }
ReturnSummary { function, formal_parameters: Vec<String>, retval_name: String,
                relation: Formula }
CallSummaryRegistry { summaries: BTreeMap<String, ReturnSummary>,
                      next_call_site: Cell<usize> }
    new, insert(summary), get(callee)->Option<&>, is_empty,
    next_call_site_id() -> usize  (interior mutability)
AdapterError { MissingStart, MissingExit, UnsupportedFloatingPointInstruction,
               UnsupportedInstruction, UnsupportedValue, PhiPredecessorMismatch,
               Cfg(String) }
```

### Public functions

```rust
adapt(graph) = adapt_with_purity(graph, &empty)
adapt_with_purity(graph, memory_pure) = adapt_with_purity_and_summaries(graph, memory_pure, &empty registry)
adapt_with_purity_and_summaries(graph, memory_pure, summaries) -> AdaptedProcedure
infer_memory_pure_functions(graphs) -> BTreeSet<String>   (unchanged from old impl)
collect_callee_names(graphs) -> BTreeSet<String>          (walk Call insts)
compute_return_summary(graph, &AdaptedProcedure) -> Option<ReturnSummary>
```

### local_name / synthetic_retval_name

CRITICAL: every variable in a function's formula gets prefixed with `<funcname>$`
so cross-procedure summaries don't collide on `%0`/`%1`/...

```rust
local_name(function_name, instruction) = format!("{function_name}${}", instruction.display_name())
synthetic_retval_name(function_name)   = format!("{function_name}$__retval")
```

`assigned_var`, `lower_numeric_value`, `lower_integer_value`, `lower_bool_value`,
`pointer_name`, `lower_gep_offset` ALL take `function_name: &str` and use
`local_name`. Phi-edge effects, edge guards, and assertion lowering also thread
function_name.

### adapt_with_purity_and_summaries (sketch)

```
function_name = &graph.name
start = graph.start.ok_or(MissingStart)?
allocation_regions = walk graph.vertices: alloca_inst -> "<funcname>$stack<N>"
cfg = AbstractCfg::new(start.print())
cfg.set_entry_transfer(lower_node_transfer(funcname, start, ...))
instruction_nodes[start] = cfg.entry()
attach source_location

for each instruction != start in graph.vertices:
    transfer = lower_node_transfer(funcname, instr, memory_pure, allocation_regions, summaries)
    id = cfg.add_node(instr.print(), transfer)
    instruction_nodes[instr] = id; attach source_location

for each exit in graph.end: cfg.mark_exit(instruction_nodes[exit])

for each (source, node) in graph.edges:
    for target in node.successors:
        guard = lower_edge_guard(funcname, source, target)
        edge_id = cfg.add_edge(insts[source], insts[target], guard, vec![])
        edge_ids[(source,target)] = edge_id

lower_phi_edge_effects(funcname, graph, &mut cfg, &edge_ids)
let assertions = lower_assertions(funcname, graph, &mut cfg, &instruction_nodes)
cfg.ensure_single_exit()
resolve_memory_effects(&mut cfg)   // Load/Store -> Assign(Select)/MemoryStore
return AdaptedProcedure { name, cfg, assertions, instruction_nodes }
```

### lower_node_effects per opcode (function_name threaded)

- Add/Sub/Mul/SDiv/UDiv: Assign(target, AssignValue::Term(arith)).
- ICmp: Assign(target, AssignValue::Predicate) with predicate from `==,!=,>,>=,<,<=`;
  `!=` is `Not(Eq)`.
- And/Or/Xor (Bool only): Assign(Predicate). Xor lowers to (l∧¬r)∨(¬l∧r).
- Alloca: Alloca{target, region from allocation_regions}.
- Load: Load{target, source: pointer_name(operand0)}.
- Store: Store{target: pointer_name(op1), value: lower_integer_value(op0)}.
- GetElementPtr: GetElementPtr{target, base, offset = sum of operands[1..]}.
- PHI / Br -> None (phi handled as edge effect; Br produces guard only).
- Ret:
  ```
  if let Some(ret_value) = inst.get_operand(0):
      if Sort::Int:
          push Assign{target = Var::int(synthetic_retval_name(funcname)),
                      value = AssignValue::Term(lower_numeric_value(funcname, ret_value))}
  None
  ```
  Effects pushed BEFORE returning None (use `&mut effects` accumulator).
- Call:
  ```
  let callee = inst.get_called_function()?;
  if callee == "may_assert": None
  else:
      push Call{callee, memory_effect: PreservesMemory if pure else HavocMemory};
      if let Some(assume) = summary_assume_for_call(funcname, inst, &callee, summaries)?:
          push assume;
      None
  ```
- F* opcodes -> UnsupportedFloatingPointInstruction.
- default -> UnsupportedInstruction.

### lower_edge_guard

Br with condition: lookup successors[0]/[1]; if target is successors[0], guard
= lower_bool_value(condition); if successors[1], guard = !lower_bool_value(condition);
no condition -> True. Switch/IndirectBr/Invoke -> Unsupported.

### lower_phi_edge_effects

For each PHI: target = assigned_var(funcname, phi); for each (incoming_block,
incoming_value): find edge whose source's parent block == incoming_block AND
target instruction == phi; push Assign(target, value) onto that edge's effects
(Predicate for Bool, Term for Int/Real).

### lower_assertions

```
for each (index, site) in graph.asserts.iter().enumerate():
    let node = choose_assert_node(site, instruction_nodes).ok_or(MissingStart)?;
    let asserted = lower_bool_value(funcname, site.asserted_value)?;
    sites.push(AssertionSite { id: index+1, node,
        source_location: site.source_location.into(),
        location: assertion_location(site),
        obligation: asserted });
    // CRITICAL: do NOT push Obligation onto node's transfer; engine seeds
    // state[node] = wp(node.transfer)(¬obligation) directly.
```

`choose_assert_node` tries `asserted_value` -> `predecessor` -> `successor` from
the AssertSite. `assertion_location` formats "after <pred>" / "before <succ>" /
the asserted-value text.

### resolve_memory_effects (function-wide pointer pre-pass)

```
let order = cfg.topological_order(); if None: return  // cycles: leave Load/Store symbolic
let mut env = PointerEnv::default()
for node_id in order:
    let mut rewritten = Vec::new()
    for effect in node.transfer.effects.drain(..):
        match effect {
            Alloca{target,region}: env.bind(target, region, Term::int(0)); push Alloca.
            GEP{target,base,offset}: if env has base, env.bind(target, parent.region, parent.offset + offset); push GEP.
            Load{target,source}: if env has source: push Assign(target, Select(Memory::var(region), offset))
                                 else: push original Load.
            Store{target,value}: if env has target: push MemoryStore{region, offset, value}
                                 else: push original Store.
            other: push as-is.
        }
    node.transfer.effects = rewritten
```

### compute_return_summary (BACKWARD wp, not forward sp)

```
order = cfg.topological_order()?;  exit = cfg.exit()?
retval_name = synthetic_retval_name(procedure.name)
retval_obs_name = format!("{retval_name}$obs")

state[*] = False
// CRITICAL: seed POST-state at exit, then wp through exit's own transfer to
// get pre-state. For the single-ret case (no synthetic exit), the ret node IS
// the exit and its transfer carries Assign(__retval, ret_value); wp converts
// "post: __retval == __retval$obs" into "pre: ret_value == __retval$obs".
let post_at_exit = (Var::int(retval_name) == Var::int(retval_obs_name))
state[exit] = cfg.node(exit).transfer.wp(&post_at_exit)

for node in order.iter().rev():
    for edge_id in cfg.incoming_edges(*node):
        // notmay_pre style: state[source] |= wp(source.transfer)(guard ∧ wp(edge.transfer)(state[target]))
        let edge_pre = edge.transfer().wp(&state[edge.target])
        let post_at_source = edge.guard ∧ edge_pre
        let pre_at_source = cfg.node(edge.source).transfer.wp(&post_at_source)
        state[edge.source] = state[edge.source] ∨ pre_at_source

let entry_state = state[cfg.entry()]
// Rename __retval$obs back to __retval so call sites can substitute.
let relation = rename_vars_in_formula(entry_state, |name|
    if name == retval_obs_name { retval_name } else { name })
if !formula_contains_var(&relation, &retval_name): return None
Some(ReturnSummary { function, formal_parameters: formal_parameter_names(graph, name),
                     retval_name, relation })

formal_parameter_names(graph, funcname) = graph.params.iter().map(|p| format!("{funcname}${p}")).collect()
formula_contains_var, term_contains_var: recursive walk of Formula/Term checking Var name == target.
```

### summary_assume_for_call (called from Call lowering)

CRITICAL: this is `Obligation(R)`, NOT `Assume(R)`. Conjunctive semantics
(wp(Obligation(R))(post) = R ∧ post) is what makes the summary actually
constrain the failure path. Implication semantics (wp(Assume(R))(post) =
R ⇒ post) lets Z3 satisfy by violating R, defeating the summary.

```
fn summary_assume_for_call(caller, instruction, callee, summaries)
    -> Result<Option<TransferEffect>, AdapterError>
{
    let summary = summaries.get(callee).cloned()?;   // Ok(None) if absent
    let mut mapping: BTreeMap<String, String>;
    let actual_args = instruction.get_call_args();
    for (formal, actual) in summary.formal_parameters.iter().zip(actual_args.iter()):
        if actual.as_constant_int().is_some(): continue   // handled below
        else: mapping.insert(formal.clone(), local_name(caller, *actual))
    mapping.insert(summary.retval_name.clone(), local_name(caller, instruction))   // LHS

    let call_site_id = summaries.next_call_site_id()
    let local_prefix = format!("{caller}$call{call_site_id}")
    let renamed = rename_callee_vars(&summary.relation, &mapping, &summary.function, &local_prefix)

    // Constant args: literal substitution by variable name.
    let mut substituted = renamed
    for (formal, actual) in zip:
        if let Some(constant) = actual.as_constant_int():
            substituted = substitute_var_name_with_term(&substituted, formal, &Term::int(constant))

    Ok(Some(TransferEffect::Obligation(substituted)))
}

rename_callee_vars(formula, mapping, callee_name, local_prefix):
    rename_vars_in_formula(formula, |name|
        if let Some(t) = mapping.get(name): return t.clone();
        let cp = format!("{callee_name}$");
        if name starts with cp: format!("{local_prefix}${suffix}")
        else: name.to_string())
```

`rename_vars_in_formula`, `rename_vars_in_term`, `rename_vars_in_memory` walk
recursively, building new Formula/Term/Memory with renamed Var/Memory::Var.
`Var::new(new_name, var.sort())` preserves the sort.

`substitute_var_name_with_term` and friends: for each Var with matching name,
replace with the term (Term::Int(...) for constant args).

### Key invariants

1. Every variable in a function's formula is `<funcname>$<llvm_display_name>`.
2. Memory regions are also prefixed: `<funcname>$stack<N>` from allocation_regions.
3. Per-call-site rename uses `<caller>$call<N>$<suffix>` for callee locals
   (including memory regions) other than formals and __retval. Three calls to
   the same function from the same caller get suffixes call0, call1, call2.
4. Summary application uses `Obligation` (conjunctive) not `Assume` (implicative).
5. compute_return_summary seeds state[exit] = wp(exit.transfer)(post-state),
   not the post-state directly, so the single-ret case works without a synthetic exit.

## 10. driver.rs

```rust
ProcedureReport { procedure: String, assertions: Vec<AssertionResult>,
                  failures: Vec<String> }
impl Display for ProcedureReport: writeln procedure, then render_result for each
    assertion, then "  unsupported: ..." for each failure.

SafetyVerdict { Safe, Unsafe, Unknown }     // Display: SAFE/UNSAFE/UNKNOWN
ProcedureReport::verdict():
    if !failures.is_empty(): Unknown
    if assertions.is_empty(): Safe
    walk: Verified ok; BugFound -> Unsafe; Unknown -> all_verified=false
    if all_verified: Safe else Unknown

DriverError { Adapter(#[from] AdapterError) }

analyze_function_graph(graph, oracle) =
    analyze_with_summaries(graph, &empty, &CallSummaryRegistry::new(), oracle)

analyze_module(graphs, memory_pure, oracle) =
    analyze_module_with_provider(graphs, memory_pure, &NoProvider, oracle)

analyze_module_with_provider(graphs, memory_pure, provider, oracle):
    let summaries = CallSummaryRegistry::new()
    // Phase 0: provider-supplied EXTERN summaries.
    let in_graph = graphs.iter().map(|g| &g.name).collect::<BTreeSet>()
    for callee in collect_callee_names(graphs):
        if in_graph.contains(&callee): continue
        if let Some(s) = provider.function_summary(&callee): summaries.insert(s)
    // Phase 1: bottom-up fixpoint over in-graph functions.
    for _ in 0..graphs.len().max(1):
        let snapshot = summaries.clone()
        for graph in graphs:
            adapted = adapt_with_purity_and_summaries(graph, memory_pure, &snapshot)?
            if let Some(s) = compute_return_summary(graph, &adapted): summaries.insert(s)
    // Phase 2: per-procedure analysis with the populated registry.
    let mut reports = Vec::new()
    for graph in graphs:
        reports.push(analyze_with_summaries(graph, memory_pure, &summaries, oracle)?)
    Ok(reports)

analyze_with_summaries(graph, memory_pure, summaries, oracle):
    adapted = if summaries.is_empty() && memory_pure.is_empty() { adapt(graph)? }
              else { adapt_with_purity_and_summaries(graph, memory_pure, summaries)? }
    let mut assertions = Vec::new(); let mut failures = Vec::new()
    for site in &adapted.assertions:
        match analyze(&adapted.cfg, site, oracle) {
            Ok(r) -> assertions.push(r),
            Err(CyclicCfgUnsupported) -> failures.push("assertion #{id} ({label}): CFG has a cycle; loops are not supported"),
            Err(other) -> failures.push("assertion #{id} ({label}): {other}"),
        }
    Ok(ProcedureReport { procedure: adapted.name, assertions, failures })

analyze_function_graph_with_purity(graph, memory_pure, oracle) =
    analyze_with_summaries(graph, memory_pure, &CallSummaryRegistry::new(), oracle)
```

## 11. main.rs

```rust
mod analysis; mod assertions; mod errors; mod expressions; mod llvm_utils; mod smt;

fn main():
    parse `<INPUT>` (required) and `--no-dot` flag with clap.
    init env_logger with default "info".
    initialize_target().
    let context = Context::new()
    let module = context.parse_bc_file(input).ok_or(exit 1)
    let graphs = generate_program_graph(&module).map_err(exit 1)?
    if dump_dot: dump_graphs(&graphs, &graph_output_dir(input))
    let memory_pure = analysis::adapter::infer_memory_pure_functions(&graphs)
    let oracle = analysis::oracle::Oracle::new()
    let reports = analysis::driver::analyze_module(&graphs, &memory_pure, &oracle)?
    for (graph, report) in graphs.zip(reports):
        println "Function {name}: {N} visible instructions, {M} assertion sites"
        println "{report}"
        println "  verdict: {verdict}"
    println "Module verdict: {Safe if all safe, Unsafe if any unsafe, else Unknown}"

graph_output_dir(input) = format!("graph_dot/{stem}", stem = file_stem of input or "graph")
```

No `--simple-check`, `--rule-check`, `--max-step`, `--trace-predicates`,
`--llm-invariants`, `--max-llm-calls`. No tokio runtime.

## 12. Verification

```sh
cargo fmt
cargo test -- --test-threads=1            # 64 tests, all pass
make -C tests ir
cargo run --bin main -- --no-dot tests/out/straight_line_assert.bc
# expect: assertion Verified, verdict SAFE
cargo run --bin main -- --no-dot tests/out/multi_exit.bc
# expect: both assertions Verified, verdict SAFE
cargo run --bin main -- --no-dot tests/out/loop_counter.bc
# expect: assertion unsupported (CFG has a cycle), verdict UNKNOWN
bash tests/build_ir.sh tests/paper_section2_fig1_not_may.c
cargo run --bin main -- --no-dot tests/out/paper_section2_fig1_not_may.bc
# expect: g SAFE, section2_example1_not_may SAFE, Module verdict: SAFE
```

## 13. What is intentionally absent

- `src/analysis/cfg.rs`, `state.rs`, `transfer.rs`, `llvm_adapter.rs`,
  `loops.rs` — DELETED, do not recreate.
- Any `--simple-check` / `max_step` / bounded explorer.
- Any LLM provider or async/tokio scaffolding.
- Loop invariants / loop summaries (next milestone).
- `oracle::check_initiation` etc. (loop milestone).
- Floating-point support.
- `switch` / `indirectbr`.

## 14. Test inventory (where 64 comes from)

- `formula.rs`: 6
- `oracle.rs`: 4
- `node_summary.rs`: 5
- `abstract_cfg.rs`: 10
- `summaries.rs`: 3
- `rules.rs`: 3
- `backward.rs`: 3
- `adapter.rs`: 5
- `driver.rs`: 4 (straightline, unconstrained-bug, callee-summary, extern-via-provider)
- `providers.rs`: 3
- `source.rs`: 2
- `smt::solver`: 4
- `assertions::translation`: 5
- `expressions::exp`: 3
- `llvm_utils::program_graph`: 4
- (sum: 64)
