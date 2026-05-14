# REPRODUCER
Reconstruct current repo state from this file only.

Assumption already available:
- `src/common/llvm_utils/llvm_wrap.rs`
- `src/common/llvm_utils/program_graph.rs`

You still need `src/common/llvm_utils/mod.rs`.

## Cargo

Use this exact package surface:

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
clap = {version = "4.5", features =["cargo"]}
thiserror = "2.0.16"
dot = "0.1.4"
chumsky = {features = ["pratt"], version = "0.11"}
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

Keep the `psm` pin comment about `ar_archive_writer` / Rust 1.88+.

## Tree

Create exactly:

```text
src/
  main.rs
  common/
    mod.rs
    errors.rs
    source.rs
    formula.rs
    abstract_cfg.rs
    adapter.rs
    oracle.rs
    transfer_effects_reference.md
    assertions/
      mod.rs
      translation.rs
    expressions/
      mod.rs
      exp.rs
    smt/
      mod.rs
      solver.rs
    llvm_utils/
      mod.rs
      llvm_wrap.rs              # assumed already present
      program_graph.rs          # assumed already present
  may_must_analysis/
    mod.rs
    node_summary.rs
    summaries.rs
    providers.rs
    rules.rs
    loops.rs
    llm_response_parser.rs
    llm_provider.rs
    chc.rs
    backward.rs
    driver.rs
    design.md
    analysis_flow.md
  absint_analysis/
    mod.rs
```

## Global invariants

- `common::oracle` is the only normal SMT entrypoint. `may_must_analysis::chc` also talks to Z3 fixedpoint directly for CHC/Spacer.
- `AbstractCfg` is the single carrier. `AbstractNode` owns `pre`, `transfer`, `post`.
- Rules consume only `NodeSummary { reach, state }`.
- Backward engine is primary. `state[n]` means pre-state at `n` that can lead to assertion violation.
- Branch conditions live on edges as guards, never in node transfer.
- Phi nodes lower to predecessor-specific edge effects, except pointer-typed phi which is handled by pointer binding resolution.
- `may_assert(c)` becomes `AssertionSite { obligation: c }`; do not bake that obligation into the node transfer.
- Variable names are namespaced with `<function>$...`.
- Summary inlining uses `$` as the structural separator.
- Prefer `Unknown` over unsound `Verified`.

## `src/main.rs`

Purpose: CLI entrypoint; always dispatch through `may_must_analysis::driver::analyze_module_with_llm`.

Exact constants:
- `DEFAULT_LLM_SCRIPT = "tools/llm_invariant.py"`
- `DEFAULT_LLM_MODEL = "gpt-5.3"`
- `DEFAULT_LLM_TRIES = 5`

Module declarations:
- `mod absint_analysis;`
- `mod common;`
- `mod may_must_analysis;`

CLI flags:
- positional `<INPUT>`
- `--no-dot`
- `--show-summaries`
- `--debug-invariants`
- `--llm-invariants`
- `--llm-tries <N>`
- `--llm-model <MODEL>`
- `--llm-script <PATH>`
- `--llm-force`
- `--llm-prompt-template <FILE>`
- `--inv-chc`
- `--inv-houdini`
- `--inv-template`

Behavior:
- init env_logger with default filter `info`; if `--debug-invariants`, set module `loop_invariant` to `Debug`.
- call `initialize_target()`.
- parse bitcode via `Context::new().parse_bc_file(input)`.
- build `graphs` via `generate_program_graph`.
- if dot enabled: `dump_graphs(&graphs, graph_output_dir(input))`, print `DOT graphs written to ...`.
- compute `memory_pure = common::adapter::infer_memory_pure_functions(&graphs)`.
- build `InvariantConfig`:
  - `methods` only from explicit `--inv-*` flags; if empty, downstream uses default `[Chc,Houdini,Template]`.
  - `llm` is `Some(LlmInvariantConfig)` when `--llm-invariants` or `--llm-force`.
  - `skip_algorithmic` hardcoded `false`.
- `llm_prompt_template` is file contents, not path.
- call `analyze_module_with_llm(&graphs, &memory_pure, &NoProvider, &oracle, &inv_config)`.

Printing:
- `print_module_report` prints one block per procedure:
  - header: `procedure <name>  [<assertions> assertion(s), <instruction_count> instruction(s)[ | <loop_count> loop(s)][ | recursive]]`
  - each assertion via `backward::render_result`
  - loop failure note string and recursion note string exactly as current code
  - verdict per procedure
- module verdict accumulation: `Unsafe` dominates `Unknown` dominates `Safe`
- if `--show-summaries`, print:
  - `[return summaries]` from `ModuleReport.computed_summaries`
  - `[must summaries]`
  - `[not-may summaries]`
- `print_summary` prints pretty-formatted return relation and write effects.
- `graph_output_dir("tests/out/foo.bc") -> "graph_dot/foo"`.

## `src/common/mod.rs`

Just export:
- `abstract_cfg`
- `adapter`
- `assertions`
- `errors`
- `expressions`
- `formula`
- `llvm_utils`
- `oracle`
- `smt`
- `source`

## `src/common/errors.rs`

`ProgError`:
- `GraphError(Instruction, String)` with display using `inst.print()`
- `NoDefinitionForGraph(String)`
- `IOError(std::io::Error)`
- `ParseError(String)`

Alias:
- `pub type Result<T> = std::result::Result<T, ProgError>;`

## `src/common/source.rs`

Standalone `SourceLocation { file:String, line:u32, column:u32 }`, `new`, `Display`.
Display omits `:column` when column is 0.

## `src/common/formula.rs`

Define:
- `Sort::{Bool, Int, Real}`
- `Var { name:String, sort:Sort }` with constructors `new/bool/int/real`, accessors `name`, `sort`
- `Rational { num:i64, den:i64 }` normalized by gcd, denominator always positive
- `Memory::{Var(String), Store(Box<Memory>, Box<Term>, Box<Term>)}`
- `Term::{Var(Var), Int(i64), Real(Rational), Select(Box<Memory>,Box<Term>), Add, Sub, Mul, Div, Neg}`
- `Formula::{True, False, Var(Var), Not(Box<Formula>), And(Vec<Formula>), Or(Vec<Formula>), Implies(Box<Formula>,Box<Formula>), Eq(Term,Term), Lt, Le, Gt, Ge}`
- `pub type Predicate = Formula`
- `FormulaError::{ExpectedBooleanSort, ExpectedNumericSort, ExpectedIntegerSort, MixedSorts}`
- `ModelValue::{Int(i64), Bool(bool), Real(Rational), ArrayDefault(Box<ModelValue>)}`
- `SmtModel { scalar:Vec<(Var,ModelValue)>, memory:Vec<(String,ModelValue)> }`

Important methods:
- `Memory::validate()`
- `Term::sort()`
- `Formula::bool_var/not/and_all/and/or_all/or/implies/iff/eq/lt/le/gt/ge/validate`
- `Formula::substitute(mapping: HashMap<Var,Var>)`: rename vars recursively in formulas/terms/memory
- `Formula::and_all` and `or_all`:
  - flatten nested same connective
  - dedup by `Vec::contains`
  - `True`/`False` short-circuit
- `SmtModel::is_empty()`
- `collect_select_indices(formula) -> Vec<i64>` collecting constant indices from every `Term::Select(_, Term::Int(c))`

Formatting:
- `Formula::Display`: `true`, `false`, `(!x)`, `(a && b)`, `(a || b)`, `(a => b)`, `(x == y)`, etc.
- `Memory::Display`: `(store mem idx val)`
- `Term::Display`: infix arithmetic, `(select mem idx)`, `(-t)`
- `SmtModel::Display`: one `(define-fun ...)` per line; memory sort string is `(Array Int Int)`.

## `src/common/abstract_cfg.rs`

Define:
- `CfgNodeId(pub usize)`, `CfgEdgeId(pub usize)`
- duplicate local `SourceLocation` struct + `From<crate::common::source::SourceLocation>`
- `CallMemoryEffect::{PreservesMemory, HavocMemory}`
- `AssignValue::{Term(Term), Predicate(Formula)}`
- `TransferEffect` variants:
  - `Assign { target:Var, value:AssignValue }`
  - `Alloca { target:String, region:String }`
  - `GetElementPtr { target:String, base:String, offset:Term }`
  - `Load { target:Var, source:String }`
  - `Store { target:String, value:Term }`
  - `MemoryStore { region:String, offset:Term, value:Term }`
  - `PointerStore { target_slot:String, value_ptr:String }`
  - `PointerLoad { target_ptr:String, source_slot:String }`
  - `Assume(Formula)`
  - `Obligation(Formula)`
  - `Nop`
  - `Call { callee:String, memory_effect:CallMemoryEffect }`
- `TransferFn { effects: Vec<TransferEffect> }`
- `PointerEnv` with `HashMap<String, PointerBinding>`
- `PointerBinding { region:String, offset:Term }`
- `NodeKind::{Entry, Normal, Exit, SyntheticExit}`
- `AbstractNode { id,label,kind,source_location,transfer,pre,post }`
- `AbstractEdge { id,source,target,guard,effects }`
- `AbstractCfg { nodes, edges, entry, concrete_exits, exit, next_node, next_edge }`
- `CfgError::{UnknownNode, UnknownEdge, MissingExit}`

Methods:
- `TransferFn::new/identity/is_identity/wp/sp/pointer_resolution`
- `PointerEnv::bind/get`
- `AbstractEdge::transfer()`
- `AbstractCfg::new`, `entry`, `exit`, `node`, `node_mut`, `edge`, `nodes`, `edges`, `node_ids`, `edge_ids`, `add_node`, `set_entry_transfer`, `set_source_location`, `mark_exit`, `add_edge`, `append_edge_effects`, `successors`, `predecessors`, `outgoing_edges`, `incoming_edges`, `ensure_single_exit`, `topological_order`, `topological_order_excluding`, `detect_back_edges`

WP/SP semantics:
- `Assign(Term)` => substitute target var in formulas/terms/memory
- `Assign(Predicate)` => substitute bool var in formulas
- `Assume(c)` => `c => post` in wp; `pre && c` in sp
- `Obligation(c)` => `c && post` in wp; `pre && c` in sp
- `Alloca/GetElementPtr/PointerStore/PointerLoad` are bookkeeping; wp/sp no-op
- `Call` wp/sp no-op (`memory_effect` ignored)
- unresolved `Load` and `Store` are no-op in wp/sp
- `MemoryStore(region,offset,value)` wp substitutes `Memory::Var(region)` by `Memory::store(Memory::var(region), offset, value)`

Need helper substitution functions exactly as current code.

## `src/common/adapter.rs`

Types:
- `AdaptedProcedure { name, cfg, assertions, instruction_nodes }`
- `AssertionSite { id, node, source_location, location, obligation }`
- `WriteEffectSummary { param_index, ext_region_name, obs_name, relation }`
- `ReturnSummary { function, formal_parameters, retval_name, relation, write_effects }`
- `CallSummaryRegistry { summaries:BTreeMap<String,ReturnSummary>, next_call_site: Cell<usize> }`
- `AdapterError::{MissingStart, MissingExit, UnsupportedFloatingPointInstruction{instruction}, UnsupportedInstruction{instruction}, UnsupportedValue{value}, PhiPredecessorMismatch{instruction}, Cfg(String)}`

Exports:
- `adapt`
- `adapt_with_purity`
- `adapt_with_purity_and_summaries`
- `infer_memory_pure_functions`
- `collect_callee_names`
- `local_name`
- `synthetic_retval_name`
- `ext_region_name`
- `ext_obs_name`
- `compute_return_summary`
- `build_horn_model`

Adapt algorithm:
1. start from `FunctionGraph.start`
2. first visible instruction becomes CFG entry node transfer
3. every other visible instruction becomes one node
4. mark real exits from `graph.end`
5. add edges from `graph.edges` using `lower_edge_guard`
6. append phi edge effects via `lower_phi_edge_effects`
7. create `AssertionSite`s via `lower_assertions`
8. `ensure_single_exit`
9. `resolve_memory_effects`
10. `apply_pending_write_effects`

Instruction lowering:
- arithmetic opcodes `Add/Sub/Mul/SDiv/UDiv/FAdd/FSub/FMul/FDiv` -> `Assign(target, Term op)`
- `ICmp/FCmp` -> `Assign(target, Predicate)` using wrapper predicate strings `== != > >= < <=`
- bool `And/Or/Xor` only when result sort is Bool; `Xor` expands to `(lhs && !rhs) || (!lhs && rhs)`
- `Alloca` -> `TransferEffect::Alloca`
- `Load`:
  - pointer-typed load -> `PointerLoad`
  - else unresolved `Load`
- `Store`:
  - storing pointer value -> `PointerStore`
  - else unresolved `Store`
- `GetElementPtr` -> `GetElementPtr`
- `PHI`, `Br`, `Switch`, `IndirectBr` -> no node effect
- `Ret` captures only Int return values into synthetic `<func>$__retval`; non-int returns ignored
- `Call`:
  - `may_assert` => no transfer effect
  - else push `Call { callee, memory_effect }`
  - if summary available and call has trackable lhs, append summary effect from `summary_assume_for_call`
- `FNeg` -> numeric negation assign
- `FRem` unsupported float instruction error
- `SExt/ZExt/Trunc` -> identity numeric assignment
- `FPExt/FPTrunc/SIToFP/UIToFP/FPToSI/FPToUI` -> no-op approximation
- `BitCast/AddrSpaceCast` -> no-op approximation
- everything else unsupported

Edge guard lowering:
- conditional `Br`: true edge uses lowered condition; false edge uses `!condition`
- `Switch`: per-target equality disjunction; default is conjunction of inequality-to-all-cases
- `IndirectBr`: all listed destinations `Formula::True`
- `Invoke`: unsupported
- all other terminators: `Formula::True`

Phi lowering:
- non-pointer phi only
- append predecessor-specific `Assign` effect to matching incoming edge
- pointer phi skipped here; resolved later only if all incoming bindings agree exactly

Assertions:
- `choose_assert_node` order: asserted value node -> predecessor node -> successor node
- `location` string: `after <pred>` or `before <succ>` or asserted value label
- obligation stored only on `AssertionSite`

Naming helpers:
- `local_name(function, instruction) = format!("{function}${}", instruction.display_name())`
- `synthetic_retval_name(function) = "{function}$__retval"`
- external regions: `"{function}$__ext_{k}"`; obs: `"{function}$__ext_{k}_obs"`

Pointer/memory resolution:
- seed pointer params to external regions at offset 0 using `graph.pointer_param_indices`
- traverse topological order excluding back-edges
- `Alloca` binds `(region,0)`
- `GetElementPtr` extends offset by `Term::add`
- `PointerStore` records slot-region -> stored pointer name and rewrites effect to `Nop`
- `PointerLoad` follows alias chain through slot-region and rewrites effect to `Nop`
- `Load` from bound pointer rewrites to `Assign(target, Select(Memory::var(region), offset))`
- `Store` to bound pointer rewrites to `MemoryStore`
- unresolved ones stay symbolic
- afterwards resolve pointer phi bindings only for unanimous identical incoming bindings

Memory purity:
- `infer_memory_pure_functions` iteratively shrinks set of graphs preserving memory
- `preserves_memory` rejects any store through non-local pointer or call to non-memory-pure callee
- `infer_local_pointer_names` derives local pointers from `alloca`, GEP of local pointer, pointer phi whose incomings are all local

Summary insertion at call sites:
- `summary_assume_for_call` returns `TransferEffect::Obligation`, not `Assume`
- map callee formals to caller actual names, retval to caller lhs, other callee locals to per-call-site prefix `<caller>$call<id>$...`
- substitute constant actual args as `Term::int(constant)`
- write-effect summaries also become appended `TransferEffect::Obligation`s after resolving actual pointer args through final `PointerEnv`; use prefix `<caller>$wcall<id>$...`

Return summary inference:
- `compute_return_summary` is backward-WP based, not SP-based
- require acyclic cfg and exit
- seed exit postcondition `(__retval == __retval$obs)` then apply exit node wp
- backward propagate through incoming edges in reverse topo order
- rename `retval_obs` back to `retval`
- return `None` if resulting relation does not mention retval
- `formal_parameters` are `graph.params` prefixed with function name
- `write_effects` come from separate backward pass per pointer param, seeding `select(ext_region,0) == obs`

`build_horn_model`:
- uses `compute_return_summary`
- collects non-`may_assert`, non-`llvm.*` call refs whose result var actually appears in summary formula
- param sorts all `Int`
- call actual args only from `lower_numeric_value(...).ok()`
- `result_sort` hardcoded `Sort::Int`

## `src/common/oracle.rs`

Define:
- `Feasibility::{Feasible, Infeasible, Unknown}`
- `Validity::{Valid, Invalid, Unknown}`
- `FeasibilityReport { feasibility, model }`
- `Oracle`
- `OracleError::Formula(FormulaError)`

Methods:
- `new`
- `feasibility`
- `feasibility_with_model`: build `SmtScope`, assert formula, use `collect_select_indices`, treat `Sat` and `Unknown` as model-eligible
- `check_summary(summary)` => solver on `summary.combined()`
- `implies(assumptions, conclusion)` => check `assumptions && !conclusion`
- `check_chc_property(model, callee_models, property)` => build `ChcSession` and query it

## `src/common/smt/solver.rs`

Define `SmtScope { solver, bool_vars, int_vars, real_vars, memory_vars }`.

Behavior:
- `new` creates Z3 `Solver`, sets 3000ms timeout param
- `assert_formula` validates formula then lowers and asserts
- `check`
- `model_string`
- `model_bindings(extra_indices)`:
  - scalars for all registered bool/int/real vars
  - arrays probed at index 0 plus all `extra_indices`
  - if all probed values same => `memory.push((region, ArrayDefault(Int(v))))`
  - else emit per-index scalar vars named `region[idx]`
- `reset`
- expose `formula_to_z3` and `term_to_z3_int`
- free `quick_sat_check(Bool) -> SatResult`

Lowering:
- bool vars by `Bool::new_const`
- int vars by `Int::new_const`
- real vars by `Real::new_const`
- memory vars are `Array Int Int`
- `Term::Select` always lowers to Int
- Int/Real mixes error with `FormulaError::MixedSorts`
- `Memory::Store` lowers to array store

## `src/common/assertions/mod.rs`

Exact shim:
- `pub mod exp { pub use crate::common::expressions::exp::*; }`
- `pub mod translation;`

## `src/common/assertions/translation.rs`

Types:
- `type SortSeeds = BTreeMap<String, Sort>`
- `TranslatedStatement { func, predicate }`
- `TranslatedAssertion { name, stmt }`
- `TranslationError::{NonBooleanAtom, UnsupportedOperator, ExpectedArithmeticExpr, UnsupportedBooleanTerm, NoSharedNumericSort, AmbiguousNumericSort, SeedConflict{name,expected,actual}, MixedNumericContext, InvalidIntegerLiteral, InvalidRealLiteral}`

Behavior:
- translate assertion/frontend AST to `Formula`
- bare identifiers in boolean position default to Bool unless seed says otherwise; seeded non-Bool there is error
- arithmetic only allowed in numeric contexts
- equality/comparisons infer numeric sort from operand candidate sets
- if intersection has both Int and Real and either side contains arithmetic, choose `Int`; else ambiguity error
- literals with `.` force Real candidate set
- real literals parse to `Rational`

## `src/common/expressions/mod.rs`

Single line: `pub mod exp;`

## `src/common/expressions/exp.rs`

Implements independent assertion language parser with chumsky Pratt parser.

AST/public types:
- `Op::{Plus,Minus,Div,Mult,LAnd,LOr,LNot,Gt,Ge,Lt,Le,Eeq,Arrow,Named}`
- `Expr::{Ident(String), Const(String), Binop(Box<Expr>,Op,Box<Expr>), Unop(Box<Expr>)}`
- `Statement { func:String, exp:Expr }`
- `Assertion { stmt:Statement, name:String }`

Grammar facts:
- assertion file line: `name :: function => expression`
- command-line parse prepends `cmdline :: `
- tokens:
  - `%`-prefixed idents
  - extended identifiers starting `[A-Za-z_]`, then `[A-Za-z0-9_$%]*`
  - numbers incl decimal
  - `&&`/`&`, `||`/`|`, `!`/`~`
- precedence:
  - unary not highest
  - `* /`
  - `+ -`
  - relational
  - equality
  - and
  - or
  - implication right-assoc

Exports:
- `parse_cmd_line(&str) -> Result<Assertion>`
- `parse_file(&str) -> Result<Vec<Assertion>>`

Parse errors:
- use Ariadne diagnostics
- `parse_failure_noret` exits process
- `parse_cmd_line` / `parse_file` return `ProgError::ParseError`

## `src/common/smt/mod.rs`

Single line: `pub mod solver;`

## `src/common/llvm_utils/mod.rs`

Export `llvm_wrap` and `program_graph` only.

## `src/absint_analysis/mod.rs`

Placeholder only. Doc comment says lattice-based issue checkers are on hold.

## `src/may_must_analysis/mod.rs`

Export:
- `backward`
- `chc`
- `driver`
- `llm_provider`
- `llm_response_parser`
- `loops`
- `node_summary`
- `providers`
- `rules`
- `summaries`

## `src/may_must_analysis/node_summary.rs`

`NodeSummary { node, reach, state }`

Methods:
- `unreachable(node)` => both false
- `entry(node)` => `reach=true`, `state=false`
- `combined()` => `False` if either side syntactic `False`, else `reach && state`
- `join_reach`, `join_state` => disjunctive merge

## `src/may_must_analysis/summaries.rs`

Types:
- `type ProcedureName = String`
- `NotMaySummary { precondition, postcondition }`
- `MustSummary { precondition, postcondition }`
- `SummaryTables { notmay, must, loop_invariants }`

Methods:
- `new`
- `init_notmay`
- `init_must`
- `notmay(&str) -> &[NotMaySummary]`
- `must(&str) -> &[MustSummary]`
- `add_notmay`, `add_must` with dedup by `Vec::contains`
- `set_loop_invariants(function, Vec<(CfgNodeId,Formula)>)`
- `get_loop_invariants(function) -> &[(CfgNodeId,Formula)]`
- `all_procedure_names()`

## `src/may_must_analysis/providers.rs`

Types:
- `LoopContext { function, loop_id }`
- trait `CandidateProvider` with defaults:
  - `function_summary(&self, callee) -> Option<ReturnSummary>`
  - `loop_invariant(&self, ctx) -> Vec<Formula>`
- `NoProvider`
- `ManualProvider { function_summaries }`

`ManualProvider` methods:
- `new`
- `with_function_summary`
- `add_function_summary`
- `function_summaries`

## `src/may_must_analysis/rules.rs`

Types:
- `Judgement::{Verified, BugFound{model:Option<SmtModel>}, Unknown}`
- `RuleError::{UnknownEdge, UnknownNode, Oracle(OracleError)}`
- `RuleEngine<'a> { cfg:&'a AbstractCfg, summaries:BTreeMap<CfgNodeId,NodeSummary>, blocked_edges:BTreeSet<CfgEdgeId> }`

Methods:
- accessors `cfg/summaries/summary/summary_mut/blocked_count/is_blocked`
- `block_edge`
- `init`
- `set_state`
- `must_post(edge)`:
  - skip blocked
  - `reach[target] |= reach[source] && guard`
- `notmay_pre(edge)`:
  - skip blocked
  - `state[source] |= wp_source(guard && wp_edge(state[target]))`
- `notmay_pre_pruned(edge, oracle)`:
  - run `notmay_pre`
  - if combined formula at source becomes infeasible, block edge and reset `state[source]=False`
- `notmay_pre_usesummary(edge, tables, oracle)`:
  - only applies when target node contains a `Call`
  - for each callee not-may summary:
    - require `reach[source] && precondition` feasible
    - require `state[target] => postcondition` valid
    - then block edge and reset `state[source]=False`
- `must_post_usesummary(edge, tables)`:
  - only applies when source node contains a `Call`
  - for each must summary, blindly `join_reach(postcondition)` into target reach; precondition currently ignored
- `run_to_fixpoint(order, tables, oracle)`:
  - iterate until blocked edge count stops growing or iterations exceed `|edges|+1`
  - forward pass: `must_post` then `must_post_usesummary`
  - backward pass reverse topo: `notmay_pre`, `notmay_pre_usesummary`, `notmay_pre_pruned`
- `verified(entry, oracle)` => combined infeasible
- `bugfound(entry, oracle)` => `Some(model)` only when combined feasible

Free helpers:
- `callee_of(node)` returns first non-`may_assert` call effect callee
- `edge_view(cfg,id)`

## `src/may_must_analysis/loops.rs`

Types:
- `LoopInfo { header, latch, back_edge, body, exit_edges, back_edge_guard, source_location }`
- `CounterInit::{Literal(i64), Variable(String), Unknown}`
- `type InnerInvariants<'a> = &'a [(CfgNodeId, Formula)]`
- `InvariantCheckResult::{Accepted, InitiationFailed, InductivenessFailed, ExitClosureFailed{exit_edge}}`

Exports:
- `fmt_loop_loc`
- `detect_loops`
- `algorithmic_candidates`
- `houdini_candidates`
- `chc_loop_invariant`
- `sort_innermost_first`
- `check_loop_invariant_verbose`
- `check_loop_invariant`

Loop detection:
- use `cfg.detect_back_edges()`
- body computed by backward BFS from latch to header
- exit edges are body->outside

Algorithmic candidates:
- inspect:
  - back-edge guard
  - header->body guards
  - exit-edge guards
  - predicate assignments in body (`AssignValue::Predicate`) and their negation
- extract counter/bound pairs from `<`, `<=`, and `!(>=)` patterns
- emit `counter >= 0`, `counter <= bound`, and conjunction
- also inspect assignments for `var := var +/- k` -> `var >= 0`, and `var := constant` -> `var >= constant`

Houdini candidates:
- constants = `{-1,0,1}` + ints from loop body assignments + ints from `header_wp`
- vars = all `Sort::Int` vars in provided sort map
- emit:
  - `v >= c`
  - `v <= c`
  - `v1 <= v2`
  - `v1 >= v2`
  - `v1 + 1 <= v2`
  - range conjunctions `v >= c1 && v <= c2` for `c1 < c2`

CHC loop helper:
- collect counter/bound pairs from guards and predicate assigns
- only handle Int counter and Int bound variable
- find memory region by looking for header `Assign(target, Term::Select(Memory::Var(region), _))`
- init from incoming non-body predecessor `MemoryStore(region,0,value)`
- increment from body `MemoryStore(region,0, select(region,0) +/- const)`
- continue guard hardcoded as `counter < bound`
- call `chc::solve_loop_chc`

Invariant checking:
- exclude all back-edges in nested scenarios
- initiation:
  - seed `!candidate` at header
  - backward WP to entry through non-back-edge DAG
  - require entry formula UNSAT
- normalize candidate by `cfg.node(header).transfer.wp(candidate)`
- inductiveness:
  - seed latch with wp(back_edge)(normalized_candidate)
  - ignore all edge guards inside body (treat as True)
  - seed inner headers with accepted inner invariants and stop propagation through their body
  - require `normalized_candidate => body_wp_at_header`
- exit-closure:
  - for every exit edge with non-false postcondition, require `(normalized_candidate && exit_guard && postcond)` UNSAT
- `check_loop_invariant_verbose` reruns to distinguish failure mode

Important current limitations encoded in code:
- CHC path returns `None` when init is a variable parameter (`CounterInit::Variable`)
- `find_counter_increment` scans whole body and can see inner loops too

## `src/may_must_analysis/llm_response_parser.rs`

Dedicated parser for LLM invariant text. Do not reuse assertion grammar.

Public:
- `ParseError::{Syntax(String), InvalidQuantifierRange{lo,hi}, SortMismatch(String), NonBooleanContext(String)}`
- `parse_invariant(input, seeds)`
- `parse_invariant_seeds(input, &SortSeeds)`

Grammar support:
- identifiers with `$` and `%`
- integer literals only (unary `-` handled at parse level)
- `true/false`
- `!=`, `=>`, `<=>`
- bounded quantifiers:
  - `forall x in LO..HI. body`
  - `exists x in LO..HI. body`
  - expand statically over half-open range `[lo, hi)`
  - empty forall -> `true`, empty exists -> `false`

Precedence:
- `<=>` lowest, then `=>`, `||`, `&&`, `==/!=`, relations, `+/-`, `*//`, prefix `!/-`

Lowering:
- bare var in boolean context must be Bool-sorted or defaults Bool
- equality/comparison sort is `pick_numeric_sort` using first seeded Int/Real identifier else Int
- `!=` lowers to `not(eq(...))`
- quantifiers lower by substitution before formula lowering

## `src/may_must_analysis/llm_provider.rs`

Types:
- `CegisAttempt { candidate, failure }`
- `FullLoopContext { base, assertion_location, header_wp, variable_sorts, header_label, latch_label, header_out_edges, entry_edges, body_node_labels, exit_edges, back_edge_guard, source_location, exit_postcondition, previous_attempts }`
- `RecursiveContext { function, formal_parameters, current_relation, caller_entry_formula }`
- trait `LlmBackend: Send + Sync { fn propose(&self, prompt:&str) -> Option<String>; }`
- `StubLlmBackend`
- `LlmCandidateProvider { backend, max_proposals, manual_summaries }`
- `SubprocessLlmBackend { script_path, model }`

Functions:
- `collect_variable_sorts(loop_info,cfg)` from Assign targets
- `build_full_loop_context(...)`
- `build_loop_invariant_prompt(ctx, template_opt)`
- `render_template(template, ctx)` with placeholders from current code
- `build_recursive_summary_prompt(ctx)`
- `parse_candidate(raw, variable_sorts)`:
  - prefer `<INVARIANT>...</INVARIANT>` or `<POSTCONDITION>...</POSTCONDITION>`
  - else strip `Invariant:`/`Postcondition:`
  - trim backticks
  - parse via `llm_response_parser::parse_invariant`
  - reject trivial `Formula::True`
- `collect_formula_var_sorts`
- `stub_backend() -> Box<dyn LlmBackend>`

Prompt specifics:
- default template loaded from `tools/default_prompt.txt` via manifest dir fallback then cwd fallback
- `clean_node_label` strips metadata trailers from labels
- `classify_var_name` returns one of `"ssa register"`, `"stack region"`, `"named local / parameter"`, `"global / unknown scope"`
- `format_guard_disjunction([]) == "false"`

`LlmCandidateProvider`:
- `new`, `with_max_proposals`, `with_manual_summary`
- `propose_loop_invariants(ctx,seeds)` loops up to `max_proposals`
- `propose_recursive_summary(ctx)` parses tagged postcondition into `ReturnSummary`
- trait impl only supports manual function summary; `loop_invariant` trait method returns empty because full context is required

`SubprocessLlmBackend`:
- spawn `python3 <script> --model <model> <prompt>`
- stdout parsed as response
- stderr inherited
- empty/nonzero exit => `None`

## `src/may_must_analysis/chc.rs`

Types:
- `CallRef { callee, actual_args, result_var, result_sort }`
- `HornModel { function, params, retval_var, summary_formula, call_refs }`
- `ChcSession { fp, predicates }`

`ChcSession`:
- `new(models)`:
  - create `Fixedpoint`
  - set param `engine=spacer`
  - register one Bool predicate per model, domain all Int params + Int retval
  - add one Horn rule per top-level OR disjunct of summary formula
- `check_property(function, model, property)`:
  - query `pred(params,retval) && !property`
  - `Unsat -> Valid`, `Sat -> Invalid`, else `Unknown`

Horn rule builder:
- disjunct body lowered with `SmtScope`
- for each `CallRef`, if callee predicate known, conjoin callee predicate over actual args and result var
- head predicate is model's own function predicate
- no explicit quantifier wrapper; rely on Z3 CHC universalization of free vars

Spacer AST extractor:
- implement `z3_bool_to_formula`, `binary_int_relation`, `z3_int_to_term`, `z3_array_to_memory`, `equivalent_to`
- supports:
  - Bool true/false/and/or/not/implies/iff
  - Eq/Le/Ge/Lt/Gt over Int
  - Int vars, numerals, add/sub/uminus, linear mul where one side numeral, select, array store chains
- unhandled shapes => `None`

`solve_loop_chc(...)`:
- register predicate `I_loop(counter,bound)`
- rule1 init:
  - literal init -> `counter == init`
  - variable init -> return `None`
  - unknown init -> `true`
- rule2 induction:
  - from `I(c,b) && continue_guard && c_next == c + increment` imply `I(c_next,b)`
- rule3 safety:
  - if violation provided and not false, `I(c,b) && !continue_guard && violation -> false`
- query `false`; require `Unsat`
- extract invariant:
  1. try direct AST extraction from `get_cover_delta(-1, &i_decl)` and accept only if `equivalent_to` says exact
  2. fallback template testing over:
     - var/const bounds for int vars
     - pairwise var comparisons
     - conjunctions of first up to 12 atomic templates

Property template helpers:
- `default_property_templates(retval_name)` => `retval>=0`, `retval<=0`, `retval>-1`, `retval<1`
- `param_relative_templates(retval_name, params)` => `retval>=param`, `retval>=-param`, `retval==param` for Int params

## `src/may_must_analysis/backward.rs`

Types:
- `InvariantMethod::{Chc,Houdini,Template}`
- `InvariantConfig { methods, llm, skip_algorithmic }`
- `LlmInvariantConfig { backend, max_tries, force, prompt_template }`
- `AssertionResult { site_id, site_label, judgement, entry_summary, assertion_summary }`
- `BackwardError::{CyclicCfgUnsupported, Rule(RuleError), Oracle(OracleError)}`

Exports:
- `analyze`
- `analyze_with_tables`
- `discover_loop_invariants`
- `render_result`
- `pretty_formula`

Core behavior:
- `analyze` calls `analyze_with_tables(cfg, "", site, oracle, empty_tables, None, None)`
- acyclic cfg -> `run_backward`
- cyclic cfg:
  - if `precomputed` invariants available and `!force_llm`, exclude detected back-edges and call `run_backward` immediately using those invariants
  - else compute preliminary backward states for exit-closure, detect loops, process innermost-first
  - phases per loop:
    1. algorithmic unless forced/skipped
    2. selected non-LLM methods from config: CHC then Houdini then Template
    3. LLM CEGIS if configured
  - failure to accept any invariant => `CyclicCfgUnsupported`
- `try_template_invariant` returns `None`

`run_backward`:
- init `RuleEngine`
- pre-block excluded edges
- seed each accepted loop invariant into `reach[header]` by conjunction
- seed assertion state as `wp(assertion_node.transfer)(!obligation)`
- run fixpoint
- judgement selection order:
  - feasible entry => `BugFound{model}`
  - else if verified => `Verified`
  - else `Unknown`

`compute_preliminary_backward_states`:
- single backward `notmay_pre` pass only, no must pass, no tables

`discover_loop_invariants`:
- only algorithmic candidates
- no exit-closure because no assertion context
- returns `None` for acyclic cfg or any loop without candidate

Formatting:
- `render_result` prints assertion header, judgement, optional `counterexample:` block with indented model lines
- `pretty_formula` wraps `And`/`Or`/`Implies` when length exceeds `WRAP_WIDTH=100`

## `src/may_must_analysis/driver.rs`

Types:
- `ProcedureReport { procedure, assertions, failures }`
- `SafetyVerdict::{Safe, Unsafe, Unknown}`
- `DriverError::Adapter(AdapterError)`
- `ModuleReport { reports, summaries, computed_summaries }`

Exports:
- `analyze_function_graph`
- `analyze_module`
- `analyze_module_with_provider`
- `analyze_module_with_llm`
- `analyze_with_summaries`
- `analyze_function_graph_with_purity`

Procedure verdict:
- any failure => `Unknown`
- no assertions/failures => `Safe`
- any bugfound => `Unsafe`
- all verified => `Safe`
- otherwise `Unknown`

Module pipeline (`analyze_module_with_provider` and LLM variant):
1. phase0: ask provider for summaries of extern callees only (`collect_callee_names - in_graph`)
2. phase1: iterative non-recursive summary inference for `graphs.len().max(1)` rounds:
   - adapt with current summary snapshot
   - `compute_return_summary`
   - insert into registry
3. phase1b: detect recursive functions via Kosaraju SCC; infer CHC summaries for them
4. seed `SummaryTables` with:
   - `MustSummary { True, relation }`
   - `NotMaySummary { True, !relation }`
5. outer inter-procedural fixpoint up to 10 iterations:
   - re-run each procedure with `analyze_with_summaries`
   - stop when `summary_tables` unchanged

`analyze_with_summaries`:
- adapt procedure with summaries/purity
- if cfg cyclic, precompute algorithmic-only invariants once via `discover_loop_invariants`
- if precomputed exist, cache loop-header formulas in `SummaryTables.set_loop_invariants`
- analyze each `AssertionSite` with `analyze_with_tables`
- convert `CyclicCfgUnsupported` into failure string `assertion #...: CFG has a cycle; loops are not supported`

`infer_chc_summaries`:
- build HornModel for each recursive function
- for each model without existing summary, try default templates + param-relative templates
- first `oracle.check_chc_property(...) == Valid` becomes registry summary with empty write effects

`recursive_functions`:
- detect SCCs over in-graph call edges excluding `may_assert`
- size>1 SCC or self-loop => recursive

Current code-state notes:
- `computed_summaries` includes all registry summaries, including provider/extern ones
- recursive procedures still analyzed, but reports gain note string about call cycle

## Tests/documentation files under `src/`

- `src/may_must_analysis/design.md` and `analysis_flow.md` exist and describe architecture; keep them.
- Each Rust file has focused `#[cfg(test)]` blocks covering the behaviors above. Re-add equivalent tests; most important are:
  - formula validation/substitution/model extraction
  - cfg wp/sp/topological order/back-edge detection
  - adapter lowering, indirectbr support, may_assert not baked into transfer
  - oracle sat/unsat/implies/check_summary
  - rules bugfound/verified/summary interplay
  - loop detection/candidate generation/invariant checks
  - llm parser grammar and tagged extraction
  - CHC fixedpoint proofs and AST extractor
  - driver end-to-end fixtures including paper-like summary interplay, extern summary, Houdini-only, CHC-only

## One-line state summary

Current repo is a rule-driven backward may/must analyzer over an abstract CFG, with backward-WP return summaries, summary-guided interprocedural fixpoint, pointer-to-array memory lowering, multi-method loop invariant search (algorithmic/CHC/Houdini/template stub/LLM CEGIS), CHC recursive summaries, and a placeholder `absint_analysis` module.
