# CLAUDE.md

This file is for Claude. Read it before changing any code in this repository.

## Goal

Given an assertion and a program, either show the assertion site is unreachable
or show the assertion condition always holds on reachable executions. This is a
formal verification tool, not a testing tool.

Paper reference: https://dl.acm.org/doi/10.1145/1707801.1706307

## Session Startup

Read in order before touching code:

1. `README.md`
2. `TODO.md`
3. Relevant `src/` modules (see Active Architecture below)

## Active Architecture

The relevant code lives under `src/` only. Do not extend or document any
removed architecture.

```
src/llvm_utils/llvm_wrap.rs        LLVM C API wrapper boundary
src/llvm_utils/program_graph.rs    raw instruction graph generation
src/common/formula.rs              terms, predicates, SMT model types
src/common/abstract_cfg.rs         abstract CFG, transfer effects, WP helpers
src/common/adapter.rs              FunctionGraph -> AdaptedProcedure lowering
src/common/oracle.rs               SMT feasibility / implication boundary
src/may_must_analysis/node_summary.rs  per-node reach/state summaries
src/may_must_analysis/rules.rs         local backward propagation rules
src/may_must_analysis/backward.rs      assertion checking + loop invariant search
src/may_must_analysis/loops.rs         loop detection and invariant checking
src/may_must_analysis/driver.rs        module orchestration and call-summary reuse
src/may_must_analysis/providers.rs     external/manual summary provider seam
src/may_must_analysis/summaries.rs     summary table data structures
src/smt/solver.rs                  raw Z3 lowering
```

## Bidirectional Analysis — Core Invariant

This is a bidirectional may/must analysis. **Never break or bypass this.**

`run_backward` in `backward.rs` implements the full combined check:

- **Forward direction (reach / must)**: loop invariants are injected into
  `reach` at loop headers. `reach` overapproximates reachable states.
- **Backward direction (state / may)**: WP of `NOT obligation` is propagated
  backward through `state`. `state` encodes violation conditions.
- **Combined check**: `reach AND state` infeasible at entry → `Verified`.

Summaries from both directions feed into callers:
- `ReturnSummary` carries return-value relations derived from the backward check.
- `SummaryTables` carries loop invariants that seed the forward reach at headers.

When inferring summaries for cyclic (looping) callees
(`infer_cyclic_observer_summary` in `driver.rs`), the authoritative
verification is the `analyze_with_tables` call, which runs the full
bidirectional check. Intermediate invariant candidate synthesis in
`observer_summary_invariants` only needs to produce an inductive invariant —
exit closure there is intentionally skipped because the obligation is verified
by `analyze_with_tables`.

## Key Semantic Boundaries

- **`adapter.rs`**: the lowering boundary. Pointer parameters → `ext_region`
  (`fn$__ext_N`). Local allocas → `stack0`, `stack1`, ... Memory ops →
  `select`/`MemoryStore` on named regions.
- **`oracle.rs`**: all SMT queries go through here. Do not add raw solver calls
  elsewhere.
- **`backward.rs`**: `analyze_with_tables` is the top-level entry for checking
  one assertion. `run_backward` is its core. `synthesize_loop_invariants`
  handles cyclic CFGs.
- **`loops.rs`**: `check_loop_invariant_verbose` checks initiation,
  inductiveness, and optionally exit closure. Pass `&BTreeMap::new()` for
  `assertion_postconditions` when exit closure should be skipped.
- **`driver.rs`**: orchestrates per-module analysis, caches summaries, and
  drives interprocedural inference.

## CFG-to-Effects Lowering: How Pointers, Globals, and Memory Work

This section describes the full pipeline from LLVM IR to abstract transfer
effects, and how those effects are used in the subsequent analysis.

### Phase 1 — Node transfer (instruction-level, `lower_node_transfer`)

Each LLVM instruction is lowered to a list of `TransferEffect` values on its
CFG node. The key instruction kinds:

**Arithmetic / comparison** (`add`, `sub`, `icmp`, etc.)
- Lowered to `TransferEffect::Assign { target, value: Term(...) }` or
  `TransferEffect::Assign { target, value: Predicate(...) }`.
- Variable names are `fn$%varname` (function-name-prefixed to avoid collisions
  across functions).

**`alloca`**
- Each `alloca` is pre-assigned a region name `fn$stackN` (N = 0, 1, 2, …)
  during the first pass over vertices.
- Lowered to `TransferEffect::Alloca { target: "fn$%ptr", region: "fn$stackN" }`.
- The `target` is the pointer-typed SSA value. The `region` names the logical
  memory array that this allocation owns.

**`load`**
- If the loaded value is pointer-typed: `TransferEffect::PointerLoad { target_ptr, source_slot }` — tracked for pointer aliasing, resolved in Phase 2.
- Otherwise: `TransferEffect::Load { target: Var, source: "fn$%ptr" }` — the
  `source` is the pointer SSA name. Resolved in Phase 2 to
  `Assign { target, value: select(region, offset) }`.

**`store`**
- If the stored value is pointer-typed: `TransferEffect::PointerStore { target_slot, value_ptr }` — tracked for aliasing, resolved in Phase 2.
- Otherwise: `TransferEffect::Store { target: "fn$%ptr", value: Term }` — resolved in Phase 2 to `MemoryStore { region, offset, value }`.

**`getelementptr` (GEP)**
- Lowered to `TransferEffect::GetElementPtr { target, base, offset }` where
  `offset` is the sum of all GEP index operands as integer terms.
- **Current limitation**: element sizes and struct field layout are ignored —
  all indices are summed as plain integers. See `TODO.md`.

**`phi`**
- Node-level effect is empty (`PHI` and `Br` produce no effects).
- PHI incoming values are lowered as `TransferEffect::Assign` on the *incoming
  CFG edges* (`lower_phi_edge_effects`), ensuring each path carries its own
  assignment.

**`br` (branch)**
- Node effect is empty. The branch condition is encoded on CFG *edges* as a
  `Formula` guard. True branch: `condition`; false branch: `NOT condition`;
  unconditional: `True`.

**`ret`**
- Lowered to `Assign { target: Var("fn$__retval"), value: returned_term }`.
  This synthetic variable carries the return value for summary inference.

**`call`**
- `may_assert` calls are stripped from the graph by `program_graph.rs` and
  recorded as `AssertionSite` obligations; they produce no transfer effect.
- For other callees: `TransferEffect::Call { callee, memory_effect }`.
  `memory_effect` is `PreservesMemory` if the callee was inferred to be pure
  (no stores, no impure callees), else `HavocMemory`.
- After Phase 2 (return summary application), calls with known summaries gain
  a `TransferEffect::Obligation(relation)` on the call node.

**`bitcast` / `addrspacecast`**
- If the result is pointer-typed: `TransferEffect::PointerAlias { target, source }` — resolved in Phase 2 to an alias binding.

### Phase 2 — Pointer environment resolution (`resolve_memory_effects`)

After all nodes and edges are created, a second pass builds a `PointerEnv`
(a map from pointer-SSA-name → `(region, offset)`) and rewrites the effects.

**Pre-seeding pointer parameters**:
- For each function parameter at a `pointer_param_index`, the parameter SSA
  name (`fn$%param`) is bound to an *external region* named `fn$__ext_N`
  (where N is the parameter's index) with offset `0`.
- External regions are uninterpreted memory arrays — the analysis treats them
  as having unknown but fixed content. This is how pointer arguments from
  callers become observable by the callee.

**Pre-seeding global variables**:
- Any operand that `is_global_variable_ref()` and is pointer-typed gets bound
  to a region named `global$<display-name>` with offset `0`.
- Global regions are treated the same as local regions: a named array in the
  abstract memory model.

**Traversal order**: topological (excluding back edges) to propagate bindings
in definition order. For cyclic CFGs, the ordering is best-effort.

**Effect rewriting rules**:

| Input effect | Resolved to |
|---|---|
| `Alloca { target, region }` | Binds `target → (region, 0)` in env; kept as-is |
| `GetElementPtr { target, base, offset }` | If `base` is in env: binds `target → (base.region, base.offset + offset)`; kept as-is |
| `Load { target, source }` | If `source` in env: → `Assign { target, select(region, offset) }` |
| `Store { target, value }` | If `target` in env: → `MemoryStore { region, offset, value }` |
| `PointerLoad { target_ptr, source_slot }` | If `source_slot` in env: copies binding to `target_ptr`; → `Nop` |
| `PointerStore { target_slot, value_ptr }` | If `value_ptr` in env: copies binding to `target_slot`; → `Nop` |
| `PointerAlias { target, source }` | If `source` in env: copies binding to `target`; → `Nop` |

If a pointer is not in the env (e.g., unresolved external pointer from an
untranslated call), the original effect is kept unchanged and the analysis may
produce `UNKNOWN` downstream.

### Phase 3 — Return summary application (`apply_pending_return_summaries`)

For each `call` instruction where the callee has a known `ReturnSummary`:

1. **Variable renaming**: formal parameter names (`callee$%param`) are renamed
   to actual argument names (`fn$%actual`). The callee retval (`callee$__retval`)
   is renamed to the call-instruction's local name (`fn$%call`). Other
   callee-internal variables get a unique per-call-site prefix
   (`fn$callN$suffix`).

2. **Region substitution**: callee external regions (`callee$__ext_N`) are
   replaced by the actual memory region and base offset that the corresponding
   pointer argument resolves to in the caller's `PointerEnv`. This connects the
   callee's memory model to the caller's concrete allocations or globals.

3. **Constant substitution**: if an actual argument is a constant integer, the
   formal parameter variable is substituted with that constant.

4. The resulting formula is appended as `TransferEffect::Obligation(formula)`
   on the call node. In the WP backward pass, `Obligation(f)` acts like
   `assert(f)`: it adds `f` as a conjunction to the backward state.

### Phase 4 — Memcpy/memset modeling (`apply_pending_memcpy_effects`)

`llvm.memcpy` and `llvm.memmove` are modeled by unrolling them:
- If source is a constant array (global initializer), each element becomes a
  `MemoryStore { region: dst, offset: base+i, value: constant }`.
- If source is a variable region with a known length, each offset position gets
  `MemoryStore { region: dst, offset: base+i, value: select(src, src_base+i) }`.

`llvm.memset` with constant fill and length is similarly unrolled element-by-element.

### How these feed into the analysis

**Backward WP (`wp_one` in `abstract_cfg.rs`)**:
- `Assign { target, value: Term(t) }`: substitutes `target ← t` in the postcondition.
- `MemoryStore { region, offset, value }`: substitutes the memory array
  `region ← store(region, offset, value)` in the postcondition, so a subsequent
  `select(region, offset)` resolves to `value`.
- `Obligation(f)`: conjoins `f` into the postcondition, asserting the callee
  relation holds at that point.
- `Call { memory_effect: HavocMemory }`: existentially quantifies away all
  memory arrays (approximated by dropping memory constraints containing havoced
  regions).
- `Nop`, `Alloca`, `GetElementPtr`, `PointerLoad`, `PointerStore`,
  `PointerAlias`: no WP effect (pointers and regions are resolved by Phase 2
  before the analysis runs).

**Forward reach injection**:
- Loop invariants are injected into `reach` at loop headers.
- For external regions, the invariant typically constrains
  `select(fn$__ext_N, k)` — the k-th element of the pointer argument.
- At callers, region substitution (Phase 3) maps `fn$__ext_N` to the caller's
  actual memory region, so the invariant correctly constrains the caller's
  local array or global.

**Combined feasibility check**:
- At entry, `oracle.check_infeasible(reach AND state)` tests whether the
  violation condition `state` is reachable within the overapproximation `reach`.
- Infeasible → `Verified`. Feasible with a model → `BugFound`. Neither → `Unknown`.

## Soundness Rules

- Prefer `UNKNOWN` over an unsound `Verified` claim.
- Mark heavy approximations with `APPROX_HEAVY:` comments.
- An invariant is sound only when both initiation and inductiveness pass.
  Exit closure is an additional check that ties invariants to the specific
  assertion — it is not required for inductive correctness, but it IS required
  for the invariant to directly discharge the obligation. When skipping it,
  ensure `analyze_with_tables` does the discharge instead.
- Do not read `obsolete/`.
- Keep generated `.ll`, `.bc`, and DOT files out of source control.

## Verification Commands

Always run after code changes:

```sh
cargo fmt
cargo test
```

Also run when touching CLI behavior, lowering, or smoke assumptions:

```sh
make -C tests smoke
```

## Development Rules

- Keep LLVM-specific logic in `llvm_utils/`.
- Keep raw solver details in `smt/solver.rs` and policy in `oracle.rs`.
- When a concept is logically independent, split it into a new module.
- When broadening support, keep `formula.rs`, `abstract_cfg.rs`, `adapter.rs`,
  `oracle.rs`, and `smt/solver.rs` aligned.
- Add focused unit tests for new logic.
- Update `TODO.md` and `TASKVIEW.md` if the backlog or next-session plan changes.
- Update `README.md` when CLI behavior or support boundaries change.
