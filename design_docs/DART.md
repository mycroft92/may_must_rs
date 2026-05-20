# Forward MUST via DART path enumeration

How the forward-MUST pillar of the may/must analysis is implemented in
`src/may_must_analysis/forward_must.rs`.  Self-contained; read this if
you are touching DART or wiring something into it.

> **Where it fits.** SMASH (Godefroid/Nori/Rajamani/Tetali, POPL'10)
> pairs forward MUST (under-approximate; finds concrete bugs) with
> backward NOT-MAY (over-approximate; proves universal safety via WP
> + loop invariants).  Forward MUST is realised here as DART
> (Godefroid/Klarlund/Sen, PLDI'05): pick a concrete path through the
> CFG, build its path condition symbolically, and ask Z3 for a model
> that satisfies the path *and* the violation precondition.  We use
> bounded enumeration rather than classical DART's branch-flipping
> search — same algorithm class, simpler control flow.

## 1. Interface

Inputs:

- a **CFG** with a single designated **assertion node**
- a **violation precondition** `phi2` — computed by `dart_explore` as
  `assertion_node.transfer.wp(NOT obligation)`; you do not pass it in
- an **SMT oracle** providing `feasibility_with_model`
- a **`DartConfig`** with three knobs (`max_depth`, `max_loop_iters`,
  `max_paths`).  Defaults are 200 / 4 / 256.

Result: `Option<AssertionResult>`:

- `Some(BugFound { model })` — concrete SAT model witnessing the bug
- `None` — no bug found within the bounds (caller interprets as
  `Unknown`)

**DART never returns `Verified`.**  Proving safety is the backward
NOT-MAY pillar's job.

## 2. Algorithm

```text
dart_explore(cfg, site, oracle, config, debug_names):
  phi2 = site.node.transfer.wp(NOT site.obligation)
  paths = enumerate_paths(cfg, entry, site.node, config)
  for path in paths:
    (pc, current_version, memory_state) = compute_path_condition(cfg, path, True)
    phi2_in_path_namespace = subst(phi2, current_version, memory_state)
    if oracle.feasibility_with_model(pc ∧ phi2_in_path_namespace) is Feasible:
      return BugFound { model }
  return None
```

DFS to enumerate paths, build a path condition per path, one SMT
query per path, stop at the first feasible one.  That's the whole
algorithm.

## 3. Path enumeration

DFS from entry to the assertion node, bounded by:

- `max_depth` — total edges in any single enumerated path
- `max_loop_iters` — max revisits of any single node along one path
  (BMC-style unroll depth, expressed on the original cyclic CFG)
- `max_paths` — global cap on enumerated paths

The DFS keeps a per-node `visit_count` map.  Crucial detail: **on
backtrack, decrement the source node's visit count**.  Without this,
two sibling branches at a fork share a single quota for downstream
nodes, and the second sibling gets pruned away spuriously.  See
`dfs_decrement_on_backtrack_gives_siblings_independent_quotas` in the
test module.

## 4. Path condition: `compute_path_condition`

Walks the path's edges in order and **appends** new constraints to a
formula.  Maintains four pieces of state:

| State | Purpose |
|---|---|
| `formula` | the accumulated path condition (append-only) |
| `current_version: HashMap<orig → fresh>` | latest SSA-name rename for each redefined variable |
| `memory_state: HashMap<region → Memory>` | current symbolic memory chain per region (`Store(Store(Var, ...), ...)`) |
| `defined: HashSet<String>` | every variable name that has been assigned at any prior point on this path |
| `node_visit_count: HashMap<NodeId → u32>` | visits to each node so far |

For each edge `(n1, n2)`:

1. **Bump `n1`'s visit count.**  Let `src_visit = n1's new count`.
2. **For each effect in `n1.transfer.effects`** — dispatch by kind:
   - **`Assign { target, Term(t) }`**:
     1. Substitute `t` through `(current_version, memory_state)` —
        eagerly, so the RHS reads the OLD value of any variable
        (including `target` itself when self-referential, e.g.
        `x := x - 1`).
     2. Rename `target` via `version_var(target, n1, src_visit,
        current_version, defined)` — see §5.
     3. Conjoin `versioned_target = t_subst` to `formula`.
   - **`Assign { target, Predicate(p) }`**: same, with `iff` instead
     of `eq`.
   - **`Assume(c)` / `Obligation(c)` / `TypeBound(c)`**: substitute
     `c` and conjoin.  All three behave identically in forward SP —
     the WP-only distinction (TypeBound = identity in WP) does not
     apply.
   - **`MemoryStore { region, offset, value }`**: substitute both
     operands; set
     `memory_state[region] = Store(prev, offset_subst, value_subst)`.
     `formula` unchanged — the store surfaces when a later `Select`
     is substituted via `memory_state`.
   - **Everything else** (`Alloca`, `GetElementPtr`, `Call`, pointer
     bookkeeping, `Nop`, …): no-op.  These are SP-identity after
     `resolve_memory_effects` has rewritten the resolved cases into
     `Assign` / `MemoryStore`.  Do **NOT** apply `tf.sp` to the whole
     `formula` here — that would violate the append-only invariant
     (see §6).
3. **Substitute and conjoin `edge.guard`** through the current
   `(current_version, memory_state)` snapshot, then conjoin.
4. **Apply `edge.effects`** (phi-node assignments lowered onto the
   edge).  Use the **target's upcoming** visit count
   (`node_visit_count[edge.target] + 1`), not the source's — phi
   targets belong to the target block.

After the walk, return `(formula, current_version, memory_state)`.
**Do not do a final substitution on `formula` itself** — see §6.

## 5. SSA versioning: `version_var`

Each `Assign` target needs a name that is unique across the path.
The naming scheme is `<orig>$n{node_id}v{visit_count}`.  Node ids
are globally unique; visit counts are per-node monotonic; the
combination is collision-free without a shared counter.

Rule for picking the name:

- **First definition of a given variable**, on its first visit of
  the defining node → keep the original name.  Clean formulas for
  acyclic / SSA-shaped inputs.
- **Any later definition** — whether a revisit of the same node OR
  a redefinition by a different node — gets the fresh
  `<orig>$n{N}v{k}` name.

The second clause is the **extension beyond the canonical doc**.
The original DART writeup said only "first visit keeps original
name", which is correct for strict SSA inputs.  Our adapter
occasionally produces non-SSA shapes (phi assignments on edges that
re-define a header variable across iterations, hand-built test
CFGs, …) where the same variable is defined at multiple nodes on the
*first* visit of each.  The `defined` set catches this: if the
variable has been assigned anywhere earlier on this path, even at a
different node, treat the new assign as a redefinition and bump the
version.

Reads use the latest mapping (`current_version`) at the moment they
are substituted in.  Earlier conjuncts retain whatever version was
current when they were appended.

## 6. The append-only invariant

> **Once a conjunct is in `formula`, it is never modified,
> substituted, or rewritten.**

`current_version` and `memory_state` are *write-only from the
formula's perspective*: they are lookup tables that get baked into
each new conjunct at append time and never reach back.

Violations of this rule have all been encountered as real bugs:

- **Final substitution at end-of-walk:** retroactively rewriting
  every conjunct with the latest versions silently rewrites the
  first iteration's guard (`%cmp`) using the second iteration's
  versioned name (`%cmp$n{node}v2`).  The resulting formula contains
  both `%cmp$n{node}v2` (positive, from visit 2's true→exit guard
  being already substituted on append) and `!%cmp$n{node}v2` (from
  the retroactive rewrite of visit 1's positive guard).  UNSAT.
  Path is a real bug → DART falsely reports `Unknown`.
- **Apply `tf.sp` to the whole formula on unhandled effects:**
  same disaster in a different place — `sp` propagates the latest
  `memory_state` through every memory expression in `formula`,
  rewriting earlier loads.
- **Retroactively rewrite memory expressions for unhandled effects:**
  a load `array_val = select(store(initial, j, X), j)` added at
  iteration 1 gets rewritten at iteration 2 to
  `array_val = select(store(store(initial, j, X), j2, X2), j)`,
  changing the meaning of the first-iteration load.

If you ever write code that takes `formula` as input and produces a
modified `formula` (other than `formula ∧ new_conjunct`), stop and
verify it does not violate this invariant.

## 7. The `phi2` substitution (extension beyond canonical DART)

`phi2 = wp(assert.transfer)(NOT obligation)` references variables
by their entry-namespace names (e.g. `x`).  But our path's
`current_version` may have re-mapped `x` to `x$n{cond}v2` by the
time we reach the assertion.  The two namespaces have to be
reconciled before the SAT query.

**What we do:** substitute `phi2` through the path's final
`current_version` and `memory_state` *once* at combine time, then
conjoin with `pc`.  This is *not* the §6 anti-pattern — §6 forbids
rewriting the accumulated path-condition formula; here we rewrite
the externally-supplied `phi2`, which has no internal history to
clobber.

Without this step, `phi2`'s `x` evaluates against the entry-time
binding rather than the assertion-site binding, and any loop that
actually changes `x` produces a false `Unknown`.

## 8. Interaction with the rest of the engine

DART is the bug-finding fallback in `smash::run_smash`.  Sequence
per assertion:

1. Backward NOT-MAY runs first.  If it returns `Verified` or
   `BugFound`, that verdict wins.
2. If NOT-MAY returns `Unknown` (or `CyclicCfgUnsupported`), DART
   runs.  `config.bmc_bound` is reused as `max_loop_iters`.
3. If DART finds a feasible path, return `BugFound` with the SMT
   model and engine label `forward-must/dart`.  Otherwise, return
   the NOT-MAY `Unknown`.

`bmc.rs` still exists but is no longer wired into the primary
pipeline.  It's kept as a documented backup mode in case DART
regresses on a future input class.

## 9. Configuration

```rust
DartConfig {
    max_depth: 200,
    max_loop_iters: 4,   // overridden by config.bmc_bound when invoked from smash.rs
    max_paths: 256,
}
```

The CLI flag controlling unroll depth is `--bmc-bound`; nothing else
needs to change to bound DART tighter or looser.

## 10. Soundness

- `BugFound` is sound: the SAT model is a real concrete satisfying
  assignment to a feasible path condition AND the violation
  precondition.
- `Unknown` is always sound.
- `Verified` is never returned.
- The `memory_state` chain handles single-region multi-store paths
  correctly via Z3 array axioms.  Cross-region aliasing is the
  adapter's responsibility (resolved during
  `resolve_memory_effects`).

## 11. Worked example: array-2

```c
int main() {
  unsigned int SIZE = 1;
  int array[SIZE], menor;
  menor = nondet_int();
  for (j = 0; j < SIZE; j++) {
    array[j] = nondet_int();
    if (array[j] <= menor) menor = array[j];
  }
  may_assert(array[0] > menor);
}
```

The bug path: enter loop once with `menor_orig == array[0]`, body
sets `menor = array[0]`, exit loop with `menor == array[0]`,
assertion `array[0] > menor` becomes `X > X` → false.

DART finds this at `max_loop_iters >= 2`.  The SMT model
discriminates the two visits to the loop-header `cmp` node via the
versioned names — running with `-vv` shows pairs like
`(main$%15, Bool(true))` and `(main$%15$n20v2, Bool(false))` in the
output: same source variable, two distinct path-condition
versions, opposite boolean values.  Both are consistent in the
witness because they refer to different program points along the
1-iteration path.

## 12. Code map

- `src/may_must_analysis/forward_must.rs` — everything in this doc.
- `src/may_must_analysis/smash.rs` — wires DART after backward
  NOT-MAY.
- `src/may_must_analysis/bmc.rs` — legacy CFG-unrolling
  bug-finder.  Functional but unused in the primary pipeline; kept
  as a backup mode.

## 13. Tests

`forward_must::tests` covers, at minimum:

| Test | What it pins |
|---|---|
| `dart_finds_bug_on_straightline` | basic SP walk + SMT integration |
| `dart_returns_unknown_when_assertion_holds_on_all_paths` | no false positives on safe straightline |
| `dart_finds_bug_on_branchy_cfg` | path enumeration explores both branches |
| `dart_finds_bug_on_true_then_false_loop_pattern` | §6 append-only invariant + §7 `phi2`-rename; this is the regression test for the historical retroactive-substitution bug class |
| `dart_memory_store_visible_through_select` | memory chain + array axiom |
| `version_var_produces_unique_names_per_node_visit` | `(node, visit)` naming uniqueness |
| `version_var_redefinition_on_first_visit_bumps_version` | `defined`-set extension (§5) |
| `dfs_decrement_on_backtrack_gives_siblings_independent_quotas` | DFS backtrack-decrement (§3) |

Touch any of the four maps (`formula`, `current_version`,
`memory_state`, `defined`) and run these first.  The true-then-false
loop test is the canary for the append-only invariant.
