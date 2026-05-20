# DART path enumeration

How the forward-must pillar of the may/must analyzer is implemented.
This document is meant to be self-contained: an agent that has not
seen the rest of the codebase should be able to read this and arrive
at a working implementation — including all the traps that were hit
the first time around.

> **Background.** SMASH (Godefroid/Nori/Rajamani/Tetali, POPL'10) pairs
> a forward must analysis with a backward not-may analysis. The forward
> must side is implemented by DART (Godefroid/Klarlund/Sen, PLDI'05):
> Directed Automated Random Testing. DART is a symbolic-execution-style
> bug finder; it picks a concrete path through the CFG, builds the
> path's symbolic constraint, and asks an SMT solver "does any input
> satisfy this path AND violate the assertion?" If yes, you have a
> witness. The classical DART loop drives further exploration by
> flipping the last branch's condition to ask the solver for a
> different path. We use a simpler bounded enumeration variant.

---

## 1. The mental picture

You are given:

- a **CFG** for a procedure, with one designated **assertion node**
  whose obligation `O` (a formula over the procedure's variables) the
  rest of the analysis is trying to prove or refute
- a **query precondition** `phi1` (typically `True`)
- a **query postcondition** `phi2` (the **violation** precondition at
  the *pre-state* of the assertion node, computed by the caller as
  `wp(assertion_node.transfer)(¬O)`)
- an **SMT oracle** that decides feasibility / satisfiability and
  returns a model on SAT
- a **bound config** (`max_depth`, `max_loop_iters`, `max_paths`)

You must answer:

> Is there an input satisfying `phi1` such that some execution from
> entry reaches `assertion_node` and `O` is violated there?

If yes → return `BugFound` with a concrete model and the witness path.
If no path within the bound shows this → return `Unknown`. **Never
claim `Verified`** — proving universal absence of bugs is the
backward-not-may pillar's job, not DART's.

---

## 2. The algorithm at a glance

```
dart_explore(cfg, assertion_node, phi2, phi1, oracle, config):
  // 1. enumerate paths entry → assertion_node
  paths = enumerate_paths(cfg, cfg.entry(), assertion_node, config)

  // 2. for each path, build path condition and ask oracle
  for path in paths.first(config.max_paths):
    pc = compute_path_condition(cfg, path, phi1)
    combined = pc ∧ phi2
    report = oracle.feasibility_with_model(combined)
    if report.feasibility == Feasible:
      return BugFound{ path, pc, phi2, combined, report.model }

  return Unknown
```

That's it. The whole algorithm is a DFS path enumerator plus one SMT
call per path.

---

## 3. Step by step

### 3.1 Path enumeration (`enumerate_paths`)

A path is a sequence of CFG **edges** from `cfg.entry()` to
`assertion_node`. We enumerate paths by depth-first search with two
bounds:

- `max_depth`: total edges in any single path.
- `max_loop_iters`: how many times any single CFG node may be
  re-entered along the same path (BMC-style loop unrolling depth).

```rust
fn dfs(
    cfg, node, target,
    remaining_depth, max_iters,
    current: &mut Vec<EdgeId>,
    visit_count: &mut HashMap<NodeId, usize>,
    out: &mut Vec<Vec<EdgeId>>,
    max_paths: usize,
) {
    if out.len() >= max_paths { return; }
    if node == target {
        out.push(current.clone());
        return;
    }
    if remaining_depth == 0 { return; }

    {
        let count = visit_count.entry(node).or_insert(0);
        if *count >= max_iters { return; }
        *count += 1;
    }

    for edge_id in cfg.outgoing_edges(node) {
        if out.len() >= max_paths { break; }
        current.push(edge_id);
        dfs(cfg, edge.target, target, remaining_depth - 1,
            max_iters, current, visit_count, out, max_paths);
        current.pop();
    }

    // Decrement on the way back up so sibling DFS branches each
    // get their own quota of iterations on this node.
    if let Some(c) = visit_count.get_mut(&node) {
        *c = c.saturating_sub(1);
    }
}
```

The decrement on backtrack is critical: without it, sibling branches
in the DFS tree share the quota, and the second sibling might be
incorrectly pruned.

### 3.2 Path condition (`compute_path_condition`)

Given a path (list of edges), build a formula constraining program
variables to exactly those inputs that follow this path.

The implementation maintains three pieces of mutable state:

1. **`formula`** — the accumulated Boolean formula. Starts as `phi1`.
   Each constraint is **permanently conjoined** once added; nothing is
   ever rewritten after the fact.

2. **`memory_state: HashMap<region, Memory>`** — current symbolic
   memory expression per region. Updated by `MemoryStore` effects so
   subsequent loads (rewritten to `select(...)` by the adapter) see
   the stored values via Z3's array axioms.

3. **`current_version: HashMap<String, String>`** — maps each SSA
   variable's original name to its **current version name**. Updated
   when a node is visited for the second-or-later time so repeated
   definitions of the same SSA name don't collide.

For each edge `e = (n1, n2)` along the path:

1. **Increment `n1`'s visit count** in a separate
   `node_visit_count: HashMap<NodeId, u32>`.  Let `vcount` = the new
   count.

2. **For each effect in `n1.transfer.effects`:** dispatch:
   - `Assign { target, value: Term(t) }`:
     - Substitute `t` through `current_version` + `memory_state`
       (reads the OLD value of any variable, including `target`
       itself if self-referential).
     - Call `version_var(target, n1, vcount, &mut current_version)`
       to get the versioned target name (see §3.2.2).
     - Conjoin `versioned_target = t_substituted` to `formula`.
   - `Assign { target, value: Predicate(p) }`: same but with `iff`.
   - `Assume(c)` / `Obligation(c)`: substitute `c`, conjoin.
   - `MemoryStore { region, offset, value }`: substitute `offset`
     and `value` through current state, then
     `memory_state[region] = Memory::Store(prev, offset_subst, value_subst)`.
     **Formula unchanged** — the store's effect is encoded in the
     memory_state and surfaces when a subsequent `select(...)` is
     substituted.
   - **All other effects**: no-op. They are sp-identity after
     `resolve_memory_effects` has rewritten them into `Assign` /
     `MemoryStore` / `Nop`. **Do not retroactively substitute the
     accumulated formula** for these — see pitfall §P4.

3. **Conjoin the edge guard.** Substitute `edge.guard` through
   `current_version` + `memory_state` **at this point in the walk**
   (before any future updates), then conjoin to `formula`.

4. **Apply edge effects** (phi assignments). Use the **target** node's
   upcoming visit count (see pitfall §P5 for why):
   ```rust
   let tgt_visit = *node_visit_count.get(&edge.target).unwrap_or(&0) + 1;
   apply_path_effect(&mut formula, effect, ..., edge.target, tgt_visit);
   ```

**Return `formula` directly.** Do NOT do a final substitution of the
accumulated formula through `current_version` after the loop ends.
See pitfall §P1 for the disaster that causes.

### 3.2.2 Per-node-visit SSA versioning (`version_var`)

When a CFG node `n` is processed for the `k`-th time (`k ≥ 2`), its
`Assign` targets get renamed `<original>$n<n.0>v<k>` to avoid
collisions with the same node's definitions on other visits. The first
visit (`k = 1`) keeps the original name.

```rust
fn version_var(target: &Var, node_id: NodeId, visit_count: u32,
               current_version: &mut HashMap<String, String>) -> Var {
    if visit_count == 1 {
        target.clone()          // first visit: keep original name
    } else {
        // unique per (node_id, visit_count) — no two nodes produce the
        // same name, no two visits to the same node produce the same name
        let fresh_name = format!("{}$n{}v{}", target.name(), node_id.0, visit_count);
        current_version.insert(target.name().to_string(), fresh_name.clone());
        Var::new(fresh_name, target.sort())
    }
}
```

Why node-and-visit-count naming instead of a global counter? See
pitfall §P2.

After this call, `current_version[target.name()]` maps to the fresh
name. All future **reads** of `target.name()` in edge guards and value
terms are substituted through `current_version` to pick up the latest
version. Previous constraints already conjoined into `formula` are
**not touched** — they permanently retain the version that was current
when they were added.

### 3.2.3 Memory state and why it's needed

After `resolve_memory_effects` runs during CFG construction, loads are
rewritten to `Assign { target, value: select(Memory::Var(R), off) }`.
The global engine's `sp(MemoryStore)` is a no-op, so without DART's
local `memory_state`, `Memory::Var(R)` in those selects is
unconstrained and Z3 picks any default. With `memory_state`, when a
subsequent load is applied via `apply_path_effect`, its value term
`select(Memory::Var(R), off)` is substituted through `memory_state[R]`
to get `select(Memory::Store(..., off_store, val), off)`, which Z3
evaluates to `val` when `off_store == off` via the array store-select
axiom.

### 3.3 Combining with `phi2`

```rust
let combined = Formula::and(pc, phi2.clone());
let report = oracle.feasibility_with_model(&combined)?;
```

`phi2` is already in entry-namespace SSA (the caller computed
`wp(assertion_node.transfer)(¬O)`). The path condition `pc` is also
in entry-namespace SSA. Their conjunction is directly satisfiable by
Z3.

---

## 4. Interaction with the rest of the engine

DART is the **bug-finding** fallback. It runs only when the
backward-not-may pillar (loop invariants + state[entry] check)
returned `Unknown`. If not-may proved `Verified`, DART is **skipped**
— DART can produce false-positive `BugFound` results on programs where
`sp(MemoryStore)` is a no-op, and we never let a false positive
override a real proof.

```rust
let verdict = not_may_decide_verdict(&engine, oracle)?;

match verdict {
    Judgement::Verified => Judgement::Verified,
    Judgement::BugFound { model } => Judgement::BugFound { model },
    Judgement::Unknown => {
        // Only here do we run DART
        match dart_explore(cfg, assertion_node, phi2, phi1, oracle, config) {
            DartOutcome::BugFound(summary) => BugFound { model: summary.model },
            DartOutcome::Unknown => Unknown,
        }
    }
}
```

---

## 5. Configuration and CLI flags

```rust
pub struct DartConfig {
    pub max_depth: usize,        // default: 200
    pub max_loop_iters: usize,   // default: 4
    pub max_paths: usize,        // default: 256
}
```

CLI flags for isolating pillars:

| Flag | Effect |
|---|---|
| `--no-dart` | Disable DART |
| `--no-not-may` | Disable backward not-may |
| `--no-loop-invariants` | Disable loop invariant synthesis |
| `--dart-only` | Shorthand: `--no-not-may --no-loop-invariants` |
| `--not-may-only` | Shorthand: `--no-dart` |

---

## 6. Soundness

- `BugFound` is sound: every accepted witness is a concrete satisfying
  assignment to a feasible path condition.
- `Unknown` is always sound.
- `Verified` is **never** returned by DART.
- Caveat: `sp(MemoryStore)` is a no-op in the global engine. DART
  compensates locally via `memory_state`, which handles single-write
  programs correctly. Programs that store to the same region multiple
  times on the same path accumulate nested `Memory::Store` layers that
  Z3 reasons about with array axioms.

---

## 7. Where this lives in the code

- **`src/may_must_analysis/forward_must.rs`** — `DartConfig`,
  `DartPathSummary`, `DartOutcome`, `dart_explore`, `enumerate_paths`,
  `compute_path_condition`, `apply_path_effect`, `version_var`.
  Unit tests cover: straightline-verified, unconstrained-bugfound,
  branchy-bugfound, and the true-then-false loop-header pattern.
- **`src/may_must_analysis/backward.rs::smash`** — wires DART as the
  fallback after the not-may verdict.

---

## 8. Worked example: array-2

The C program:

```c
int main() {
  unsigned int SIZE = 1;
  int array[SIZE], menor;
  menor = nondet_int();          // unconstrained
  for (j = 0; j < SIZE; j++) {
    array[j] = nondet_int();     // unconstrained write
    if (array[j] <= menor) menor = array[j];
  }
  may_assert(array[0] > menor);
}
```

The bug path (1-iteration, if_true branch):

```
entry       j=0, SIZE=1, menor=M (nondet)
header      j < SIZE (0 < 1 = true) → take body
body        array[0] = X (nondet), if X <= M: menor = X
for.inc     j++  →  j = 1
header(v2)  j < SIZE (1 < 1 = false) → exit
assert      array[0] > menor? X > X? false. BUG.
```

DART finds this path and returns the model `{menor=0, X=0}` (or any
value satisfying `X <= M`). The formula encodes:

- 1st header visit: `%cmp = (j < SIZE)`, guard `%cmp` (true).
- body: `memory_state[array_R] = Store(array_R, 0, X)`.
  Load produces `array0 = X`.
  Load menor produces `menor_val = M`. `%cmp4 = (X ≤ M)`, guard `%cmp4`.
  Store menor: `memory_state[menor_R] = Store(menor_R, 0, X)`.
- for.inc: `j_new = j + 1 = 1`.
- 2nd header visit: `%cmp$n{node}v2 = (1 < 1) = false`.
  Guard `!%cmp$n{node}v2` (true, exit taken).
- assert: `array0_final = X`, `menor_final = X`.
  `phi2 = ¬(X > X) = (X ≤ X) = True`.
- Combined = `path_condition ∧ True`. SAT with any `X, M` satisfying
  `X ≤ M`.

---

## 9. Implementation pitfalls — read these before touching the code

**These are all bugs that were actually introduced and had to be fixed.
They are presented in detail so you do not repeat them.**

### P1 ★ The retroactive-substitution catastrophe (most critical)

**What happened.** The original `compute_path_condition` ended with:

```rust
// At the end of the path walk:
substitute_memory_in_formula_v2(&formula, &current_version, &memory_state)
```

This seemed reasonable: flush any remaining unresolved variable
references. But it caused every path through a loop to be UNSAT.

**Why it's fatal.** `current_version` grows over the walk. By the end,
it contains the *latest* version mapping for every variable that was
re-defined. The final substitution rewrites the **entire accumulated
formula** — including constraints that were correctly frozen at earlier
points in the walk.

Concretely for array-2: the 1st header visit adds guard `%cmp` (true,
body taken) to `formula`. The 2nd header visit bumps `%cmp` to
`%cmp$n25v2`. The final substitution converts the 1st guard `%cmp`
→ `%cmp$n25v2`. Now `formula` contains both `%cmp$n25v2` (from the
2nd visit's guard positive) and `!%cmp$n25v2` (from the 2nd visit's
guard negative... wait, same node). Actually: the 1st-visit guard was
`%cmp` (true branch into body), the 2nd-visit exit guard was already
substituted to `!%cmp$n25v2` at the time it was added. But the
1st-visit guard `%cmp` then gets rewritten to `%cmp$n25v2` by the
final substitution. So now you have `%cmp$n25v2` (positive) AND
`!%cmp$n25v2` (negative) in the same formula. UNSAT.

**The fix.** Remove the final substitution entirely. All reads are
substituted **eagerly** when they're added to the formula (before
`current_version` is updated for any subsequent definitions). Once a
constraint is in `formula`, it is never touched again.

```rust
// WRONG — retroactive substitution destroys earlier frozen guards:
return substitute_memory_in_formula_v2(&formula, &current_version, ...);

// RIGHT — formula is already fully substituted at each step:
return formula;
```

**How to verify you have this bug.** Run `--dart-only` on a fixture
with a simple counted loop. If the loop fixture returns `Unknown`
instead of `BugFound`, print the path formula and look for a variable
that appears on both sides of a contradiction (`%cmp ∧ !%cmp`).

---

### P2 ★ Counter-based SSA naming produces collisions

**What happened.** The first version of `bump_version` used a single
global `counter: u32` that incremented monotonically:

```rust
// WRONG
*counter += 1;
let fresh_name = format!("{}$it{}", original, *counter);
```

**Why it's wrong.** The formula for array-2's path[13] showed
`main$%3$it1` defined *twice* with different values — a direct
contradiction. This happened because:

1. 2nd for.cond visit bumps `%3` → `%3$it1` (counter=1).
2. 3rd for.cond visit bumps `%3` → `%3$it{K}` where K is the counter
   value *after many other bumps in between*. If by coincidence K
   happened to equal 1 (it didn't here, but the naming was still
   fragile and hard to reason about).

More precisely, the formula showed duplicate names because the counter
value at the 2nd visit of node 23 was not guaranteed to be distinct
from the counter value at ANY later redefinition.

**The fix.** Name versions by `(node_id, visit_count)` — inherently
unique:

```rust
// RIGHT
let fresh_name = format!("{}$n{}v{}", original, node_id.0, visit_count);
```

Node IDs are unique (each CFG node has a distinct id). Visit counts
are per-node-per-path and increment monotonically. Two nodes that
both define `%cmp` produce `%cmp$n23v2` and `%cmp$n25v2`
respectively — never the same string.

---

### P3 Counter-based `defined`-set bumping is also fragile

**What happened.** Before the node-visit scheme, the implementation
used a `defined: HashSet<String>` to track first definitions and
a global counter for subsequent ones:

```rust
if defined.contains(&original) {
    *counter += 1;
    let fresh = format!("{}$it{}", original, *counter);
    current_version.insert(original, fresh);
    Var::new(fresh, ...)
} else {
    defined.insert(original);
    target.clone()
}
```

**Why it's fragile.** The `counter` is shared across all variables.
The fresh name for `%cmp`'s 2nd definition depends on how many OTHER
bumps occurred since its 1st definition. This makes names hard to
predict and hard to debug. The fundamental problem is the same as P2:
a counter that's not tied to a specific (node, visit) pair can produce
surprising collisions or non-obvious orderings.

**The fix.** Same as P2: use `(node_id, visit_count)` naming.

---

### P4 ★ Retroactive substitution in the catch-all arm

**What happened.** The `_` arm for unhandled effects (Alloca, GEP,
Call, etc.) did:

```rust
// WRONG
let pre_subst = substitute_memory_in_formula_v2(formula, current_version, memory_state);
*formula = tf.sp(&pre_subst);
*formula = substitute_memory_in_formula_v2(formula, current_version, memory_state);
```

Step 1 already retroactively rewrites the accumulated formula. Then
step 2 does it again. Same disaster as P1, just in a different place.

**The fix.** Most effects in this arm are sp-identity after
`resolve_memory_effects` has rewritten them. Just do nothing:

```rust
// RIGHT
_ => {}  // no-op; sp-identity after resolve_memory_effects
```

If you need to handle an effect that truly IS NOT identity, add it as
an explicit arm ABOVE the `_` catch-all, handling only the new formula
atoms it introduces (never rewriting `formula` in-place by applying
sp to the whole thing).

---

### P5 Edge-effects version context uses the wrong node

**What happened.** Edge effects (phi assignments that occur on an
edge, not a node) were given the SOURCE node's version context instead
of the TARGET's:

```rust
// WRONG — uses source node's visit count for phi targets
for effect in &edge.effects {
    apply_path_effect(&mut formula, effect, ..., edge.source, vcount);
}
```

Phi assignments define variables that belong to the target basic
block. If you use the source node's id and visit count for the version
name, the names don't match what the target block's load effects will
reference.

**The fix.** Use the TARGET node's UPCOMING visit count (the visit
count it will have when it is next processed as a source — which is
its current count plus 1):

```rust
// RIGHT
for effect in &edge.effects {
    let tgt_visit = *node_visit_count.get(&edge.target).unwrap_or(&0) + 1;
    apply_path_effect(&mut formula, effect, ..., edge.target, tgt_visit);
}
```

This ensures that when for.cond's node 23 is next processed as a
source on the 2nd iteration, its load of `%j` produces `%3$n23v2`
that matches the phi-assigned `j` variable from the latch edge.

---

### P6 Missing test coverage for the true-then-false loop pattern

**What happened.** The unit test called
`dart_finds_bug_with_per_visit_ssa_freshening` was supposed to test
the case where a loop header is visited twice with opposite branch
directions (true on entry, false on exit). But the `phi2` chosen
(`x != 0`) had a 0-iteration witness (`x < 0`), so DART found the bug
without ever entering the loop body. The true-then-false pattern was
never exercised.

**Why this matters.** The retroactive-substitution bug (P1) does NOT
affect 0-iteration paths — it only affects multi-header-visit paths.
A test that only exercises the 0-iteration case gives false confidence
that the multi-visit path works.

**The fix.** Use a `phi2` that is violated specifically by the
1-iteration path and NOT by the 0-iteration path. Example:

```
CFG: entry → cond(cmp=x>0) →[cmp] body(x:=x-1) →[True] cond →[!cmp] assert
violation phi2 = ¬(x > 0) = x ≤ 0

0-iter witness: x = -1. cmp = false, exit immediately. phi2 = (-1 ≤ 0) = True. Feasible.
1-iter witness: x = 1. cmp = true, body x→0, cmp$v2 = (0>0) = false, exit. phi2 = (0 ≤ 0) = True. Feasible.
```

The 1-iter path exercises the true-then-false pattern:
- 1st cond visit: `%cmp = (x > 0)`, guard `%cmp` (true).
- 2nd cond visit: `%cmp$nNv2 = (x-1 > 0)`, guard `!%cmp$nNv2` (false).

If P1 is present, `%cmp` gets retroactively rewritten to `%cmp$nNv2`
and the formula contains `%cmp$nNv2 ∧ !%cmp$nNv2` = UNSAT. The test
would return `Unknown` instead of `BugFound`, catching the regression.

---

### P7 Memory-state interaction with retroactive rewrite

**What happened.** Even after fixing P1 (removing the final
substitution), a subtler retroactive rewrite remained: the `_` arm
(P4) was calling `substitute_memory_in_formula_v2(formula, ...)` on
the ACCUMULATED formula, which rewrote memory expressions in older
constraints to use the LATEST memory_state. For example, a load
`array_val = select(store(initial, j, X), j)` added at iteration 1
would be rewritten at iteration 2 to
`array_val = select(store(store(initial, j, X), j2, X2), j)`, which
changes the meaning of the first-iteration load.

**The fix.** The `_` arm becomes a no-op (P4 fix). Memory reads are
substituted **at the point they are applied** via the `apply_path_effect`
call for `Assign` effects, which calls
`substitute_memory_in_term_v2(t, current_version, memory_state)` on
the term BEFORE adding the constraint. Once the constraint is added to
`formula`, neither `memory_state` nor `current_version` is allowed to
retroactively change it.

---

### P8 Invariant: "formula is append-only"

A way to think about all the above pitfalls:

> **The formula is append-only. Once a conjunct is added, it is never
> modified, substituted, or rewritten.**

Every violation of this invariant was a bug:
- P1: final substitution violated it for all frozen guards.
- P4: the `_` arm violated it for all frozen constraints when sp was
  applied to the whole formula.
- P7: same violation for memory expressions in frozen constraints.

The `current_version` and `memory_state` maps are lookup tables used
only when **adding** new conjuncts. They are write-only from the
formula's perspective: they update to reflect the latest program
state, and their values are baked in permanently when each conjunct is
appended.

If you ever write code that takes `formula` as input and produces a
modified `formula` (other than `formula ∧ new_conjunct`), stop and
think whether you are violating this invariant.

---

## 10. Future extensions

- **Branch-flipping search.** Classical DART runs one path, then
  asks the solver "what input flips the *last* branch?" producing a
  guided tour rather than blind DFS enumeration.
- **Lifting to `MustSummary`.** When DART finds a witness, scope the
  path condition to the procedure's formals (Skolemising locals via
  `skolemise.rs`) and add it as a `MustSummary`. Callers can then
  short-circuit via `MUST-POST-USESUMMARY`.
- **Path scoring.** Prioritize paths that touch `nondet_int()` or
  unconstrained variables.
- **Engine-wide memory SSA.** DART's local `memory_state` compensates
  for the global `sp(MemoryStore)` no-op, but the not-may pillar's
  omega propagation still suffers. Fixing globally requires
  fresh-name-per-store renaming in `abstract_cfg.rs::sp_one`.
