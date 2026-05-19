# Bounded Model Checking (BMC)

Source: `src/may_must_analysis/bmc.rs`

BMC is a **bug-finding** complement to the bidirectional may/must analysis.
A `BugFound` result is a real counterexample (sound). Absence of a bug within
the bound is UNKNOWN — not a proof of safety. The proof engine (`backward.rs`,
`rules.rs`) is untouched; BMC lives entirely in `bmc.rs`.

---

## 1. Role in the Overall Flow

The intended flow is:

```
backward analysis (proof engine)
  → Verified          : assertion holds on all reachable executions
  → BugFound          : concrete counterexample found
  → Unknown           : neither proved nor refuted

  if Unknown and --bmc-bound N is given:
    BMC (bug-finding only)
      → BugFound      : real counterexample within N iterations
      → None          : no bug found within N iterations (still UNKNOWN)
```

BMC is an escalation path. It does not change `Verified` verdicts and cannot
produce them.  It can turn `Unknown` into `BugFound` when the proof engine
could not synthesize a loop invariant strong enough to find a witness.

---

## 2. Soundness of `BugFound` via BMC

Yes — `BugFound` from BMC is sound.

The unrolled CFG is a faithful, concrete (non-approximating) representation of
all executions that run the loop body at most k times.  `bmc_sat_check` computes
the exact WP of `NOT obligation` through this acyclic CFG and asks Z3 whether
the resulting formula is satisfiable.  A SAT witness is a concrete valuation of
all scalar variables and memory reads — it describes an actual execution trace
that reaches the assertion and violates it.

There are no over-approximations in the BMC path: no widening, no havoc beyond
what the unrolled CFG already contains, no spurious states injected.  The
unrolled CFG is more concrete than the original (it instantiates each iteration
separately), so a satisfying model for the unrolled formula is simultaneously a
satisfying model for the original program.

The only unsoundness direction is towards `Verified`: BMC can never prove safety
because it only covers a finite prefix of executions.  UNKNOWN is the correct
result when no bug is found.

---

## 3. Unrolling Strategy

For a loop with body `{H, B…, L}` and back edge `L→H`, unrolling to depth k:

```
Original:          H → B → L ──back──→ H
                        ↓ exit
                     post_loop

Unrolled k=2:      H₀ → B₀ → L₀ → H₁ → B₁ → L₁ → H₂ → B₂ → L₂ (dead end)
                              ↓           ↓           ↓
                         post_loop  post_loop  post_loop
```

- Iteration 0 reuses the original node IDs.
- Iterations 1..=k are fresh copies (k extra copies per depth k).
- Each copy's header carries the original exit edge, so the loop can exit
  after 0, 1, 2, …, or exactly k full iterations.
- The original back edge is removed after all copies are wired.

### Variable renaming across copies

Within each copy i (i = 1..=k), scalar SSA variable names are renamed with
suffix `_bmcI` (e.g. `main$%13` → `main$%13_bmc1`). Memory region names are
NOT renamed — they represent shared mutable state (the array, the accumulator)
that must be visible across iterations: stores from iteration i must be readable
in iteration i+1.

This uses the two-closure design from `src/common/alpha_rename.rs`:
```rust
let var_r = |name: &str| format!("{name}_bmc{i}");   // fresh scalar names
let reg_r = |name: &str| name.to_string();             // unchanged region names
```

---

## 4. Incremental Deepening

`bmc_check` tries k = 1, 2, …, bound in order and stops at the first bug:

```
for k in 1..=bound:
    bmc_cfg = clone(cfg); unroll(bmc_cfg, k); remove_back_edges(bmc_cfg)
    for each assertion copy in this depth:
        if bmc_sat_check(bmc_cfg, copy, oracle) → BugFound:
            return BugFound
    // no bug at depth k; try k+1
return None (UNKNOWN)
```

Bugs at small k are found without paying for deeper unrollings. For `array-2`,
k=1 finds the bug with one SAT query and zero wasted work.

---

## 5. The SAT Backend: `bmc_sat_check`

### Why not the proof engine

The original backend called `backward::analyze` (the bidirectional proof engine)
on the unrolled CFG. The proof engine is designed for proving safety, not for
finding bugs efficiently on acyclic CFGs:

| Problem | Source |
|---|---|
| O(edges) SMT queries per pass | `notmay_pre_pruned` fires one oracle call per edge |
| Multiple fixpoint passes | `run_to_fixpoint` iterates even though an acyclic CFG converges in one pass |
| Formula blowup | `join_state` OR-joins at merge points; with k copies, sizes grow |
| No timeout in Z3 | `oracle.rs` creates a fresh solver scope per query with no timeout |

With k = 8+ the proof engine becomes impractical.

### The algorithm (single WP pass)

`bmc_sat_check` computes exactly the same WP as `notmay_pre` + `join_state`
from `rules.rs`, but as a single topological pass with one final SAT query:

```
Seed:
  state[site.node] = site.node.transfer.wp(NOT obligation)

Backward pass (reverse topological order):
  for node in reversed_topo:
    if state[node] not set: skip
    for each incoming edge (src → node):
      edge_pre = edge.transfer().wp(state[node])   // same as notmay_pre: edge_pre
      guarded  = edge.guard ∧ edge_pre             // same as notmay_pre: post_at_source
      src_pre  = src.transfer.wp(guarded)          // same as notmay_pre: pre_at_source
      state[src] |= src_pre                        // same as join_state (OR)

Decision:
  report = oracle.feasibility_with_model(state[entry])
  SAT  → BugFound { model = report.model }
  else → None
```

The only differences from the proof engine:
1. **No `reach` component** — no loop invariants to inject (the loop is unrolled).
2. **No `notmay_pre_pruned`** — skips intermediate SMT queries; the `reach`-based
   pruning is meaningless without real forward information.
3. **One pass, not a fixpoint** — topological order gives immediate convergence
   on acyclic CFGs; the fixpoint loop is unnecessary.
4. **One SMT query** at the entry, not O(edges) queries throughout.

### Complexity

O(|CFG|) work in the WP pass, O(1) SMT queries per depth k.  Total across
incremental deepening: O(bound) SAT queries in the worst case.

---

## 6. Limitations

- **Nested loops**: not supported. `bmc_check` returns None immediately.
  Independent (non-nested) loops are each unrolled with the same bound k.
- **Symbolic loop bounds**: if the loop bound depends on a runtime value (not
  a compile-time constant), a user-supplied `--bmc-bound N` is required.
- **Only bug-finding**: cannot prove safety. If the bound is not enough to
  reach the bug, BMC returns UNKNOWN.

---

## 7. Future Work: Loop Bound Discovery

Currently the user must supply `--bmc-bound N`. For many programs the correct
bound is derivable from the CFG without any SMT:

1. Inspect the loop header's exit edge condition (e.g. `counter < SIZE`).
2. Scan the preheader (nodes dominating the loop header, no back-edge
   predecessor) for concrete `MemoryStore` facts —
   e.g. `MemoryStore { region: stack$SIZE, offset: 0, value: Int(1) }`.
3. Substitute constant-valued region reads in the exit condition.
   If the result reduces to `counter < 1`, the bound is 1.

This is purely syntactic constant-folding through the `PointerEnv`; no SMT
needed. It would auto-select the right bound (e.g. `array-2` → 1) and
eliminate the need for a CLI flag in common cases. For symbolic bounds, fall
back to the user-supplied `--bmc-bound` or skip BMC.
