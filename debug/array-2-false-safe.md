# Debug: array-2 Returns SAFE Instead of UNSAFE

**Benchmark:** `benchmarks/sv-comp/c/loops/array-2`
**Expected verdict:** UNSAFE
**Actual verdict:** SAFE (false positive — unsound)
**Discovered:** 2026-05-17
**Status:** FIXED in v0.7.4

---

## What the Benchmark Does

`array-2` is an SV-COMP loop benchmark with an assertion that is reachable and
violable.  The program iterates over an array, and the assertion fires on a
value derived from the array contents.  The assertion should produce `UNSAFE`
(or at worst `UNKNOWN`), but the analysis currently emits `SAFE`.

---

## Symptom

The analysis reports `Verified` for the assertion in `array-2`.  This is a
**false safe** — the assertion is actually violable, so `Verified` is unsound.

---

## Root Cause Trace

The false safe is produced by the precomputed loop invariant path.  The full
call chain:

```
analyze_module_with_llm
  │
  ├─ discover_loop_invariants(cfg, "main", oracle)
  │    Finds algorithmic invariant I = (i >= 0 && i <= N)   [induction on counter]
  │    Initiation: passes
  │    Inductiveness: passes
  │    Exit closure: SKIPPED (discover_loop_invariants has no assertion site)
  │    → stored in SummaryTables
  │
  └─ analyze_with_summaries("main", …, tables, config=Some)
       precomputed = tables.get_loop_invariants("main") = [(header, I)]
       analyze_with_tables(cfg, "main", site, oracle, tables, config, precomputed)
         │
         ├─ precomputed_satisfy_exit_closure(cfg, site, [(header, I)], oracle, excluded)
         │    for loop_info:
         │      loop_writes_obligation_vars(loop_info, cfg, obligation) → FALSE   ← BUG
         │      ∴ exit closure skipped, invariant accepted
         │    returns Ok(true)
         │
         ├─ exit_closure_ok = true
         │  → use precomputed invariant I directly
         │
         └─ run_backward(cfg, site, oracle, excluded, [(header, I)], tables)
              I injected into reach at header
              Backward state from assertion collapses to False at entry
              (I tightly constrains the counter; violation path is pruned)
              reach AND state = False at entry → Verified  ← FALSE SAFE
```

---

## The Bug: `loop_writes_obligation_vars` Returns False

`loop_writes_obligation_vars` in `backward.rs` is supposed to detect whether
the loop body can affect the assertion obligation.  If the loop is irrelevant,
exit closure is skipped (an optimisation).

The function checks two sets:

**`obligation_names`** — variable and memory region names appearing in
`site.obligation`, collected by `collect_formula_names`.

**`loop_writes`** — targets written in the loop body: `Assign { target }` names
and `MemoryStore { region }` names.

It returns `true` if `loop_writes ∩ obligation_names ≠ ∅`.

### The Gap

In `array-2`, the assertion obligation is on a **loaded scalar** whose value was
loaded from the array before the assertion node.  After lowering:

```
obligation = (main$%loaded_val >= 0)     ← SSA name of the loaded value
```

The loop body writes to the array region:

```
MemoryStore { region: "main$stack0", offset: i, value: … }
```

So:

```
obligation_names = { "main$%loaded_val" }
loop_writes      = { "main$stack0", "main$%i_next" }
intersection     = ∅
```

`loop_writes_obligation_vars` returns `false` → loop is considered irrelevant
to the obligation → exit closure skipped → precomputed invariant `I` accepted.

But the assertion IS about the array contents — `%loaded_val` was loaded from
`main$stack0` earlier.  The function cannot see this connection because
`collect_formula_names` traverses the obligation formula syntactically; it
finds the SSA name of the load result, not the memory region that was loaded
from.

---

## Why This Causes a False Safe

The precomputed invariant `I = (i >= 0 && i <= N)` is injected into `reach` at
the loop header.  This narrows `reach` to states where the counter is in range.

The backward state from the assertion (`NOT obligation` propagated back) depends
on the array contents.  After injection, `run_backward` sees a `reach` that is
over-constrained (the counter bounds are tighter than the violation needs), and
the `reach AND state` conjunction at entry may become infeasible — not because
the program is actually safe, but because the invariant masked the path to the
violation.

Concretely: if exit closure had been checked with the real obligation, it would
have found that `I` does not block the violation at the loop exit (the array
contents are unconstrained by `I`).  Exit closure would fail → fall through to
`synthesize_loop_invariants` → CHC/Houdini tries to find a stronger invariant
→ either finds one that correctly discharges, or fails and returns `UNKNOWN`.

---

## Correct Behaviour

- If a correct, assertion-specific invariant exists and can be found:
  `BugFound` (the violation is reachable).
- If no invariant is found that discharges the obligation: `UNKNOWN` (safe to
  return — unsound to return Verified).

`SAFE` (`Verified`) is wrong here.

---

## Fix Applied (v0.7.4)

**Remove the two-phase `run_backward` for failed exit closure.**

The relevance optimisation (`loop_writes_obligation_vars` and helpers) was
removed in an earlier pass (v0.7.2).  `precomputed_satisfy_exit_closure` now
always runs the full three-part check.

The critical fix in v0.7.4: when exit closure fails for a precomputed
invariant, `run_backward` with that invariant is **not** attempted.  Using
`run_backward` here is unsound:

- The backward `state` from the exit condition (e.g. `j ≥ 1`) propagates
  backward through the loop initialization (`j = 0`) and collapses to `False`
  at the function entry — not because the assertion is safe, but because the
  direct entry→header→exit path is infeasible (the loop body, which increments
  `j`, is never traversed in the backward direction with back edges excluded).
- `reach AND False = False → Verified` — false safe, regardless of the
  invariant in `reach`.

When exit closure fails, synthesis is attempted directly.  If synthesis also
fails, the result is `UNKNOWN` (sound).

---

## Files Changed

- `src/may_must_analysis/backward.rs` — removed `loop_writes_obligation_vars`
  and helpers; simplified `precomputed_satisfy_exit_closure` to always check
  exit closure; removed dead imports (`Memory`, `TransferEffect`, `Term`)
- `Cargo.toml` — version bumped to 0.7.2

---

## Reproduction

```sh
# compile array-2 to bitcode (adjust path as needed)
clang -O0 -g -emit-llvm -c benchmarks/sv-comp/c/loops/array-2.c -o /tmp/array-2.bc

# run analysis — should return UNSAFE or UNKNOWN, currently returns SAFE
cargo run --bin main -- /tmp/array-2.bc --no-dot
```

To see the loop invariant decisions:

```sh
cargo run --bin main -- /tmp/array-2.bc --no-dot --debug-invariants 2>&1 | grep -E "loop|precomputed|exit.closure"
```
