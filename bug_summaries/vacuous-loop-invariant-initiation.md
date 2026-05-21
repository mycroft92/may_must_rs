# Bug: Vacuous Loop Invariant Initiation via False Reach

**Found in**: v0.19.1 (exposed by `benchmarks/sv-comp/out/compact.c`)  
**Fixed in**: v0.20.0  
**File**: `src/analysis/loops/mod.rs`, `check_loop_invariant_verbose`

## Symptom

`compact.c` returned **SAFE** when the correct verdict is **UNSAFE**.

The program fills an array with random bytes and then searches for a specific
random byte.  If no element matches, `reach_error()` is called.  Because all
values are nondeterministic it is possible that no match exists, so the error
is reachable.

## Root Cause

`check_loop_invariant_verbose` uses `forward_reach_at_header` to compute an
over-approximation of the forward reach at the loop header before checking
initiation.  This is computed from the acyclic CFG skeleton (all back edges
excluded).

For the search loop in `compact.c`, the acyclic skeleton is:

1. Fill loop preheader: `i = 0`
2. Fill loop body contains `__VERIFIER_nondet_char()` (an unknown call →
   `HavocMemory`), which clears all concrete store facts from the SP pass.
3. Fill loop exit guard: `i >= 102400`.  With `i = 0` this guard is
   unsatisfiable in the acyclic skeleton → fill loop exit is unreachable.
4. Search loop preheader is unreachable → `forward_reach_at_header` returns
   `Formula::False` for the search loop.

With `reach_h = False`:

```
initiation_violation = False ∧ ¬candidate = False
```

`oracle.feasibility(False) = Infeasible` → initiation **passes for every
candidate**, including semantically absurd ones like `i < 0`.

The exit closure check then also passed vacuously for `i < 0`: the exit
condition for the search loop is `i ≥ 102400`, and `i < 0 ∧ i ≥ 102400` is
infeasible in integer arithmetic, so exit closure appeared to succeed.

The accepted invariant `i < 0` was injected into `reach` at the search loop
header, forcing `reach ∧ state = False` at the function entry and producing a
spurious **Verified / SAFE** verdict.

Note: `reach_h = False` is an artefact of the acyclic skeleton approximation
for sequential counting loops.  The search loop **is** reachable in the real
program — the fill loop's back edge drives `i` to `102400`, it exits, the
search loop resets `i = 0`.  The acyclic skeleton cannot model that path
because back edges are excluded.

## Fix

After the initiation check passes, add an additional feasibility guard:

```rust
let reach_at_entry = Formula::and(reach_h, candidate.clone());
match oracle.feasibility_with_model(&reach_at_entry) {
    Ok(report) if report.feasibility != Feasibility::Feasible => {
        return InvariantCheckResult::InitiationFailed { witness: None };
    }
    Err(_) => return InvariantCheckResult::InitiationFailed { witness: None },
    _ => {}
}
```

This rejects any candidate for which `reach_h ∧ candidate` is infeasible.
That covers both:

- `reach_h = False` (loop header unreachable in acyclic skeleton) — any
  candidate is rejected because its conjunction with False is always False.
- `reach_h ≠ False` but `candidate` is impossible at every reachable entry
  state — also rejected.

**Soundness**: rejecting these candidates is safe.  A candidate that never
actually holds at a reachable loop entry cannot serve as a useful invariant;
accepting it only creates spurious infeasibility in `reach ∧ state`.

## Result After Fix

`compact.c` returns **UNKNOWN** (sound): the backward analysis cannot
synthesize a valid loop invariant for the search loop (no candidate survives
the vacuous-initiation guard), and DART exhausts its path budget before finding
a concrete counterexample through 102400 loop iterations.  UNKNOWN is correct
and sound; the previous SAFE verdict was unsound.
