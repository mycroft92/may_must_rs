# SV-COMP Benchmark Runner

Scaffolding to run Smash-plus-ultra against selected SV-COMP benchmark
categories and collect a per-file verdict summary.

---

## Quick start

### All-in-one (recommended)

`bench.sh` sparse-clones sv-benchmarks, runs the checker, updates `RESULTS.md`,
then deletes the clone.  No manual setup needed.

```sh
# From the repo root — builds the checker if needed:
cargo build --release

# Run all active categories (can take a while):
./benchmarks/sv-comp/bench.sh

# Quick sanity check — first 20 files per category:
./benchmarks/sv-comp/bench.sh --limit 20

# Commit the updated RESULTS.md automatically:
./benchmarks/sv-comp/bench.sh --limit 20 --commit
```

`RESULTS.md` is updated in place (newest run first) and is committed to the
repo so benchmark progress is tracked over time.

### Manual (step-by-step)

If you want to keep the sv-benchmarks clone around for repeated runs:

```sh
# 1 — Clone sv-benchmarks (sparse, ~100 MB for two categories):
git clone --depth 1 --filter=blob:none --sparse \
    https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git \
    /path/to/sv-benchmarks
cd /path/to/sv-benchmarks
git sparse-checkout set properties c/ReachSafety-Loops c/ReachSafety-ControlFlow
cd -

# 2 — Build the checker:
cargo build --release

# 3 — Run:
./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks --limit 20
```

---

## File layout

```
benchmarks/sv-comp/
├── README.md           This file.
├── RESULTS.md          Benchmark results — updated each run, committed to repo.
├── categories.txt      Which benchmark subdirectories to run (one per line).
├── svcomp_shim.h       Maps __VERIFIER_* sentinels to our intrinsics.
├── convert.py          Transforms a single SV-COMP .c file for our checker.
├── bench.sh            All-in-one: clone → run → update RESULTS.md → delete clone.
├── run.sh              Low-level: iterate categories, compile, check, write CSV.
├── update_results.py   Parse CSV and prepend a new section to RESULTS.md.
└── out/                Generated (gitignored) — converted sources and bitcode.
```

---

## How it works

### Sentinel mapping

| SV-COMP sentinel | Our intrinsic | Semantics |
|---|---|---|
| `__VERIFIER_error()` | `may_assert((_Bool)0)` | Assert false — prove this call is unreachable |
| `__VERIFIER_assume(cond)` | `assume((_Bool)(cond))` | Prune infeasible paths |
| `__VERIFIER_nondet_*()`  | extern stub | Unconstrained input — models nondeterminism |

### Conversion pipeline (per file)

1. `convert.py` strips `extern void __VERIFIER_error` / `__VERIFIER_assume`
   declarations (they would collide with the macros defined in `svcomp_shim.h`)
   and strips standalone function-body definitions for those sentinels.
2. `#include "svcomp_shim.h"` is prepended so call sites expand correctly.
3. `clang -O0 -g -fno-inline` compiles the converted file to LLVM bitcode.
4. The checker runs on the bitcode and emits `SAFE`, `UNSAFE`, or `UNKNOWN`.

### Expected verdict

Each SV-COMP task has a `.yml` file with `expected_verdict: true` (safe) or
`false` (unsafe).  `run.sh` reads this and records it in the CSV alongside the
checker's verdict, making it easy to spot unsound results (`SAFE` when expected
`false`) or missed bugs (`UNSAFE` when expected `true`).

### CSV output

```
file,category,expected,verdict,time_s
loop_forever,c/ReachSafety-Loops,unsafe,UNSAFE,0.3
count_up_down,c/ReachSafety-Loops,safe,SAFE,1.1
```

---

## Choosing categories

Edit `categories.txt` to add or remove categories.  The file ships with two
active categories and several commented-out ones:

| Category | Active | Reason |
|---|---|---|
| `c/ReachSafety-Loops` | ✅ | Best fit — loop invariant synthesis is the core feature |
| `c/ReachSafety-ControlFlow` | ✅ | Acyclic integer programs — exercises WP directly |
| `c/ReachSafety-ECA` | commented | State-machine programs; enable once Loops is stable |
| `c/ReachSafety-BitVectors` | commented | Needs broader bitwise-op coverage |
| `c/ReachSafety-Arrays` | commented | Many benchmarks need heap model (Step 4) |

---

## Known limitations

- **Floating-point**: programs with `float`/`double` variables produce
  `UNKNOWN` (checker reports "unsupported").
- **Heap allocation**: `malloc`/`new` are not modelled; programs relying on
  heap aliasing produce `UNKNOWN`.
- **Concurrency**: out of scope — do not include `c/Concurrency-*` categories.
- **Nondet return values**: `__VERIFIER_nondet_*()` calls are treated as
  opaque external calls, which is sound (over-approximating) but may increase
  `UNKNOWN` for programs where the return value is load-bearing.
