# SV-COMP Benchmark Runner

Scaffolding to run Smash-plus-ultra against selected SV-COMP benchmark
categories and collect a per-file verdict summary.

---

## Quick start

### 1 — Clone sv-benchmarks (once, outside this repo)

```sh
git clone git@gitlab.com:sosy-lab/benchmarking/sv-benchmarks.git \
    /path/to/sv-benchmarks
```

The repo is large; a shallow clone saves disk space:

```sh
git clone --depth 1 git@gitlab.com:sosy-lab/benchmarking/sv-benchmarks.git \
    /path/to/sv-benchmarks
```

### 2 — Build the checker

```sh
# From the repo root:
cargo build --release
```

### 3 — Run

```sh
./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks
```

By default this runs every `.c` file in the categories listed in
`categories.txt` and writes a CSV summary to `benchmarks/sv-comp/results.csv`.

Useful flags:

```sh
# Only the first 20 files per category (good for a quick sanity check):
./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks --limit 20

# Custom category list:
./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks \
    --categories my_categories.txt

# Write results to a different file:
./benchmarks/sv-comp/run.sh --benchmarks /path/to/sv-benchmarks \
    --csv /tmp/svcomp_results.csv
```

---

## File layout

```
benchmarks/sv-comp/
├── README.md          This file.
├── categories.txt     Which benchmark subdirectories to run (one per line).
├── svcomp_shim.h      Maps __VERIFIER_* sentinels to our intrinsics.
├── convert.py         Transforms a single SV-COMP .c file for our checker.
├── run.sh             Iterates over categories; compiles and checks each file.
└── out/               Generated (gitignored) — converted sources and bitcode.
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
