# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

> **Note**: This file is only updated on the `stable` branch (via CI).
> Do not commit benchmark runs from `main`.


## 2026-05-20 — `2a5f88b`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 0 | 0 | 13 |
| loop-crafted | 5 | 1 | 3 | 0 | 0 | 0 | 9 |
| loop-invariants | 5 | 1 | 4 | 0 | 0 | **1** | 10 |
| loops | 16 | 13 | 34 | 0 | 0 | **7** | 63 |
| **Total** | **36** | **15** | **54** | **0** | **0** | **8** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/nec40` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE



## 2026-05-21 — `a53ae94`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 0 | 0 | 13 |
| loop-crafted | 5 | 1 | 3 | 0 | 0 | 0 | 9 |
| loop-invariants | 5 | 1 | 4 | 0 | 0 | **1** | 10 |
| loops | 19 | 13 | 31 | 0 | 0 | **9** | 63 |
| **Total** | **39** | **15** | **51** | **0** | **0** | **10** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/n.c24.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/nec40` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/vogal-2.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE



---

