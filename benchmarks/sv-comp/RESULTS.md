# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

> **Note**: This file is only updated on the `stable` branch (via CI).
> Do not commit benchmark runs from `main`.

---

## 2026-05-20 — `577e672`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 12 | 1 | 0 | 0 | 13 |
| loop-crafted | 5 | 1 | 3 | 0 | 0 | 0 | 9 |
| loop-invariants | 5 | 1 | 4 | 0 | 0 | **1** | 10 |
| loops | 20 | 13 | 30 | 0 | 0 | **10** | 63 |
| **Total** | **40** | **15** | **49** | **1** | **0** | **11** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/n.c24.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/nec40` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE

---

---


## 2026-05-20 — `2a5f88b`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 9 | 4 | 0 | 0 | 13 |
| loop-crafted | 5 | 1 | 3 | 0 | 0 | 0 | 9 |
| loop-invariants | 5 | 1 | 4 | 0 | 0 | **1** | 10 |
| loops | 20 | 16 | 27 | 0 | 0 | **10** | 63 |
| **Total** | **40** | **18** | **43** | **4** | **0** | **11** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/n.c24.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/nec40` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE


---

