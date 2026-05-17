# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

> **Note**: This file is only updated on the `stable` branch (via CI).
> Do not commit benchmark runs from `main`.

---

## 2026-05-17 — `116c4dd`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 0 | 10 |
| locks | 4 | 0 | 8 | 1 | 0 | 0 | 13 |
| loop-crafted | 6 | 1 | 2 | 0 | 0 | 0 | 9 |
| loop-invariants | 9 | 1 | 0 | 0 | 0 | **2** | 10 |
| loops | 37 | 12 | 14 | 0 | 0 | **15** | 63 |
| **Total** | **66** | **14** | **24** | **1** | **0** | **17** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/array-2` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/for_bounded_loop1` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/heavy-1` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/ludcmp` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/nec20` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/string-2.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE
  - MISSED:  `c/loop-invariants/linear-inequality-inv-b` expected UNSAFE, got SAFE

---

---


## 2026-05-16 — `4261cf4`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 0 | 13 |
| loop-crafted | 3 | 1 | 5 | 0 | 0 | 9 |
| loop-invariants | 9 | 1 | 0 | 0 | **2** | 10 |
| loops | 20 | 10 | 33 | 0 | **8** | 63 |
| **Total** | **42** | **12** | **51** | **0** | **10** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/array-2` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/ludcmp` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/nec20` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE
  - MISSED:  `c/loop-invariants/linear-inequality-inv-b` expected UNSAFE, got SAFE


---

