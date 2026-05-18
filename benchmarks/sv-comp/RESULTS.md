# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

> **Note**: This file is only updated on the `stable` branch (via CI).
> Do not commit benchmark runs from `main`.

---

## 2026-05-18 — `fc0a6a1`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 8 | 0 | 2 | 0 | 0 | 0 | 10 |
| locks | 1 | 0 | 6 | 6 | 0 | 0 | 13 |
| loop-crafted | 5 | 0 | 4 | 0 | 0 | 0 | 9 |
| loop-invariants | 3 | 1 | 6 | 0 | 0 | **1** | 10 |
| loops | 24 | 5 | 34 | 0 | 0 | **9** | 63 |
| **Total** | **41** | **6** | **52** | **6** | **0** | **10** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/heavy-1` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/invert_string-1` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE

---

---


## 2026-05-17 — `975add2`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | TIMEOUT | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|---|
| infeasible-control-flow | 7 | 0 | 3 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 0 | 0 | 13 |
| loop-crafted | 4 | 0 | 5 | 0 | 0 | 0 | 9 |
| loop-invariants | 1 | 0 | 9 | 0 | 0 | 0 | 10 |
| loops | 12 | 6 | 45 | 0 | 0 | **5** | 63 |
| **Total** | **24** | **6** | **75** | **0** | **0** | **5** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/compact` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/terminator_02-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/trex03-2_abstracted` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE


---

