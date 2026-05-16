# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

---

## 2026-05-16 — `970a9dd`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Wrong | Total |
|---|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 0 | 13 |
| loop-crafted | 3 | 0 | 6 | 0 | 0 | 9 |
| loop-invariants | 3 | 1 | 6 | 0 | **1** | 10 |
| loops | 18 | 10 | 35 | 0 | **8** | 63 |
| **Total** | **34** | **11** | **60** | **0** | **9** | **105** |

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

---

## 2026-05-16 — `fb42c7e`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |
|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 13 |
| loop-crafted | 3 | 0 | 6 | 0 | 9 |
| loop-invariants | 3 | 1 | 6 | 0 | 10 |
| loops | 18 | 10 | 35 | 0 | 63 |
| **Total** | **34** | **11** | **60** | **0** | **105** |

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

---

## 2026-05-16 — `bc36863`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |
|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 13 |
| loop-crafted | 3 | 1 | 5 | 0 | 9 |
| loop-invariants | 9 | 1 | 0 | 0 | 10 |
| loops | 18 | 12 | 33 | 0 | 63 |
| **Total** | **40** | **14** | **51** | **0** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/array-2` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/count_up_down-1` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/ludcmp` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/nec20` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/trex03-2` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE
  - MISSED:  `c/loop-invariants/linear-inequality-inv-b` expected UNSAFE, got SAFE

---

## 2026-05-16 — `91b75e8`

Run: all files

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |
|---|---|---|---|---|---|
| infeasible-control-flow | 10 | 0 | 0 | 0 | 10 |
| locks | 0 | 0 | 13 | 0 | 13 |
| loop-crafted | 3 | 1 | 5 | 0 | 9 |
| loop-invariants | 9 | 1 | 0 | 0 | 10 |
| loops | 18 | 12 | 33 | 0 | 63 |
| **Total** | **40** | **14** | **51** | **0** | **105** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/array-2` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/count_up_down-1` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/linear_sea.ch` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/ludcmp` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/nec20` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum01_bug02.i` expected UNSAFE, got SAFE
  - MISSED:  `c/loops/sum04-1.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/trex03-2` expected SAFE, got UNSAFE
  - UNSOUND: `c/loops/veris.c_NetBSD-libc_loop.i` expected SAFE, got UNSAFE
  - MISSED:  `c/loops/verisec_OpenSER_cases1_stripFullBoth_arr.i` expected UNSAFE, got SAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE
  - MISSED:  `c/loop-invariants/linear-inequality-inv-b` expected UNSAFE, got SAFE

---

## 2026-05-16 — `d20ec5b`

Run: --limit 5 (first 5 files per directory)

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |
|---|---|---|---|---|---|
| infeasible-control-flow | 5 | 0 | 0 | 0 | 5 |
| locks | 0 | 0 | 5 | 0 | 5 |
| loop-crafted | 1 | 1 | 3 | 0 | 5 |
| loop-invariants | 4 | 1 | 0 | 0 | 5 |
| loops | 2 | 1 | 2 | 0 | 5 |
| **Total** | **12** | **3** | **10** | **0** | **25** |

**Soundness / completeness flags:**
  - MISSED:  `c/loops/array-2` expected UNSAFE, got SAFE
  - UNSOUND: `c/loops/count_up_down-1` expected SAFE, got UNSAFE
  - UNSOUND: `c/loop-invariants/bin-suffix-5` expected SAFE, got UNSAFE

---

## 2026-05-16 — `d20ec5b`

Run: --limit 5 (first 5 files per category)

| Category | SAFE | UNSAFE | UNKNOWN | ERROR | Total |
|---|---|---|---|---|---|
| infeasible-control-flow | 0 | 0 | 5 | 0 | 5 |
| locks | 0 | 0 | 5 | 0 | 5 |
| loop-crafted | 0 | 0 | 5 | 0 | 5 |
| loop-invariants | 0 | 0 | 5 | 0 | 5 |
| loops | 0 | 0 | 5 | 0 | 5 |
| **Total** | **0** | **0** | **25** | **0** | **25** |

_No soundness flags._

---

