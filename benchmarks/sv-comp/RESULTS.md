# SV-COMP Benchmark Results

Newest run first.  Each section shows verdict counts per category
and flags any soundness or completeness anomalies.

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

