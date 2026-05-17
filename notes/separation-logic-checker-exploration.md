# Exploratory Idea: Separation Logic-Based Bug Finder

## Status: EXPLORATORY — not started

## Motivation

The current may/must checker works well for stack-allocated and globally-allocated
memory with static structure.  It cannot soundly handle:

- Use-after-free (no ownership model)
- Double free
- Memory leaks
- Heap aliasing across call sites

The natural extension is a separation logic (SL)-based tool that tracks heap
ownership.  Rather than extending the current tool, this would be a separate
binary that reuses the LLVM and SMT infrastructure but has a fundamentally
different analysis core.

## The Core Idea

Instrument C programs with ownership assertions derived from common bug patterns,
then verify them using an incorrectness-logic-flavored bidirectional analysis over
a separation logic memory model:

```
Bug pattern            Instrumentation
─────────────────────────────────────────────────────────
Null dereference       assert(ptr != NULL) before each load/store
Use-after-free         ownership consumed by free(); assert ownership at dereference
Double free            assert ownership not already consumed at free() site  
Memory leak            assert all heap ownership transferred or freed at exit
Uninitialized var      undef tracking at LLVM IR level
Integer overflow       assert no wrap before each arithmetic op
```

This is the approach taken by SV-COMP's MemorySafety category (programs are
pre-instrumented with `__VERIFIER_error()` at potential violation sites) and by
CBMC (instruments every dereference and arithmetic op internally).

## Theoretical Grounding

**Incorrectness logic** (O'Hearn, POPL 2020) is the right foundation for the
bug-finding direction.  The current may/must checker already does this for
assertion reachability:

- Forward `reach` — over-approximates reachable states (Hoare-flavored)
- Backward `state` — WP of violation = incorrectness precondition
- Combined check — `reach AND state` feasible at entry → real bug witness

**Incorrectness Separation Logic** (ISL, Raad et al., CAV 2020) extends this to
heap ownership.  The `*` (separating conjunction) connective provides:

- Disjoint ownership: `P * Q` holds on non-overlapping heap regions
- Points-to predicate: `x ↦ v` means x owns the cell containing v
- Frame rule: reasoning about a function only needs its spatial footprint;
  everything else is preserved automatically without havocing

Meta's **Pulse** analyzer (Infer) implements ISL for null deref and UAF at scale
(OOPSLA 2022: "Finding Real Bugs in Big Programs with Incorrectness Logic").

## What Is Reusable From This Repo

| Component | Reuse | Notes |
|---|---|---|
| `llvm_utils/llvm_wrap.rs` | High | LLVM C API bindings, fully tool-agnostic |
| `llvm_utils/program_graph.rs` | Partial | Graph skeleton yes; instruction effects different |
| `smt/solver.rs` | High | Z3 bindings; need to extend for heap entailment |
| `common/formula.rs` | Partial | Arithmetic terms stay; SL connectives are new |
| `common/abstract_cfg.rs` | Low | CFG structure yes; WP computation replaced |
| `common/adapter.rs` | Low | Rewritten for ownership effects |
| `common/alias_analysis.rs` | None | Ownership IS the alias information in SL |
| `may_must_analysis/` | Low | Algorithmic patterns may survive; formulas replaced |
| `build.rs`, CI, LLVM toolchain setup | Full | This is the biggest reason not to split repos |

## Planned Architecture

```
Instrumenter
  └─ LLVM IR pass (extends program_graph.rs)
  └─ Injects ownership assertions at malloc/free/deref sites

SL Formula layer
  └─ Points-to: x ↦ v
  └─ Separating conjunction: P * Q
  └─ Symbolic heap: list of (addr, value) pairs + pure arithmetic constraints

SL Transfer effects (replaces abstract_cfg.rs effects)
  └─ Alloc(x)       → x ↦ _
  └─ Store(x, v)    → x ↦ v
  └─ Load(x)        → requires x ↦ _
  └─ Free(x)        → consumes x ↦ _
  └─ Call(f, args)  → frame + footprint from summary

SL Oracle (extends oracle.rs)
  └─ Heap entailment: does symbolic heap h1 entail h2?
  └─ SMT for arithmetic (reuse existing Z3 layer)
  └─ Smallfoot-style entailment procedure for SL formulas

Incorrectness analysis core (replaces may_must_analysis/)
  └─ Backward: ISL incorrectness WP from error site
  └─ Forward: reachable ownership states from entry
  └─ Combined check: real bug witness or safe
```

## Repo Strategy

Do **not** split into a new repo.  The LLVM build infrastructure (`build.rs`,
`llvm-sys`, LLVM version pinning, CI toolchain setup) is the hardest part to
duplicate and maintain.

When ready to start:
1. Add as a second binary in this repo (`src/bin/sl_checker.rs` or `sl/` dir)
2. Copy (do not extract yet) `llvm_utils/` and `smt/` into the new binary
3. Once the SL tool is mature enough to see the sharing boundary clearly,
   convert to a Cargo workspace with shared crates

## Literature

- O'Hearn, "Incorrectness Logic", POPL 2020
  (search: "Incorrectness Logic O'Hearn POPL 2020")

- Raad, Brochenin, Toumi, Dreyer, Villard, O'Hearn,
  "Local Reasoning About the Presence of Bugs: Incorrectness Separation Logic",
  CAV 2020
  (search: "Incorrectness Separation Logic CAV 2020")

- Le, Raad, Villard, Berdine, Dreyer, O'Hearn,
  "Finding Real Bugs in Big Programs with Incorrectness Logic",
  OOPSLA 2022  ← most directly relevant; describes Pulse/Infer at scale
  (search: "Finding Real Bugs in Big Programs with Incorrectness Logic OOPSLA 2022")

- Calcagno, Distefano, O'Hearn, Yang,
  "Compositional Shape Analysis by means of Bi-Abduction", POPL 2009
  (search: "Bi-Abduction Compositional Shape Analysis POPL 2009")
  ← describes the technique that makes Infer scale interprocedurally

- Clarke, Kroening, et al., "CBMC: Bounded Model Checking for ANSI-C", TACAS 2004
  (search: "CBMC Bounded Model Checking ANSI-C TACAS 2004")
  ← describes the instrumentation approach for memory safety encoding

- SV-COMP MemorySafety property file:
  search "sv-comp sosy-lab memsafety" for the property encoding spec

## Prerequisites Before Starting

1. Current tool reaches good stability on loop/integer benchmarks
2. Instruction coverage gaps in `TODO.md` addressed
3. Heap model (TODO Step 4) explored — that work will clarify how much of the
   current memory model is salvageable vs. needs SL from scratch
