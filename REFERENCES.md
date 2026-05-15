# References

Academic references for every technique implemented or planned in this tool,
grouped by the component that uses them.

---

## 1. Core Bidirectional Analysis

**[Godefroid2010]**
Godefroid, P., Nori, A.V., Rajamani, S.K., and Tetali, S.D. (2010).
"Compositional May-Must Program Analysis: Unleashing the Power of Alternation."
*POPL 2010*, pp. 43–56. ACM.
https://dl.acm.org/doi/10.1145/1707801.1706307

*The paper this tool implements.  The bidirectional reach/state pair,
the combined feasibility check at entry, and the interprocedural summary
reuse are all taken directly from this paper.*

---

## 2. Weakest Precondition / Strongest Postcondition

**[Dijkstra1975]**
Dijkstra, E.W. (1975).
"Guarded Commands, Nondeterminacy and Formal Derivation of Programs."
*Communications of the ACM 18*(8), pp. 453–457.

*The `wp_one` / `sp_one` functions in `abstract_cfg.rs` implement the
standard WP calculus.  The substitution-based WP rules for assignments
(`post[target ← value]`) and memory updates
(`post[region ← store(region, offset, value)]`) follow Dijkstra's original
formulation.*

**[Floyd1967]**
Floyd, R.W. (1967).
"Assigning Meanings to Programs."
*Mathematical Aspects of Computer Science*, AMS, pp. 19–32.

*Floyd's inductive assertion method underpins the loop invariant checks
in `loops.rs`: initiation, inductiveness, and (when required) exit closure
are exactly Floyd's three conditions on inductive invariants.*

---

## 3. Loop Invariant Synthesis

### 3a. Candidate-Based Inference (Houdini)

**[Flanagan2001]**
Flanagan, C. and Leino, K.R.M. (2001).
"Houdini, an Annotation Assistant for ESC/Java."
*FME 2001*, LNCS 2021, pp. 500–517. Springer.

*`houdini_candidates` in `loops.rs` generates a large template set (linear
bounds `x ≥ c`, `x ≤ c`, range conjunctions, pairwise comparisons) and
eliminates candidates that fail the initiation or inductiveness check.
This is exactly the Houdini algorithm: start with the conjunction of all
candidates and delete any that are not inductive.*

### 3b. Constrained Horn Clause Solving

**[Komuravelli2014]**
Komuravelli, A., Gurfinkel, A., and Chaki, S. (2014).
"SMT-Based Model Checking for Recursive Programs."
*CAV 2014*, LNCS 8559, pp. 17–34. Springer.

*`chc.rs` encodes the loop-invariant problem as a system of Constrained
Horn Clauses and delegates to Z3's CHC / SPACER engine (via the fixedpoint
API).  The CHC formulation of loop invariant inference — `pre(x) ∧ body(x,x') ⇒ pre(x')` as a Horn clause — is due to Komuravelli et al.*

**[Bjorner2015]**
Bjørner, N., Gurfinkel, A., McMillan, K., and Rybalchenko, A. (2015).
"Horn Clause Solvers for Program Verification."
*Fields of Logic and Computation II*, LNCS 9300, pp. 24–51. Springer.

*Background on the CHC solving approach implemented in `chc.rs`; the
SPACER algorithm (implemented inside Z3 as `z3::Fixedpoint`) is described
in §4.*

**[Een2011]**
Eén, N., Mishchenko, A., and Brayton, R. (2011).
"Efficient Implementation of Property Directed Reachability."
*FMCAD 2011*, pp. 125–134. IEEE.

*IC3 / PDR, the predecessor of SPACER.  Z3's `Fixedpoint` solver uses a
PDR-derived algorithm internally.*

### 3c. Algorithmic Pattern Matching

**[Cousot1977]**
Cousot, P. and Cousot, R. (1977).
"Abstract Interpretation: A Unified Lattice Model for Static Analysis
of Programs by Construction or Approximation of Fixpoints."
*POPL 1977*, pp. 238–252. ACM.

*`algorithmic_candidates` in `loops.rs` uses interval analysis (counter
bounds derived from back-edge guards) to produce candidates of the form
`0 ≤ i ∧ i ≤ n`.  This is a special case of the interval abstract domain
from Cousot & Cousot.*

### 3d. CEGIS with LLM

**[Solar-Lezama2006]**
Solar-Lezama, A., Tancau, L., Bodik, R., Seshia, S., and Saraswat, V. (2006).
"Combinatorial Sketching for Finite Programs."
*ASPLOS 2006*, pp. 404–415. ACM.

*The LLM-guided invariant synthesis in `backward.rs` follows the
Counterexample-Guided Inductive Synthesis (CEGIS) loop introduced here:
propose a candidate, check it, extract a counterexample on failure, and
feed the counterexample back to the synthesiser (the LLM).*

---

## 4. SMT Solving

**[deMoura2008]**
de Moura, L. and Bjørner, N. (2008).
"Z3: An Efficient SMT Solver."
*TACAS 2008*, LNCS 4963, pp. 337–340. Springer.

*All satisfiability and validity queries go through `oracle.rs`, which
calls Z3 via the `z3` Rust crate.  Z3 handles quantifier-free linear
arithmetic, array theory, and the CHC / SPACER engine used in `chc.rs`.*

**[McCarthy1962]**
McCarthy, J. (1962).
"Towards a Mathematical Science of Computation."
*IFIP Congress 1962*, pp. 21–28.

*The `select`/`store` array theory used to encode memory in `formula.rs`
is McCarthy's array model.  The WP rule for `MemoryStore` —
`post[region ← store(region, offset, value)]` — is the direct application.*

---

## 5. Memory Model and Pointer Analysis

### 5a. Stack Regions and Pointer Environment

**[Necula2002]**
Necula, G.C., McPeak, S., Rahul, S.P., and Weimer, W. (2002).
"CIL: Intermediate Language and Tools for Analysis and Transformation
of C Programs."
*CC 2002*, LNCS 2304, pp. 213–228. Springer.

*The `PointerEnv` design — mapping SSA pointer names to `(region, offset)` pairs via a forward dataflow pass — follows the C intermediate language
tradition of making pointer provenance explicit before analysis.*

### 5b. Struct Field Regions (Step 2)

**[Pearce2004]**
Pearce, D.J., Kelly, P.H.J., and Hankin, C. (2004).
"Efficient Field-Sensitive Pointer Analysis of C."
*PASTE 2004*, pp. 37–42. ACM.

*The `StructFieldGep` effect and the `{region}$f{N}` naming for per-field
regions implement field-sensitive pointer analysis at the abstract CFG level.
The access-path model (pointer + field sequence) in §2 of Pearce et al.
is the direct precedent.*

### 5c. Alias Analysis (Step 4 prerequisite)

See `ALIAS_ANALYSIS.md` for the full algorithm design and references.

Primary references: Andersen (1994), Steensgaard (1996), Pearce et al. (2004),
Hardekopf & Lin (2007), Hind (2001), Sui & Xue (2016).

### 5d. GEP Offset Calculation (Step 1)

**[LLVMRef]**
LLVM Project (2024).
"LLVM Language Reference Manual — getelementptr Instruction."
https://llvm.org/docs/LangRef.html#getelementptr-instruction

*The type-chain walking in `lower_gep` follows the GEP semantics exactly:
first index = pointer-level stride over the source element type; subsequent
indices = walk into array elements or struct fields using `TargetData`
(`LLVMOffsetOfElement`, `LLVMStoreSizeOfType`) for byte offsets.*

---

## 6. Interprocedural Analysis and Summaries

**[Godefroid2007]**
Godefroid, P. (2007).
"Compositional Dynamic Test Generation."
*POPL 2007*, pp. 47–54. ACM.

*Compositional summary reuse in `driver.rs` — computing a `ReturnSummary`
for each callee and splicing it as an `Obligation` at call sites — follows
the compositional test generation approach from §2.*

**[Reps1995]**
Reps, T., Horwitz, S., and Sagiv, M. (1995).
"Precise Interprocedural Dataflow Analysis via Graph Reachability."
*POPL 1995*, pp. 49–61. ACM.

*The bottom-up summary accumulation loop in `analyze_module_with_llm` —
process callees before callers, reuse computed summaries at call sites —
is a simplified instance of the IFDS/IDE framework for interprocedural
dataflow.*

**[McMillan2006]**
McMillan, K.L. (2006).
"Lazy Abstraction with Interpolants."
*CAV 2006*, LNCS 4144, pp. 123–136. Springer.

*The return-summary formula (a conjunction of relations between parameters
and the return value) is conceptually a Craig interpolant between the
callee's pre- and postcondition.  The `compute_return_summary` function
in `adapter.rs` derives it via backward WP rather than interpolation, but
the result plays the same role.*

---

## 7. Purity Analysis

**[Blanchet2003]**
Blanchet, B., Cousot, P., Cousot, R., Feret, J., Mauborgne, L.,
Miné, A., Monniaux, D., and Rival, X. (2003).
"A Static Analyzer for Large Safety-Critical Software."
*PLDI 2003*, pp. 196–207. ACM.

*`infer_memory_pure_functions` in `adapter.rs` classifies functions as
memory-pure (no stores, no impure callees) by a simple syntactic scan,
a conservative approximation of the escape analysis and purity inference
used in industrial static analysers like Astrée.*

---

## 8. Observer Invariant Pattern (Cyclic Callee Summaries)

**[Godefroid2010]** *(cited above)*

*The observer-invariant pattern in `driver.rs::infer_cyclic_observer_summary`
— synthesising `retval ≥ array[k]` for each accessed index k — is described
in §5 of Godefroid et al. (2010).  The tool's implementation extends it with
an explicit candidate-and-verify loop using the full bidirectional check.*

---

## 9. Counterexample Rendering

**[Clarke2003]**
Clarke, E., Grumberg, O., Jha, S., Lu, Y., and Veith, H. (2003).
"Counterexample-Guided Abstraction Refinement for Symbolic Model Checking."
*Journal of the ACM 50*(5), pp. 752–794.

*`render_counterexample` in `backward.rs` extracts an SMT model when
`reach AND state` is satisfiable and presents it as a human-readable
trace grouped by function.  The model extraction is the concrete
counterexample step of the CEGAR loop.*

---

## 10. LLVM Infrastructure

**[Lattner2004]**
Lattner, C. and Adve, V. (2004).
"LLVM: A Compilation Framework for Lifelong Program Analysis and
Transformation."
*CGO 2004*, pp. 75–88. IEEE.

*The tool operates directly on LLVM bitcode via the `llvm-sys` Rust
crate.  `llvm_wrap.rs` wraps the LLVM C API (`LLVMGetGEPSourceElementType`,
`LLVMOffsetOfElement`, `LLVMInstructionGetDebugLoc`, etc.).*

**[LLVMDebug]**
LLVM Project (2024).
"Source Level Debugging with LLVM."
https://llvm.org/docs/SourceLevelDebugging.html

*Debug metadata extraction in `llvm_wrap.rs` (`LLVMInstructionGetDebugLoc`,
`LLVMDILocationGetLine`, `LLVMDIFileGetFilename`) follows the DWARF-based
debug info encoding described in this reference.*

---

## Quick-Reference Index

| Component | File | Primary reference |
|-----------|------|-------------------|
| Bidirectional reach/state | `backward.rs` | [Godefroid2010] |
| WP / SP calculus | `abstract_cfg.rs` | [Dijkstra1975] |
| Loop invariant (Floyd conditions) | `loops.rs` | [Floyd1967] |
| Houdini candidate weakening | `loops.rs` | [Flanagan2001] |
| CHC / SPACER solver | `chc.rs` | [Komuravelli2014], [Bjorner2015] |
| IC3 / PDR (inside Z3) | `chc.rs` | [Een2011] |
| Algorithmic interval candidates | `loops.rs` | [Cousot1977] |
| LLM-guided CEGIS | `backward.rs` | [Solar-Lezama2006] |
| SMT solving | `oracle.rs`, `smt/solver.rs` | [deMoura2008] |
| Array theory (select/store) | `formula.rs` | [McCarthy1962] |
| Stack regions / PointerEnv | `adapter.rs` | [Necula2002] |
| Struct field regions (Step 2) | `adapter.rs`, `abstract_cfg.rs` | [Pearce2004] |
| GEP type-chain walking (Step 1) | `adapter.rs` | [LLVMRef] |
| Alias analysis (Step 4 prereq) | `alias_analysis.rs` (planned) | [Andersen1994], [Pearce2004] |
| Return summaries | `adapter.rs`, `driver.rs` | [Godefroid2007] |
| Interprocedural summary reuse | `driver.rs` | [Reps1995] |
| Observer invariant synthesis | `driver.rs` | [Godefroid2010] §5 |
| Purity analysis | `adapter.rs` | [Blanchet2003] |
| Counterexample extraction | `backward.rs` | [Clarke2003] |
| LLVM IR interface | `llvm_wrap.rs` | [Lattner2004] |
| Debug source locations | `llvm_wrap.rs` | [LLVMDebug] |
