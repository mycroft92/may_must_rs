# Reading List

Papers chosen for implementation clarity over historical priority.
Ordered within each section from most concrete to most foundational.

---

## Incorrectness Logic

**O'Hearn, "Incorrectness Logic", POPL 2020**
The original paper. Short and readable. Section 2 gives the proof rules directly;
Section 4 connects it to under-approximate reasoning. Start here to understand
the `[P] C [Q]_err` judgement and why it differs from Hoare logic.
Search: `"Incorrectness Logic" O'Hearn POPL 2020`

**Raad, Brochenin, Toumi, Dreyer, Villard, O'Hearn,
"Local Reasoning About the Presence of Bugs: Incorrectness Separation Logic",
CAV 2020**
Extends incorrectness logic with separation logic heap ownership. This is the
theory behind Pulse. The combination of `*` (separating conjunction) and the
incorrectness triple is what makes use-after-free reasoning possible.
Section 3 gives the ISL proof rules; Section 4 shows the frame rule for bugs.
Search: `"Incorrectness Separation Logic" CAV 2020`

**Le, Raad, Villard, Berdine, Dreyer, O'Hearn,
"Finding Real Bugs in Big Programs with Incorrectness Logic",
OOPSLA 2022**
Engineering paper: how ISL was implemented in Pulse (Infer). Details the
bi-abduction + ISL combination that makes it scale. Most directly useful for
understanding what a production implementation looks like at scale.
Search: `"Finding Real Bugs Big Programs Incorrectness Logic" OOPSLA 2022`

---

## Separation Logic

**Reynolds, "Separation Logic: A Logic for Shared Mutable Data Structures",
LICS 2002**
The foundational paper. Section 2 gives the core connectives (`*`, `-*`,
`↦`). Section 3 gives the frame rule. Dense but precise — read alongside
a tutorial.
Search: `Reynolds "Separation Logic" LICS 2002`

**O'Hearn, Reynolds, Yang, "Local Reasoning About Programs that Alter Data
Structures", CSL 2001**
The paper that introduced the frame rule and the key insight: local reasoning
means you only need to describe what a function actually touches. More
accessible than Reynolds 2002 for understanding *why* separation logic matters.
Search: `O'Hearn Reynolds Yang "Local Reasoning" CSL 2001`

**Calcagno, Distefano, O'Hearn, Yang,
"Compositional Shape Analysis by means of Bi-Abduction", POPL 2009**
The algorithm that makes Infer scale interprocedurally. Bi-abduction
automatically infers both the precondition (what the function needs from the
heap) and the frame (what it leaves untouched). Section 3 gives the algorithm;
Section 5 gives the soundness argument. Key for understanding how to handle
unknown callee footprints without havocing all memory.
Search: `"Bi-Abduction Compositional Shape Analysis" POPL 2009`

**Berdine, Calcagno, O'Hearn,
"Smallfoot: Modular Automatic Assertion Checking with Separation Logic",
FMCO 2005**
The first practical automatic verifier for separation logic. Shows concretely
how symbolic heaps (list of points-to pairs + pure constraints) are
represented and how entailment is checked. Good reference for the data
structures an implementation needs.
Search: `"Smallfoot Modular Automatic Assertion" Berdine Calcagno FMCO 2005`

---

## LLM + Verification Loop

**Charalambous et al., "A New Era in Software Security: Towards Self-Healing
Software via Large Language Models and Formal Verification", arXiv 2023**
Concrete pipeline: LLM generates repair + invariant candidates, formal tool
verifies them. Implementation details on the feedback format between LLM and
verifier. Closest to what we want to build.
Search: `"Self-Healing Software Large Language Models Formal Verification" 2023`

**Chakraborty and Lahiri, "Ranking LLM-Generated Loop Invariants for
Program Verification", FMCAD 2023**
Directly relevant: how to prompt an LLM for loop invariants, how to rank
candidates, and how the CEGIS feedback loop works in practice. Includes
empirical results on what prompt formats work.
Search: `"Ranking LLM Generated Loop Invariants" FMCAD 2023`

**Kamath et al., "Finding Inductive Invariants using Large Language Models",
arXiv 2023**
LLM as the synthesis oracle in a CEGIS loop for inductive invariants.
Concrete prompt templates in the appendix. Shows the feedback message format
that makes LLMs refine invariants effectively (counterexample + which check
failed).
Search: `"Finding Inductive Invariants Large Language Models" 2023`

---

## Background: CBMC Memory Safety Encoding

**Clarke, Kroening, Lerda,
"A Tool for Checking ANSI-C Programs", TACAS 2004**
Describes how CBMC instruments programs with overflow checks, null checks,
and array bounds checks before model checking. Section 3 explains the
encoding. Most directly relevant to the instrumentation idea: how to convert
bug patterns into `assert(false)` reachability targets automatically.
Search: `"CBMC Tool Checking ANSI-C" TACAS 2004`
