# Design Note: LLM-Guided Verification with Tiered Trust

## Status: EXPLORATORY — seams exist, full loop not yet wired

## What Already Exists

The codebase already has most of the plumbing:

- `src/may_must_analysis/providers.rs` — `CandidateProvider` trait: the seam
  for injecting external loop invariant candidates into the synthesis loop
- `src/may_must_analysis/llm_provider.rs` — `LlmCandidateProvider` implements
  the trait; `CegisAttempt` tracks candidate + failure reason; `FullLoopContext`
  carries all the context needed to prompt an LLM; `SubprocessLlmBackend` calls
  an external script
- `src/may_must_analysis/llm_response_parser.rs` — `parse_invariant` parses
  LLM-generated formulas from C-like boolean expressions into internal `Formula`
  values; handles `forall`/`exists` quantifier syntax
- The CEGIS feedback loop structure is present: if an LLM-proposed invariant
  fails any of the three checks (initiation, inductiveness, exit closure), the
  failure is recorded in `CegisAttempt` and the LLM can be called again with
  the failure reason included in the prompt

**What is missing**: the LLM does not yet generate function summaries (only
loop invariants), there is no trust-level distinction on verdicts, and the
prompt engineering for reliable invariant output is unresolved.

## The Core Problem: Getting Clean LLM Output

Loop invariants are hard for LLMs to get right on the first try because:
- The formula must be over the exact internal variable names (e.g. `main$i`,
  not `i`) — the LLM needs to be told these
- The invariant must be inductive, not just true at a single point
- LLMs tend to produce prose annotations or Python-style conditions rather
  than the parser-ready format `parse_invariant` expects
- When a candidate fails, the failure reason (e.g. "inductiveness check failed:
  counterexample has i=5, n=3") needs to be communicated back clearly enough
  for the LLM to refine rather than guess again

Function summaries have the same problem plus an additional one: the summary
must be expressed in terms of the callee's formal parameter names and return
variable (`fn$__retval`), which the LLM has no natural way of knowing.

## Practical Recommendation: Function Summaries for UNKNOWN Functions

The highest-leverage immediate extension: when the static tool produces UNKNOWN
for a function F due to unsupported instructions or unresolvable heap access,
call the LLM to generate a candidate postcondition (return summary) for F.
The static tool then:

1. Attempts to verify the candidate by running backward WP analysis on F
   with the candidate as the assertion goal.
2. If verification passes: promote the summary to a **trusted lemma** and
   re-analyze all callers of F with the summary injected.
3. If verification fails: send the failure + counterexample back to the LLM
   (CEGIS round), up to a configurable max.
4. If still unverified after max rounds: record the summary as a
   **low-trust assumption** — used in analysis but flagged in the verdict.

This fits directly into the existing `ReturnSummary` + `SummaryTables`
infrastructure. The only new wiring needed is:
- Trigger the LLM call when a function produces UNKNOWN in the driver
- Pass the summary back through `apply_pending_return_summaries` as if it
  were a normally-inferred summary (but tagged with its trust level)
- Propagate trust level through to the final verdict

## The Trust Model

Three levels, tracked per lemma and per final verdict:

| Level | Name | Meaning |
|---|---|---|
| 0 | **Verified** | Fully proved by static tool; no LLM involvement |
| 1 | **LLM-verified** | LLM proposed; static tool confirmed all three checks |
| 2 | **LLM-assumed** | LLM proposed; static tool could not fully verify (e.g. unsupported instruction blocked the check); taken as sound assumption, clearly flagged |

Final verdict annotation:
- `SAFE (verified)` — only level-0 and level-1 lemmas used
- `SAFE (conditional: N assumed lemmas)` — some level-2 lemmas in the chain
- `UNSAFE (verified)` — concrete counterexample found, no unverified lemmas
- `UNSAFE (candidate: N assumed lemmas)` — counterexample depends on level-2 claims

The distinction matters: a `SAFE (verified)` result is a real proof.
A `SAFE (conditional)` result is a useful hint that may still be wrong.

## Prompt Engineering Strategy

The LLM needs to produce output in the exact format `parse_invariant` accepts.
The key constraints to communicate:

**For loop invariants** — give the LLM:
- The loop body in readable C (not LLVM IR)
- The exact variable names the formula must use (from `variable_sorts`)
- The assertion being proved (from `exit_postcondition`)
- The previous failed candidates with failure reasons (from `previous_attempts`)
- A concrete format example: `x >= 0 && x <= n && sum == x*(x+1)/2`
- A grammar snippet: operators are `+`, `-`, `*`, `/`, `%`, `==`, `!=`,
  `<`, `<=`, `>`, `>=`, `&&`, `||`, `!`; no function calls

**For function summaries** — give the LLM:
- The function source (readable C)
- The formal parameter names and their types
- The return variable name (`fn$__retval`)
- What the caller needs to know: "produce a formula over the parameters and
  return value that captures what this function guarantees"
- The failure reason if a previous candidate was rejected

**Structured output**: ask the LLM to respond with a tagged block:
```
<invariant>
x >= 0 && x <= n && sum == x*(x+1)/2
</invariant>
```
or
```
<summary>
fn$__retval >= 0 && fn$__retval <= fn$x
</summary>
```

This makes extraction reliable and avoids parsing prose. `llm_response_parser.rs`
already has the `parse_invariant` entry point; the extraction of the tagged
block is a trivial pre-processing step.

## The Bubble Sort Case as a Test

`bubble_sort-2` is a good target for this approach:

1. `fail()` → postcondition is `False` (trivially verifiable by static tool;
   level-0 lemma)
2. `inspect()` → LLM can see that `fail()` is called when `head->next == head`;
   candidate summary: "if called with an empty list, the function diverges
   (postcondition False)"; static tool tries to verify — blocked by `ptrtoint`
   → level-2 (assumed)
3. `gl_read()` → LLM: "if nondet returns 0 immediately, no insertions occur";
   static tool: loop exit condition is checkable → level-1 (LLM-verified)
4. Compose: gl_read() with zero iterations + inspect() called on empty list
   + inspect() → False = UNSAFE (candidate: 1 assumed lemma)

The `ptrtoint` instruction is the remaining blocker for a fully verified result.
Once that is handled (see TODO.md — instruction coverage), the level-2 lemma
for `inspect()` can potentially be promoted to level-1.

## Files to Touch When Implementing

- `src/may_must_analysis/providers.rs` — extend `CandidateProvider` to also
  cover function summaries, not just loop invariants
- `src/may_must_analysis/llm_provider.rs` — add `propose_function_summary`
  method; add trust-level field to proposed results
- `src/may_must_analysis/driver.rs` — trigger LLM call when function produces
  UNKNOWN; inject returned summary with trust tag; propagate trust to verdict
- `src/may_must_analysis/summaries.rs` — add `trust_level: TrustLevel` field
  to `ReturnSummary`
- Output layer (`src/main.rs`) — render trust level in verdict string

## Open Questions

- **Prompt caching**: can we cache LLM responses keyed on function content
  hash, so the same function isn't re-queried across runs?
- **Grammar-constrained generation**: if the LLM backend supports it,
  constrain generation to the `parse_invariant` grammar to eliminate parse
  failures entirely (llama.cpp / Outlines support this)
- **How many CEGIS rounds before giving up?** 3 rounds seems reasonable as
  a default — beyond that the LLM is unlikely to converge.
- **Can the LLM propose multiple candidates in one call?** Batching candidates
  reduces round-trips: ask for 3 invariant candidates ranked by confidence,
  check all three, feed back the failures together.

## Literature

- Clover (2023) — LLM + Dafny verifier feedback loop; closest to this design
  (search: "Clover LLM Dafny verification")
- Lemur (2024) — LLM-guided invariant generation with verifier in the loop
  (search: "Lemur LLM invariant generation verification")
- CEGIS + LLM — several 2023-2024 papers on using LLMs as the synthesis
  oracle in counterexample-guided synthesis loops
- "Finding Inductive Invariants using Large Language Models" — direct match
  (search that title)
