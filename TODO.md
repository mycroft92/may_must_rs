# TODO

## Current Backlog

- change the external loop-summary design: after lowering detects loops, send the loop body/instructions through an external interface, parse the returned summary, and attach it to the current procedure instead of sourcing loop summaries from the CLI layer
- add an opt-in LLM candidate-generation layer for loop invariants and function summaries on top of the existing external-summary CLI seam
- keep the default non-LLM route as the baseline/fallback for summary and invariant discovery
- add oracle-backed verification/adoption flow for LLM-proposed loop invariants and function summaries
- extend `SummaryProvider` provenance/state beyond discovered summaries so future imported or generated candidates can be verified and adopted cleanly
- add oracle-backed verification/adoption flow for discovered loop invariant candidates over the extracted loop regions
- extend the current Figure 5-10 rule driver beyond the acyclic visible-memory call-summary subset
- broaden rule-driver handling beyond the current `Assign` / `Assume` / branch subset to more lowered instructions
- improve rule-driver handling beyond the current integer-array memory and conservative impure-call havoc slice
- improve summary projection/elimination beyond the current syntactic hidden-assignment slice
- extend default rule-check witness replay beyond the current acyclic visible-memory query slice
- remove the remaining legacy bounded-explorer code from `driver.rs` now that the CLI is rule-check only
- replace temporary `max_step` loop bounding with loop summaries / invariants
- extend LLVM adapter coverage beyond the current scalar/integer/integer-memory subset
- much later, add file-loaded trusted summaries for missing / external functions through the same trait/JSON seam
