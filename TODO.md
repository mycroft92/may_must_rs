# TODO

## Current Backlog

- wire the trait-based external summary generator seam behind a separate opt-in CLI switch
- add an opt-in LLM candidate-generation layer for loop invariants and function summaries on top of that external generator seam
- keep the default non-LLM route as the baseline/fallback for summary and invariant discovery
- add oracle-backed verification/adoption flow for LLM-proposed loop invariants and function summaries
- extend `SummaryProvider` provenance/state beyond discovered summaries so future imported or generated candidates can be verified and adopted cleanly
- add oracle-backed verification/adoption flow for discovered loop invariant candidates over the extracted loop regions
- extend the current Figure 5-10 rule driver beyond the acyclic visible-memory call-summary subset
- broaden rule-driver handling beyond the current `Assign` / `Assume` / branch subset to more lowered instructions
- improve rule-driver handling beyond the current integer-array memory and conservative impure-call havoc slice
- improve summary projection/elimination beyond the current syntactic hidden-assignment slice
- extend default rule-check witness replay beyond the current acyclic visible-memory query slice
- extend CLI checking beyond the current `--simple-check` / `--rule-check` split
- replace temporary `max_step` loop bounding with loop summaries / invariants
- extend LLVM adapter coverage beyond the current scalar/integer/integer-memory subset
- much later, add file-loaded trusted summaries for missing / external functions through the same trait/JSON seam
