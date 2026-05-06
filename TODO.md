# TODO

## Current Backlog

- add an opt-in LLM candidate-generation layer for loop invariants and function summaries behind a separate CLI switch
- keep the default non-LLM route as the baseline/fallback for summary and invariant discovery
- add oracle-backed verification/adoption flow for LLM-proposed loop invariants and function summaries
- extend the current local Figure 5/6/7 rule driver beyond the acyclic scalar-plus-memory subset
- broaden rule-driver handling beyond the current `Assign` / `Assume` / branch subset to more lowered instructions
- improve rule-driver handling beyond the current integer-array memory and conservative impure-call havoc slice
- extend default rule-check witness replay beyond the current local scalar query slice
- extend CLI checking beyond the current `--simple-check` / `--rule-check` split
- replace temporary `max_step` loop bounding with loop summaries / invariants
- extend LLVM adapter coverage beyond the current scalar/integer/integer-memory subset
- connect actual call lowering to the implemented summary-rule interfaces
- much later, add file-loaded trusted summaries for missing / external functions
