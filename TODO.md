# TODO

## Current Backlog

- add real-valued lowering so fixtures like `tests/flow/float_compare.c` are
  analyzed instead of reported as unsupported
- implement loop handling beyond structural preservation:
  loop invariants, loop summaries, or another sound cyclic-CFG strategy
- decide whether the driver should gain best-effort module analysis internally
  instead of relying on the CLI fallback path
- wire real LLVM debug/source locations into `llvm_wrap.rs` and `adapter.rs` so
  assertion reports point to source coordinates instead of relative instruction
  descriptions
- broaden cast/instruction coverage beyond the current integer/boolean subset
- decide whether `assertions::translation` should become a CLI input path or
  remain a library-only component
- either wire `providers.rs` loop-invariant candidates into the analysis or
  remove the stub until loop work resumes
- tighten and document the current call-summary contract, especially what kinds
  of return relations are inferred and reused soundly
