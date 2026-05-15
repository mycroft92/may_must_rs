# TODO

## Current Backlog

- add real-valued lowering so fixtures like `tests/flow/float_compare.c` are
  analyzed instead of reported as unsupported
- strengthen cyclic procedure handling:
  return summaries for looping callees, tighter invariant checking, and better
  accepted-candidate quality
- decide whether the driver should gain best-effort module analysis internally
  instead of relying on the CLI fallback path
- wire real LLVM debug/source locations into `llvm_wrap.rs` and `adapter.rs` so
  assertion reports point to source coordinates instead of relative instruction
  descriptions
- struct / aggregate GEP layout:
  `lower_gep_offset` sums all GEP indices as plain integers, ignoring
  element sizes and struct field layout. Fix: use `LLVMOffsetOfElement` /
  `LLVMStoreSizeOfType` to convert GEP indices to correct abstract integer
  offsets
- broaden cast/instruction coverage beyond the current integer/boolean subset
- decide whether `assertions::translation` should become a CLI input path or
  remain a library-only component
- keep the loop-invariant provider / LLM path aligned with the active checker
- tighten and document the current call-summary contract, especially what kinds
  of return relations are inferred and reused soundly
