# Frontend — LLVM IR to FunctionGraph

Parses LLVM bitcode into a graph of raw instructions. No analysis logic here.

## llvm_wrap.rs

Thin safe wrappers around the LLVM C API:
- `Context` / `Module` — bitcode loading and ownership
- `Function`, `BasicBlock`, `Instruction` — IR traversal
- `InstructionOpcode` — opcode enumeration
- `TypeKind` — type classification (integer, pointer, struct, array, …)
- `TargetData` — struct layout and element-size queries (used by `adapter.rs`)
- `initialize_target()` — required before any TargetData query

## program_graph.rs

Builds one `FunctionGraph` per defined LLVM function:
- Strips `may_assert` calls → `AssertSite` records
- Strips `may_assume` calls → `AssumeSite` records (with `is_type_bound` flag)
- Strips `reach_error` / `__assert_fail` / `__VERIFIER_error` → unconditional
  `AssertSite { is_unconditional_fail: true }`
- Builds vertex list (remaining visible instructions)
- Records successor / predecessor edges
- Attaches LLVM debug metadata (`SourceLocation`) to each site

## assertions/

Expression parser and translator for the `may_assert(expr)` argument language:
- `exp.rs` — AST types (`Assertion`, `Expr`, `Op`, `Statement`)
- `translation.rs` — lowers `Assertion` to a `Formula`
