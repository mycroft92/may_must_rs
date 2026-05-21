# Pointer Analysis

Field-sensitive, flow-insensitive Andersen-style alias analysis.

## andersen.rs

Runs once per LLVM module (called by `driver.rs` before the adapter loop).
Produces an `AliasResult` — a points-to map from each pointer SSA name to a
set of abstract locations (regions with field subscripts).

Abstract location naming:
- Stack alloca: `fn$stackN` (N = alloca index within the function)
- Pointer parameter: `fn$__ext_N` (N = parameter index)
- Global variable: `global$<name>`
- Struct field subscript: `region.field_N` (appended per GEP index)

`may_alias_regions(r1, r2)` returns true if any pointer can reach both regions
— used by `adapter.rs` to decide whether two `PointerStore`/`PointerLoad`
effects alias and must be resolved conservatively.

## pointer_env.rs

`PointerEnv` — a `HashMap<String, PointerBinding>` mapping each pointer SSA
name to its resolved `(region, offset)` pair. Built incrementally during
Phase 2 of the adapter (`resolve_memory_effects`) in topological order.

`PointerBinding` carries:
- `region: String` — the memory array name
- `offset: Term` — the base offset (integer term, typically 0 or a GEP sum)
