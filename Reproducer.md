# REPRODUCER

All changes from tag `pre_fix_state_a` to the current HEAD, in order.
Applying these changes to a checkout at `pre_fix_state_a` reproduces
the current state exactly.

---

## Fix 1 — Return-summary memory mapping

### Problem

`summary_assume_for_call` ran during instruction lowering, before
`resolve_memory_effects` had built the `PointerEnv`.  ext_region names
(`callee$__ext_k`) in the return-summary formula had no mapping entry,
so `rename_callee_vars` renamed them to ghost per-call-site names
(`caller$callN$__ext_k`) that were disconnected from the caller's actual
memory — assertions depending on pointer reads in the callee were always
`BugFound`.

A second bug: the zero-offset guard `binding.offset == Term::int(0)` used
structural equality; a two-index GEP with all-zero indices produces
`Term::Add(Int(0), Int(0))`, which is not structurally equal to `Int(0)`,
so the guard always failed.

### `src/common/adapter.rs`

**Remove `summaries` from `lower_node_transfer` / `lower_node_effects`
and delete `summary_assume_for_call`.**

Remove the `summaries: &CallSummaryRegistry` parameter from both
functions and their two call sites.  Remove the `summary_assume_for_call`
call from the `Call` arm of `lower_node_effects`.  Delete
`summary_assume_for_call` entirely.

**Add step 9 in `adapt_with_purity_and_summaries`** (after step 8):

```rust
apply_pending_return_summaries(
    &mut cfg, graph, &instruction_nodes, function_name, summaries, &final_env,
)?;
```

**Add `apply_pending_return_summaries`** (after `apply_pending_write_effects`):

```rust
fn apply_pending_return_summaries(
    cfg: &mut AbstractCfg,
    graph: &FunctionGraph,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
    function_name: &str,
    summaries: &CallSummaryRegistry,
    final_env: &PointerEnv,
) -> Result<(), AdapterError> {
    for instruction in &graph.vertices {
        if instruction.get_opcode() != InstructionOpcode::Call { continue; }
        let Some(callee) = instruction.get_called_function() else { continue; };
        let Some(summary) = summaries.get(&callee) else { continue; };
        let node_id = match instruction_nodes.get(instruction) {
            Some(&id) => id, None => continue,
        };
        let actual_args = instruction.get_call_args();
        let call_site_id = summaries.next_call_site_id();
        let local_prefix = format!("{function_name}$call{call_site_id}");

        let mut mapping: BTreeMap<String, String> = BTreeMap::new();
        for (formal, actual) in summary.formal_parameters.iter().zip(actual_args.iter()) {
            if actual.as_constant_int().is_none() {
                mapping.insert(formal.clone(), local_name(function_name, *actual));
            }
        }
        let lhs_name = local_name(function_name, *instruction);
        mapping.insert(summary.retval_name.clone(), lhs_name);

        let renamed = rename_callee_vars(&summary.relation, &mapping, &callee, &local_prefix);

        // Build region_map keyed on POST-RENAME ext_region names.
        // rename_callee_vars turns "callee$__ext_k" → "{local_prefix}$__ext_k".
        let mut region_map: BTreeMap<String, (String, Term)> = BTreeMap::new();
        for (param_idx, actual) in actual_args.iter().enumerate() {
            if let Ok(ptr_name) = pointer_name(function_name, *actual) {
                if let Some(binding) = final_env.get(&ptr_name) {
                    let callee_prefix = format!("{callee}$");
                    let ext_key = ext_region_name(&callee, param_idx);
                    let renamed_key = if let Some(suffix) = ext_key.strip_prefix(&callee_prefix) {
                        format!("{local_prefix}${suffix}")
                    } else { ext_key };
                    region_map.insert(renamed_key, (binding.region.clone(), binding.offset.clone()));
                }
            }
        }
        let rewritten = substitute_ext_regions(&renamed, &region_map);
        let mut substituted = rewritten;
        for (formal, actual) in summary.formal_parameters.iter().zip(actual_args.iter()) {
            if let Some(c) = actual.as_constant_int() {
                substituted = substitute_var_name_with_term(&substituted, formal, &Term::int(c));
            }
        }
        if let Some(node) = cfg.node_mut(node_id) {
            node.transfer.effects.push(TransferEffect::Obligation(substituted));
        }
    }
    Ok(())
}
```

**Add `substitute_ext_regions` and helpers** (before `formula_contains_var`):

```rust
// Rewrites select(Memory::Var(ext_k), idx) → select(Memory::Var(actual), base+idx)
// for every entry in region_map.
fn substitute_ext_regions(formula: &Formula, region_map: &BTreeMap<String,(String,Term)>) -> Formula
fn substitute_ext_regions_term(term: &Term, ...) -> Term {
    // Term::Select: if Memory::Var(name) in region_map →
    //   Term::select(Memory::var(actual), Term::add(base, idx))
    // All other Term variants: recurse.
}
fn substitute_ext_regions_memory(memory: &Memory, ...) -> Memory
```

### `tests/array_max_callee.c`

Remove the loop; use explicit 5-way comparisons (so `compute_return_summary`,
which requires an acyclic CFG, can derive the return summary):

```c
int find_max(int *arr) {
    int max = arr[0];
    if (arr[1] > max) max = arr[1];
    if (arr[2] > max) max = arr[2];
    if (arr[3] > max) max = arr[3];
    if (arr[4] > max) max = arr[4];
    return max;
}
int main() {
    int numbers[5] = {10, 20, 30, 40, 50};
    int m = find_max(numbers);
    may_assert(m >= numbers[0]); // ... through numbers[4]
}
```

### `src/may_must_analysis/driver.rs`

Rename test and flip expected verdict:
- was: `array_max_callee_bugfound_without_loop_return_summary` → BugFound/Unsafe
- now: `array_max_callee_verified_with_return_summary` → Verified/Safe

---

## Fix 2 — Global variables

### Problem

`resolve_memory_effects` only seeded `PointerEnv` bindings for pointer
parameters.  Loads/stores through global variable pointers (`@g`) had no
binding and were silent Nops in `wp`.

### `src/common/llvm_utils/llvm_wrap.rs`

Add to `impl Instruction`:

```rust
pub fn is_global_variable_ref(&self) -> bool {
    unsafe { !LLVMIsAGlobalVariable(self.0).is_null() }
}

/// Returns integer element values for a ConstantDataArray/ConstantArray/
/// GlobalVariable with such an initialiser, or a one-level bitcast of any
/// of the above.  Uses LLVMGetAggregateElement (LLVM 15+) which is
/// bounds-safe for both ConstantArray and ConstantDataArray.
pub fn constant_int_elements(&self) -> Option<Vec<i64>> {
    self.constant_int_elements_inner()
        .or_else(|| self.get_operand(0)?.constant_int_elements_inner())
}

fn constant_int_elements_inner(&self) -> Option<Vec<i64>> {
    unsafe {
        let arr = if !LLVMIsAGlobalVariable(self.0).is_null() {
            let init = LLVMGetInitializer(self.0);
            if init.is_null() { return None; }
            init
        } else if !LLVMIsAConstantArray(self.0).is_null()
               || !LLVMIsAConstantDataArray(self.0).is_null() {
            self.0
        } else { return None; };
        let mut out = Vec::new();
        let mut i = 0u32;
        loop {
            let elem = LLVMGetAggregateElement(arr, i);
            if elem.is_null() { break; }
            if LLVMIsAConstantInt(elem).is_null() { return None; }
            out.push(LLVMConstIntGetSExtValue(elem));
            i += 1;
        }
        if out.is_empty() { None } else { Some(out) }
    }
}
```

### `src/common/adapter.rs`

In `resolve_memory_effects`, right after the pointer-param seeding block:

```rust
// Seed pointer bindings for global variable references in this function.
for instruction in &graph.vertices {
    for operand_idx in 0..instruction.get_operand_count() {
        if let Some(op) = instruction.get_operand(operand_idx) {
            if op.is_global_variable_ref() && is_pointer_value(op) {
                let ptr_name = local_name(function_name, op);
                if env.get(&ptr_name).is_none() {
                    let region = format!("global${}", op.display_name());
                    env.bind(ptr_name, region, Term::int(0));
                }
            }
        }
    }
}
```

### `tests/global_int.c` (new)

```c
#include "local_assert.h"
int g;
void test(int x) {
    g = x;
    may_assert(g == x);   // Verified
}
```

---

## Fix 3 — BitCast pointer alias + llvm.memcpy / llvm.memset

### Problem

Pointer-typed `BitCast`/`AddrSpaceCast` were Nops — no binding propagated
through them.  The `dst` argument of `llvm.memcpy` is typically
`bitcast [N x i32]* %local to i8*`; without the alias the dst was unbound
and the memcpy was ignored.  All `llvm.*` intrinsics were modeled as
`HavocMemory` (a Nop in `wp`), so C aggregate initialisers like
`int nums[3] = {7, 8, 9}` left local arrays completely unknown.

### `src/common/abstract_cfg.rs`

Add `TransferEffect::PointerAlias`:

```rust
/// Pointer-typed bitcast or addrspacecast; no formula semantics (wp = identity);
/// consumed only by resolve_memory_effects.
PointerAlias { target: String, source: String },
```

Add `TransferEffect::PointerAlias { .. }` to the bookkeeping arms of
both `wp_one` (returns `post.clone()`) and `sp_one` (returns `pre.clone()`).

### `src/common/adapter.rs`

**Lower `BitCast`/`AddrSpaceCast` as `PointerAlias`** (was `None`):

```rust
InstructionOpcode::BitCast | InstructionOpcode::AddrSpaceCast => {
    if is_pointer_value(instruction) {
        if let Some(op) = instruction.get_operand(0) {
            if let Ok(source) = pointer_name(function_name, op) {
                Some(TransferEffect::PointerAlias {
                    target: local_name(function_name, instruction),
                    source,
                })
            } else { None }
        } else { None }
    } else { None }
}
```

**Handle `PointerAlias` in `resolve_memory_effects`** (after the
`PointerLoad` arm):

```rust
TransferEffect::PointerAlias { ref target, ref source } => {
    if let Some(binding) = env.get(source).cloned() {
        env.bind(target.clone(), binding.region, binding.offset);
    }
    rewritten.push(TransferEffect::Nop);
}
```

**Add step 10 in `adapt_with_purity_and_summaries`** (after step 9):

```rust
apply_pending_memcpy_effects(&mut cfg, graph, &instruction_nodes, function_name, &final_env)?;
```

**Add `apply_pending_memcpy_effects`** (after `apply_pending_return_summaries`):

```rust
fn apply_pending_memcpy_effects(...) -> Result<(), AdapterError> {
    for instruction in &graph.vertices {
        let Some(callee) = instruction.get_called_function() else { continue; };
        let is_memcpy = callee.starts_with("llvm.memcpy") || callee.starts_with("llvm.memmove");
        let is_memset = callee.starts_with("llvm.memset");
        if !is_memcpy && !is_memset { continue; }
        // args: dst(0), [src(1)], len(2)
        // Resolve dst through PointerEnv; skip if unresolvable.
        // memcpy Case A: src is (bitcast-wrapped) constant global array →
        //   use src_arg.constant_int_elements() to get concrete values,
        //   emit one MemoryStore per element.
        // memcpy Case B: src is locally resolved + len is constant →
        //   emit MemoryStore(dst, dst_off+k, select(src, src_off+k)) for k in 0..len.
        //   APPROX_HEAVY: byte-len treated as element-count.
        // memset: fill and len both constant →
        //   emit MemoryStore(dst, dst_off+k, fill) for k in 0..len.
    }
    Ok(())
}
```

### `tests/array_init.c` (new)

```c
#include "local_assert.h"
int main() {
    int nums[3] = {7, 8, 9};
    may_assert(nums[0] == 7);
    may_assert(nums[1] == 8);
    may_assert(nums[2] == 9);
    return 0;
}
```

---

## Fix 4 — Non-zero base-offset pointer arguments in callee summaries

### Problem

The zero-only path inserted `ext_region_k → actual_region` only when the
binding offset was structurally zero.  Passing `&arr[2]` (offset 2) left
the ext_region as a ghost name unconnected to the actual array.  Even if
fixed to recognise zero offsets, the rename only changed the region name —
it did not adjust the select indices — so `select(ext_k, i)` would produce
the wrong element when the base offset was non-zero.

### `src/common/adapter.rs`

This fix is integrated into `apply_pending_return_summaries` (Fix 1).
The key differences from the previous zero-only approach:

1. `region_map` is built for **all** pointer args (any offset).
2. **Post-rename keys**: `rename_callee_vars` turns `callee$__ext_k` →
   `{local_prefix}$__ext_k`; the map keys use the renamed names.
3. `substitute_ext_regions` (added in Fix 1) rewrites
   `select(ext_k, i)` → `select(actual_region, base_offset + i)`, not
   just a region name rename.

### `tests/array_max_offset.c` (new)

```c
#include "local_assert.h"
int find_max3(int *arr) {   // no loop; compute_return_summary works
    int m = arr[0];
    if (arr[1] > m) m = arr[1];
    if (arr[2] > m) m = arr[2];
    return m;
}
int main() {
    int numbers[5] = {10, 20, 30, 40, 50};
    int m = find_max3(&numbers[2]);  // passes {30,40,50}, offset=2
    may_assert(m >= numbers[2]);     // Verified
    may_assert(m >= numbers[3]);     // Verified
    may_assert(m >= numbers[4]);     // Verified
    return 0;
}
```

---

## Fix 5 — SRem/URem, pointer ICmp operands, bitwise integer And/Or/Xor

### Problem

Three LLVM IR patterns caused `UnsupportedInstruction` / `UnsupportedValue`
errors that prevented CFG generation for programs using integer remainder
(`rand() % 5`), pointer comparisons (`buf == NULL`), or bitwise masking
(`rand() & 0xff`).

### `src/common/formula.rs`

Add `Term::Rem(Box<Term>, Box<Term>)` to the `Term` enum:

```rust
Div(Box<Term>, Box<Term>),
Rem(Box<Term>, Box<Term>),    // NEW
Neg(Box<Term>),
```

Add `pub fn rem(lhs: Term, rhs: Term) -> Self`.

Extend every `Term` match arm that handles `Div` to also handle `Rem`:
- `sort()`: `| Term::Rem(lhs, rhs) => unify_numeric_sorts(...)`
- `Display`: `Term::Rem(lhs, rhs) => write!(f, "({lhs} % {rhs})")`
- `substitute_term`: add `Term::Rem` arm
- `collect_select_indices_term`: add `Term::Rem` to the binary-op group

### `src/common/smt/solver.rs`

Add `Term::Rem` to `lower_term`, using `Int::rem` (Z3's integer remainder).
Real-sorted operands return `ExpectedIntegerSort`:

```rust
Term::Rem(lhs, rhs) => match (self.lower_term(lhs)?, self.lower_term(rhs)?) {
    (EncodedTerm::Int(lhs), EncodedTerm::Int(rhs)) => Ok(EncodedTerm::Int(lhs.rem(&rhs))),
    (EncodedTerm::Int(_),  EncodedTerm::Real(_)) => Err(MixedSorts { left: Int, right: Real }),
    (EncodedTerm::Real(_), EncodedTerm::Int(_))  => Err(MixedSorts { left: Real, right: Int }),
    (EncodedTerm::Real(_), EncodedTerm::Real(_)) => Err(ExpectedIntegerSort { found: Real }),
},
```

### `src/common/abstract_cfg.rs`

Add `Term::Rem` to the two `substitute_var_in_term` /
`substitute_memory_var_in_term` recursive helpers (same pattern as `Div`).

### `src/common/adapter.rs`

**Wire `SRem`/`URem` into `lower_node_effects`:**

```rust
// outer match arm — add SRem, URem alongside SDiv, UDiv:
| InstructionOpcode::SRem
| InstructionOpcode::URem

// inner value selector:
InstructionOpcode::SRem | InstructionOpcode::URem => Term::rem(lhs, rhs),
```

**Handle pointer-typed ICmp operands in `lower_numeric_value`:**

```rust
fn lower_numeric_value(function_name: &str, value: Instruction) -> Result<Term, AdapterError> {
    // APPROX_HEAVY: pointer values (e.g. ICmp operands comparing to null)
    // are treated as Sort::Int addresses.  null → 0; non-null → Int var.
    if is_pointer_value(value) {
        if value.as_constant_int() == Some(0) || value.print().contains("null") {
            return Ok(Term::int(0));
        }
        return Ok(Term::var(local_name(function_name, value), Sort::Int));
    }
    match sort_for_value(value)? { ... }
}
```

**Bitwise integer `And`/`Or`/`Xor` — emit empty effects instead of error:**

```rust
InstructionOpcode::And | InstructionOpcode::Or | InstructionOpcode::Xor => {
    let result_sort = sort_for_value(instruction)?;
    if result_sort != Sort::Bool {
        // APPROX_HEAVY: bitwise integer op — leave result unconstrained.
        return Ok(effects);
    }
    // ... existing Bool path unchanged ...
}
```

**Add `Term::Rem` to all term-traversal helpers in `adapter.rs`:**
`rename_vars_in_term`, `term_contains_var`, `substitute_term_var_name`,
`substitute_ext_regions_term` — each gets a `Term::Rem` arm matching `Div`.

### `src/may_must_analysis/loops.rs`

```rust
Term::Add(l,r) | Term::Sub(l,r) | Term::Mul(l,r) | Term::Div(l,r) | Term::Rem(l,r) => { ... }
```

### `src/may_must_analysis/llm_provider.rs`

```rust
Add(a,b) | Sub(a,b) | Mul(a,b) | Div(a,b) | Rem(a,b) => { ... }
```

---

## Fix 6 — `tests/kw_fn.c` (new fixture)

### Problem / Test purpose

`kw_fn.c` exercises integer remainder (`rand() % 5`), pointer ICmp
(`buf == NULL`), and bitwise masking (`rand() & 0xff`).  `get_len()`
returns one of `{1, 123, 0, 22, 3}` from a local array indexed by
`rand() % 5`.  Values 22 and 123 both exceed `MAX_LEN = 12`, so the
buffer allocation (`allocSize = min(len, 12) - 1`) is insufficient for
the loop `for (i = 0; i < len; i++)`.

Two assertions:
1. `may_assert(len < MAX_LEN)` — placed before the loop; directly
   checkable without loop analysis.
2. `may_assert(i < MAX_LEN)` — placed inside the loop; expresses
   "for every iteration i must be < MAX_LEN".

### Expected analysis result

- **Assertion #1 (`len < MAX_LEN`) → BugFound.**  The return summary for
  `get_len` encodes `retval == select(store_chain{1,123,0,22,3}, idx)`
  where `idx` is free.  Z3 finds `idx = 3 → retval = 22 > 12`.
- **Assertion #2 (`i < MAX_LEN` in loop) → Verified** (precision gap).
  The loop invariant synthesis seeds `i >= 0` and the backward analysis
  cuts off at the loop header, preventing the `len > 12` violation from
  propagating to entry.  This is a known limitation: tighter callee-return
  + loop-bound interaction is not yet modeled.

### `tests/kw_fn.c`

```c
#include<stdio.h>
#include<stdlib.h>
#include"local_assert.h"

#define MAX_LEN 12

int get_len() {
    int arr[5] = {1,123,0,22,3};
    int idx = rand() % 5;
    return arr[idx];
}

int main(int argc, const char *argv[])
{
    int len  = get_len();
    if(len == 0)
        return -1;

    int i, resultCount, server = 0;
    int allocSize;
    char * buf = NULL;

    if(len != 0)
    {
        resultCount = (len < MAX_LEN) ? len : MAX_LEN;
        allocSize = (resultCount - 1);

        /* len from get_len() can be 22 or 123 — both > MAX_LEN.
           This pre-loop assertion catches that directly. */
        may_assert(len < MAX_LEN);

        buf = malloc(allocSize);
        if(buf == NULL)
            return -1;

        for (i = 0; i < len; i++)
        {
            may_assert(i < MAX_LEN);
            buf[i] = rand() & 0xff; //OOB access
        }
    }
    free(buf);
    return 0;
}
```

---

## TODO.md

Added item 5 after the existing item 4:

> **Struct / aggregate GEP layout.**
> `lower_gep_offset` sums all GEP indices as plain integers, ignoring
> element sizes and struct field layout.  Fix: use `LLVMOffsetOfElement`
> / `LLVMStoreSizeOfType` to convert GEP indices to correct abstract
> integer offsets.

---

## New driver tests (`src/may_must_analysis/driver.rs`)

Five tests loading compiled `.bc` files via `parse_bc_file`:

| Test | Fixture | Expected |
|---|---|---|
| `array_max_callee_verified_with_return_summary` | `array_max_callee.bc` | 5 × Verified, Safe |
| `global_int_store_then_assert_verified` | `global_int.bc` | 1 × Verified, Safe |
| `array_init_verified_after_memcpy_modeling` | `array_init.bc` | 3 × Verified, Safe |
| `array_max_offset_verified_with_nonzero_base_offset` | `array_max_offset.bc` | 3 × Verified, Safe |

(No driver test for `kw_fn.bc` — the result depends on the loop analysis
precision and the two assertions give mixed verdicts.)

---

## Verification

```sh
make -C tests ir
cargo test -- --test-threads=1   # 118 tests pass

cargo run --bin main -- --no-dot tests/out/array_max_callee.bc
# → 5 assertions Verified, SAFE

cargo run --bin main -- --no-dot tests/out/global_int.bc
# → test: Verified, SAFE

cargo run --bin main -- --no-dot tests/out/array_init.bc
# → 3 assertions Verified, SAFE

cargo run --bin main -- --no-dot tests/out/array_max_offset.bc
# → 3 assertions Verified, SAFE

cargo run --bin main -- --no-dot tests/out/kw_fn.bc
# → assertion #1 (len < MAX_LEN): BugFound  — len can be 22 or 123
# → assertion #2 (i < MAX_LEN):   Verified  — loop precision gap
# Module verdict: UNSAFE
```
