# Alias Analysis

This document describes the alias analysis pass implemented in
`src/common/alias_analysis.rs`.  Alias analysis is the prerequisite for the
heap memory model (Step 4): without it, every store through an unresolved
pointer must conservatively havoc *all* heap regions, making the solver unable
to maintain any fact about heap-allocated data across an unknown write.

---

## Motivation

`resolve_memory_effects` in `adapter.rs` builds a `PointerEnv` by tracking
pointer provenance through `alloca`, `GEP`, `bitcast`, and pointer parameter
seeding.  When a pointer operation's target cannot be resolved from the local
`PointerEnv` (e.g. a pointer loaded from a heap cell, or a store through a
pointer received as an argument to an inlined helper), the effect was
previously left as a raw `Store`/`PointerLoad` — invisible to the WP engine.
For heap objects this means:

- every `malloc` result stored into a slot and later loaded becomes an
  unresolved load target, losing all information about the written value; and
- the only sound fallback is to treat the pointer as having unknown provenance,
  producing `UNKNOWN` for any downstream assertion.

Alias analysis computes a **points-to map** — for each SSA pointer name, the
set of abstract memory regions it may point to — which lets `resolve_memory_effects`
use AA as a fallback to resolve the region when the local env does not have
enough information.

---

## Algorithm Choice

### Candidates considered

| Algorithm | Complexity | Precision | Notes |
|-----------|-----------|-----------|-------|
| Steensgaard (1996) | O(n α(n)) | Low | Unification conflates unrelated pointers; loses struct-field separation |
| Andersen (1994) | O(n³) | Medium-high | Inclusion constraints; field-sensitive extension well-understood |
| Flow-sensitive Andersen | O(n⁴) | High | Nested fixpoint over CFG; overkill on SSA form |
| LLVM built-in BasicAA | — | Medium | Syntactic; no heap reasoning |

### Selected: field-sensitive Andersen on LLVM SSA, flow-insensitive

**Justification:**

1. **SSA gives near-linear def-use structure.**  Each pointer SSA name has
   exactly one definition, so the constraint graph is nearly linear in the IR
   size and the O(n³) bound is rarely approached in practice.

2. **Field sensitivity is already in place.**  Step 2 introduced per-field
   region names (`fn$stack0$f1`, `heap$call42$f1`).  The AA constraint for
   `StructFieldGep` propagates the field subscript:
   `pts(target) ⊇ { r$fN | r ∈ pts(base) }`.
   This keeps fields of different structs — and different fields of the same
   struct — in separate abstract locations automatically.

3. **Flow insensitivity is sound and sufficient.**  SSA encodes most
   per-definition flow sensitivity at the value level.  A flow-insensitive
   analysis is a sound over-approximation and avoids a nested fixpoint over
   the same CFG the main may/must analysis already traverses.

4. **Steensgaard is too imprecise.**  Unification would merge `heap$call42`
   and `heap$call87` if a single pointer is ever assigned from both call sites
   (e.g. `p = cond ? malloc() : malloc()`), collapsing two independent heap
   regions into one and destroying precision on all subsequent field accesses.

**References:** Andersen (1994) §2; Hind (2001) Table 1; Pearce et al. (2004)
for field sensitivity; Hardekopf & Lin (2007) for the O(n³) constant-factor
optimisation via wave propagation.

---

## Abstract Locations

Abstract locations mirror the existing region-naming convention:

| Source | Abstract location name |
|--------|----------------------|
| `alloca T` (instruction K) | `fn$stackK` |
| struct field N of stack alloca K | `fn$stackK$fN` |
| pointer parameter index I | `fn$__ext_I` |
| struct field N of ext_I | `fn$__ext_I$fN` |
| global variable `@g` | `global$<g>` |
| `malloc`/`new` call site C | `heap$callC` |
| struct field N of heap call C | `heap$callC$fN` |

The field subscripts `$fN` are produced on demand as the constraint solver
follows `StructFieldGep` edges; no pre-enumeration of all struct fields is
needed.

---

## Constraint Rules

Notation: `pts(x)` = points-to set of SSA pointer `x`;
`pts_mem(r)` = set of abstract locations ever stored *as pointer values* into
region `r` (needed to resolve pointer loads through heap cells).

```
alloca T  (region name rK already assigned by adapter)
    pts(%alloca_result) ⊇ { rK }

getelementptr — StructFieldGep pattern (SrcTy=Struct, indices=[0,N])
    pts(%target) ⊇ { r$fN  |  r ∈ pts(%base) }

getelementptr — plain offset GEP
    pts(%target) ⊇ pts(%base)          -- same region, offset tracked separately

load ptr, %slot                        -- PointerLoad: loads a pointer value
    pts(%target) ⊇ ⋃ { pts_mem(r) | r ∈ pts(%slot) }

store ptr %v, %slot                    -- PointerStore: stores a pointer value
    pts_mem(r) ⊇ pts(%v)   for each r ∈ pts(%slot)

%t = call @malloc(...)  (call site id C)
    pts(%t) ⊇ { heap$callC }

%t = call @callee(%a0, %a1, ...)  (non-malloc, returns pointer)
    pts(%t) ⊇ AA_return_summary(callee)
    pts(callee$__ext_I) ⊇ pts(%aI)    for each pointer arg aI

bitcast / addrspacecast / PointerAlias
    pts(%target) ⊇ pts(%source)

phi ptr [%a, bb1], [%b, bb2]
    pts(%target) ⊇ pts(%a) ∪ pts(%b)

pointer parameter %p at index I
    pts(%p) ⊇ { fn$__ext_I }

global @g
    pts(@g) ⊇ { global$<g> }
```

### Heap struct field regions

When a `malloc` result is immediately cast to a struct pointer type and a
`StructFieldGep` follows, the field-sensitive constraint propagates the
`$fN` subscript through the heap region:

```
%raw  = call i8* @malloc(sizeof(Foo))     → pts(%raw)  = { heap$callC }
%p    = bitcast i8* %raw to Foo*          → pts(%p)   ⊇ pts(%raw) = { heap$callC }
%fp0  = gep Foo* %p, 0, 0                 → pts(%fp0) ⊇ { heap$callC$f0 }
%fp1  = gep Foo* %p, 0, 1                 → pts(%fp1) ⊇ { heap$callC$f1 }
store i32 42, i32* %fp0  →  MemoryStore { region: heap$callC$f0, offset: 0, value: 42 }
store i32  7, i32* %fp1  →  MemoryStore { region: heap$callC$f1, offset: 0, value:  7 }
```

No special-casing is needed: the existing `StructFieldGep` machinery applies
to heap pointers exactly as to stack allocas.

---

## Implementation

### Data structures (`src/common/alias_analysis.rs`)

```rust
/// An abstract memory location, identified by its region name.
#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct AbstractLoc(pub String);

impl AbstractLoc {
    /// Returns the abstract location for struct field `field` of this location.
    pub fn field(&self, field: u32) -> Self;
}

pub struct AliasResult {
    /// Points-to sets for every SSA pointer name seen in the IR.
    pts: HashMap<String, BTreeSet<AbstractLoc>>,
    /// For each abstract region name, the set of abstract locations
    /// ever stored into it as pointer values (needed to resolve PointerLoad).
    pts_mem: HashMap<String, BTreeSet<AbstractLoc>>,
}

impl AliasResult {
    /// May two abstract region names alias (i.e. be pointed to by the same pointer)?
    pub fn may_alias_regions(&self, r1: &str, r2: &str) -> bool;

    /// The set of abstract locations that SSA pointer `ptr` may point to.
    pub fn points_to(&self, ptr: &str) -> &BTreeSet<AbstractLoc>;

    /// The set of abstract locations ever stored into `region` as pointer values.
    pub fn stored_into(&self, region: &str) -> &BTreeSet<AbstractLoc>;

    /// Iterator over region names in `pts(ptr)`.
    pub fn pointed_regions(&self, ptr: &str) -> impl Iterator<Item = &str>;
}

/// Run the whole-module alias analysis and return an AliasResult.
pub fn run_alias_analysis(graphs: &[FunctionGraph]) -> AliasResult;
```

### Worklist algorithm

```
Input:  constraint set C generated from one module's FunctionGraphs
Output: AliasResult

Seed pts(p) with singleton sets for:
    alloca → { stackK }, malloc → { heap$callC },
    ext_param → { fn$__ext_I }, global → { global$g }

worklist ← all constrained SSA pointer names

while worklist ≠ ∅:
    p ← worklist.pop()

    for each constraint  pts(p) ⊇ pts(q):          // copy
        if pts(q) ⊄ pts(p):
            pts(p) |= pts(q)
            worklist.push(p)

    for each constraint  pts(p) ⊇ ⋃ pts_mem(r), r ∈ pts(%slot):  // pointer load
        for r in pts(%slot):
            if pts_mem(r) ⊄ pts(p):
                pts(p) |= pts_mem(r)
                worklist.push(p)

    for each constraint  pts_mem(r) ⊇ pts(%v), r ∈ pts(%slot):   // pointer store
        for r in pts(%slot):
            if pts(%v) ⊄ pts_mem(r):
                pts_mem(r) |= pts(%v)
                // all PointerLoad through r must be re-evaluated
                for p2 that load from any r' ∈ pts(%slot):
                    worklist.push(p2)

    for each StructFieldGep  pts(p) ⊇ { r$fN | r ∈ pts(%base) }:
        new_locs = { AbstractLoc(r.0 + "$f" + N) | r ∈ pts(%base) }
        if new_locs ⊄ pts(p):
            pts(p) |= new_locs
            worklist.push(p)
```

**Termination:** the lattice height is bounded by the total number of distinct
abstract locations (one per alloca + one per call site + fields on demand).
Each iteration adds at least one element to some set.  Monotone growth
guarantees termination.

**Complexity:** O(n³) worst case (n = number of pointer SSA names in the
module).  In SSA form the constraint graph is sparse and the constant factor
is small; the wave-propagation optimisation from Hardekopf & Lin (2007) can
reduce it further if needed.

---

## Integration with the Pipeline

### Where AA runs

`run_alias_analysis` is called in two places:

1. **`driver.rs::analyze_module_with_llm`** — once on the entire module, before
   the summary-accumulation loop.  The result is shared across all
   `adapt_with_purity_and_summaries` calls for that module.

2. **`driver.rs::analyze_with_summaries`** — on the single `FunctionGraph`
   being lowered, for callers that bypass `analyze_module_with_llm`.  The
   per-function AA is a sound over-approximation of the full module result.

### How `resolve_memory_effects` uses `AliasResult`

**Unresolved `PointerStore { target_slot, value_ptr }`** (the stored pointer
`value_ptr` is not in the `PointerEnv`):

```
locs = alias.points_to(value_ptr)
if |locs| == 1:
    bind target_slot → sole region at offset 0
else:
    leave target_slot unbound  // ambiguous or unknown → conservative
```

**Unresolved `PointerLoad { target_ptr, source_slot }`** (the source slot is
not in the `PointerEnv`):

```
candidate_regions = pts(source_slot)          // where source_slot points
stored = ⋃ { stored_into(r) | r ∈ candidate_regions }
if |stored| == 1:
    bind target_ptr → sole region at offset 0
else:
    leave target_ptr unbound  // ambiguous or unknown → conservative
```

When `pts` is empty (pointer provenance unknown) the effect stays a `Nop` and
the downstream analysis may produce `UNKNOWN` — the same as the pre-AA
behaviour.

### `HavocRegions` transfer effect

```rust
/// Havoc a specific list of memory regions.
/// WP: drops top-level And conjuncts that mention any listed region;
///     other formula shapes mentioning the region become True.
HavocRegions { regions: Vec<String> }
```

This is used when a store target resolves to a known set of regions but the
stored value is not a simple constant, allowing targeted rather than global
havocing.

---

## Complexity and Precision Summary

| Property | This design |
|----------|------------|
| Algorithm | Flow-insensitive, field-sensitive Andersen |
| Scope | Whole-program (module), one pass |
| Complexity | O(n³) worst case on SSA pointer names |
| Heap regions | One per `malloc`/`new` call site; sub-regions per struct field via StructFieldGep |
| Aliasing default | Distinct regions assumed non-aliasing unless the solver proves otherwise |
| Fallback | If pts(p) is empty (pointer provenance unknown), havoce all heap regions — same as current behaviour |
| Pointer parameter aliasing | `fn$__ext_I` and `fn$__ext_J` alias iff the solver puts them in the same pts set at some call site |

---

## References

1. **Andersen, L.O. (1994).** "Program Analysis and Specialization for the C
   Programming Language." PhD thesis, DIKU, University of Copenhagen.
   *The foundational inclusion-based points-to analysis.  Sections 2–3 define
   the constraint rules adapted verbatim in the Constraint Rules section above.*

2. **Steensgaard, B. (1996).** "Points-to Analysis in Almost Linear Time."
   *POPL 1996*, pp. 32–41. ACM.
   *The unification-based alternative; cited to justify why Andersen was
   preferred: Steensgaard conflates fields of independent structs.*

3. **Pearce, D.J., Kelly, P.H.J., and Hankin, C. (2004).** "Efficient
   Field-Sensitive Pointer Analysis of C." *PASTE 2004*, pp. 37–42. ACM.
   *The field-sensitive Andersen extension; the `$fN` access-path naming
   used here directly follows their field-access-path model.*

4. **Hardekopf, B. and Lin, C. (2007).** "The Ant and the Grasshopper: Fast
   and Accurate Pointer Analysis for Millions of Lines of Code." *PLDI 2007*,
   pp. 290–299. ACM.
   *Wave-propagation optimisation that reduces the O(n³) constant factor;
   the priority worklist strategy in the Solver section is derived from §4.*

5. **Hind, M. (2001).** "Pointer Analysis: Haven't We Solved This Problem
   Yet?" *PASTE 2001*, pp. 54–61. ACM.
   *Survey quantifying the precision–cost tradeoff; Table 1 directly informed
   the algorithm-selection rationale in the Algorithm Choice section.*

6. **Lattner, C., Lenharth, A., and Adve, V. (2007).** "Making
   Context-Sensitive Points-to Analysis with Heap Cloning Practical for the
   Real World." *PLDI 2007*, pp. 278–289. ACM.
   *LLVM-specific points-to analysis; the per-call-site heap abstraction
   (`heap$callC`) and the bitcast-follows-malloc pattern for type recovery
   are taken from §3.*

7. **Sui, Y. and Xue, J. (2016).** "SVF: Interprocedural Static Value-Flow
   Analysis in LLVM." *CC 2016*, pp. 265–266. ACM.
   *State-of-the-art LLVM alias analysis library; the constraint
   representation over LLVM SSA (PAG / VFG) is the primary implementation
   reference for mapping LLVM instructions to inclusion constraints.*

8. **Landi, W. and Ryder, B.G. (1992).** "Undecidability of Static Analysis."
   *ACM LOPLAS 1*(4), pp. 323–337.
   *Establishes that full alias analysis is undecidable; justifies why
   sound over-approximation (Andersen) rather than exact analysis is the
   correct framing.*

9. **Godefroid, P., Nori, A.V., Rajamani, S.K., and Tetali, S.D. (2010).**
   "Compositional May-Must Program Analysis: Unleashing the Power of
   Alternation." *POPL 2010*, pp. 43–56. ACM.
   *Primary reference for the bidirectional analysis this tool implements.
   Section 4 of that paper sketches the heap extension whose precise
   realisation this alias analysis enables.*
