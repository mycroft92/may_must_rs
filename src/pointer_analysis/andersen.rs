#![allow(dead_code)]

//! Field-sensitive, flow-insensitive Andersen alias analysis.
//!
//! Runs once on the full module (a slice of `FunctionGraph`s) and produces
//! an [`AliasResult`] that maps each SSA pointer name to the set of abstract
//! memory locations it may point to.
//!
//! The algorithm is inclusion-based (Andersen 1994) with field sensitivity
//! following Pearce et al. (2004).  Flow insensitivity is sound on LLVM SSA
//! because each SSA name has exactly one static definition.  The worklist
//! solver is O(n³) in the number of pointer SSA names; in practice the IR is
//! sparse and this is fast.
//!
//! # Abstract locations
//!
//! Region names follow the same convention as `adapter.rs`:
//!
//! | Source | Name |
//! |--------|------|
//! | `alloca` K in function F | `F$stackK` |
//! | struct field N of stack K | `F$stackK$fN` |
//! | pointer parameter I of F | `F$__ext_I` |
//! | struct field N of ext I | `F$__ext_I$fN` |
//! | global `@g` | `global$@g` |
//! | `malloc`/`new` call site C | `heap$callC` |
//! | struct field N of heap C | `heap$callC$fN` |
//!
//! # References
//!
//! - Andersen (1994) — inclusion-based points-to analysis
//! - Pearce, Kelly, Hankin (2004) — field-sensitive extension
//! - Hardekopf & Lin (2007) — wave-propagation optimisation (priority worklist)

use crate::frontend::llvm_wrap::{Instruction, InstructionOpcode, TypeKind};
use crate::frontend::program_graph::FunctionGraph;
use std::collections::{BTreeSet, HashMap, VecDeque};

// ── Abstract locations ────────────────────────────────────────────────────────

/// An abstract memory location, identified by its region name.
///
/// The name follows the `adapter.rs` region-naming convention so that
/// `AliasResult` and `PointerEnv` regions are directly comparable.
#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct AbstractLoc(pub String);

impl AbstractLoc {
    pub fn new(s: impl Into<String>) -> Self {
        AbstractLoc(s.into())
    }

    /// Returns the abstract location for struct field `field` of this location.
    pub fn field(&self, field: u32) -> Self {
        AbstractLoc(format!("{}$f{}", self.0, field))
    }
}

// ── Analysis result ───────────────────────────────────────────────────────────

/// The result of the whole-module alias analysis.
///
/// Stores two maps:
/// - `pts`: SSA pointer name → set of abstract locations it may point to.
/// - `pts_mem`: abstract region name → set of abstract locations ever stored
///   into that region as pointer values (needed to model `PointerLoad`).
#[derive(Debug, Default, Clone)]
pub struct AliasResult {
    pts: HashMap<String, BTreeSet<AbstractLoc>>,
    pts_mem: HashMap<String, BTreeSet<AbstractLoc>>,
}

impl AliasResult {
    /// The set of abstract locations that SSA pointer `ptr` may point to.
    ///
    /// Returns an empty set if `ptr` was never seen in the IR or has no
    /// known points-to targets (provenance unknown → caller should fall back
    /// to conservative havocing).
    pub fn points_to(&self, ptr: &str) -> &BTreeSet<AbstractLoc> {
        static EMPTY: std::sync::OnceLock<BTreeSet<AbstractLoc>> = std::sync::OnceLock::new();
        self.pts
            .get(ptr)
            .unwrap_or_else(|| EMPTY.get_or_init(BTreeSet::new))
    }

    /// The set of abstract locations that have been stored into region `region`
    /// as pointer values.
    ///
    /// Used to resolve `PointerLoad { source_slot }`: the set of things that
    /// may have been stored there is `stored_into(r)` for each `r ∈ pts(source_slot)`.
    pub fn stored_into(&self, region: &str) -> &BTreeSet<AbstractLoc> {
        static EMPTY: std::sync::OnceLock<BTreeSet<AbstractLoc>> = std::sync::OnceLock::new();
        self.pts_mem
            .get(region)
            .unwrap_or_else(|| EMPTY.get_or_init(BTreeSet::new))
    }

    /// True if two abstract region names may alias — i.e. some pointer in the
    /// module has both in its points-to set simultaneously.
    pub fn may_alias_regions(&self, r1: &str, r2: &str) -> bool {
        if r1 == r2 {
            return true;
        }
        let a = AbstractLoc::new(r1);
        let b = AbstractLoc::new(r2);
        self.pts
            .values()
            .any(|locs| locs.contains(&a) && locs.contains(&b))
    }

    /// All abstract region names that can be reached from the pointer `ptr`
    /// (i.e. `pts(ptr)`), returned as plain strings for use in targeted havocing.
    pub fn pointed_regions(&self, ptr: &str) -> impl Iterator<Item = &str> {
        self.points_to(ptr).iter().map(|l| l.0.as_str())
    }

    /// Inserts `loc` into `pts(target)`.  Returns `true` if the set grew.
    fn insert_pts(&mut self, target: &str, loc: AbstractLoc) -> bool {
        self.pts.entry(target.to_string()).or_default().insert(loc)
    }

    /// Inserts `loc` into `pts_mem(region)`.  Returns `true` if the set grew.
    fn insert_pts_mem(&mut self, region: &str, loc: AbstractLoc) -> bool {
        self.pts_mem
            .entry(region.to_string())
            .or_default()
            .insert(loc)
    }
}

// ── Constraints ───────────────────────────────────────────────────────────────

/// An Andersen inclusion constraint generated from one LLVM instruction.
#[derive(Debug, Clone)]
enum Constraint {
    /// `pts(target) ⊇ { loc }`  — seeded from alloca, parameter, global, malloc.
    Seed { target: String, loc: AbstractLoc },
    /// `pts(target) ⊇ pts(source)`  — bitcast, addrspacecast, plain-offset GEP.
    Copy { target: String, source: String },
    /// `pts(target) ⊇ { r$fN | r ∈ pts(source) }`  — struct-field GEP.
    StructField {
        target: String,
        source: String,
        field: u32,
    },
    /// `pts(target) ⊇ ⋃ { pts_mem(r) | r ∈ pts(source_slot) }`  — load of pointer.
    LoadPtr { target: String, source_slot: String },
    /// `∀ r ∈ pts(target_slot) : pts_mem(r) ⊇ pts(value_ptr)`  — store of pointer.
    StorePtr {
        target_slot: String,
        value_ptr: String,
    },
}

// ── Naming helpers (mirror adapter.rs, no import needed) ─────────────────────

/// Returns the SSA variable name as used in the abstract environment: `fn$<display>`.
///
/// Mirrors `adapter::local_name` so that AA-produced names are directly
/// comparable with `PointerEnv` keys.
fn local_name(fn_name: &str, instr: Instruction) -> String {
    format!("{fn_name}${}", instr.display_name())
}

/// Returns the external region name for the `idx`-th pointer parameter of `fn_name`.
///
/// Mirrors `adapter::ext_region_name`.
fn ext_region(fn_name: &str, idx: usize) -> String {
    format!("{fn_name}$__ext_{idx}")
}

/// Returns the stack region name for the `idx`-th `alloca` in `fn_name`.
///
/// Mirrors the region assigned by `adapter.rs` during its first pass over vertices.
fn alloca_region(fn_name: &str, idx: usize) -> String {
    format!("{fn_name}$stack{idx}")
}

/// Returns the global region name for a global-variable reference instruction.
///
/// Mirrors `adapter.rs`'s `"global${display_name}"` convention.
fn global_region(instr: Instruction) -> String {
    format!("global${}", instr.display_name())
}

/// Returns the heap region name for the allocation call at `call_site_id`.
///
/// Each `malloc`/`new` call site gets a unique, stable region so that
/// different allocation sites remain distinguishable by the analysis.
fn heap_region(call_site_id: usize) -> String {
    format!("heap$call{call_site_id}")
}

/// Returns `true` if `instr` has a pointer result type.
fn is_ptr(instr: Instruction) -> bool {
    matches!(instr.get_type().map(|t| t.kind()), Some(TypeKind::Pointer))
}

/// Returns `true` if `name` is a standard heap-allocation function.
///
/// Recognized names cover the C stdlib allocators (`malloc`, `calloc`,
/// `realloc`) and the Itanium C++ ABI allocation entry points (`_Znwm`,
/// `_Znam`, and their nothrow variants).
fn is_alloc_callee(name: &str) -> bool {
    matches!(
        name,
        "malloc"
            | "calloc"
            | "realloc"
            | "_Znwm"  // operator new(size_t)
            | "_Znam"  // operator new[](size_t)
            | "_ZnwmRKSt9nothrow_t"
            | "_ZnamRKSt9nothrow_t"
    )
}

// ── Constraint generation ─────────────────────────────────────────────────────

/// Walks every instruction in `graphs` and emits the Andersen constraints
/// that its pointer operations imply.
///
/// The five constraint kinds and the instructions that generate them are
/// described in the [`Constraint`] documentation.  The alloca numbering and
/// region-name conventions mirror `adapter.rs` exactly so that the resulting
/// [`AliasResult`] is directly usable by `resolve_memory_effects`.
///
/// A module-wide monotonic `call_site_id` counter ensures that each
/// `malloc`/`new` call site receives a unique, stable [`heap_region`] name
/// even across functions.
fn collect_constraints(graphs: &[FunctionGraph]) -> Vec<Constraint> {
    let mut constraints = Vec::new();
    // Monotonically-increasing call-site counter across the whole module so
    // each malloc site gets a unique stable region name.
    let mut call_site_id: usize = 0;

    for graph in graphs {
        let fn_name = &graph.name;

        // ── 1. Pointer parameters ────────────────────────────────────────────
        for &param_idx in &graph.pointer_param_indices {
            if let Some(param_name) = graph.params.get(param_idx) {
                constraints.push(Constraint::Seed {
                    target: format!("{fn_name}${param_name}"),
                    loc: AbstractLoc::new(ext_region(fn_name, param_idx)),
                });
            }
        }

        // ── 2. Global variable references ───────────────────────────────────
        // Pre-scan all operands to catch globals used anywhere in this function.
        for &instr in &graph.vertices {
            for idx in 0..instr.get_operand_count() {
                if let Some(op) = instr.get_operand(idx) {
                    if op.is_global_variable_ref() && is_ptr(op) {
                        let ptr = local_name(fn_name, op);
                        let region = global_region(op);
                        constraints.push(Constraint::Seed {
                            target: ptr,
                            loc: AbstractLoc::new(region),
                        });
                    }
                }
            }
        }

        // ── 3. Pre-assign alloca regions (must mirror adapter.rs order) ─────
        let mut alloca_map: HashMap<Instruction, String> = HashMap::new();
        {
            let mut stack_idx = 0usize;
            for &instr in &graph.vertices {
                if instr.get_opcode() == InstructionOpcode::Alloca {
                    alloca_map.insert(instr, alloca_region(fn_name, stack_idx));
                    stack_idx += 1;
                }
            }
        }

        // ── 4. Per-instruction constraints ───────────────────────────────────
        for &instr in &graph.vertices {
            match instr.get_opcode() {
                // ── alloca ────────────────────────────────────────────────────
                InstructionOpcode::Alloca => {
                    if let Some(region) = alloca_map.get(&instr) {
                        constraints.push(Constraint::Seed {
                            target: local_name(fn_name, instr),
                            loc: AbstractLoc::new(region.clone()),
                        });
                    }
                }

                // ── getelementptr ─────────────────────────────────────────────
                InstructionOpcode::GetElementPtr => {
                    if !is_ptr(instr) {
                        continue;
                    }
                    let target = local_name(fn_name, instr);
                    let Some(base_op) = instr.get_operand(0) else {
                        continue;
                    };
                    let source = local_name(fn_name, base_op);

                    // Detect the pure struct-field pattern that the adapter
                    // also recognises: SrcTy = Struct, indices = [0, field_N].
                    if let Some(src_ty) = instr.get_gep_source_element_type() {
                        let operands: Vec<Instruction> = instr.get_operands();
                        let indices: Vec<Instruction> = operands.into_iter().skip(1).collect();

                        if src_ty.kind() == TypeKind::Struct && indices.len() == 2 {
                            if let (Some(0), Some(field_idx)) =
                                (indices[0].as_constant_int(), indices[1].as_constant_int())
                            {
                                if field_idx >= 0 {
                                    constraints.push(Constraint::StructField {
                                        target,
                                        source,
                                        field: field_idx as u32,
                                    });
                                    continue;
                                }
                            }
                        }
                    }
                    // Plain offset GEP — stays in the same region.
                    constraints.push(Constraint::Copy { target, source });
                }

                // ── load (of a pointer value) ─────────────────────────────────
                InstructionOpcode::Load => {
                    if !is_ptr(instr) {
                        continue;
                    }
                    let Some(slot_op) = instr.get_operand(0) else {
                        continue;
                    };
                    constraints.push(Constraint::LoadPtr {
                        target: local_name(fn_name, instr),
                        source_slot: local_name(fn_name, slot_op),
                    });
                }

                // ── store (of a pointer value) ─────────────────────────────────
                InstructionOpcode::Store => {
                    let Some(val_op) = instr.get_operand(0) else {
                        continue;
                    };
                    if !is_ptr(val_op) {
                        continue;
                    }
                    let Some(slot_op) = instr.get_operand(1) else {
                        continue;
                    };
                    constraints.push(Constraint::StorePtr {
                        target_slot: local_name(fn_name, slot_op),
                        value_ptr: local_name(fn_name, val_op),
                    });
                }

                // ── bitcast / addrspacecast ────────────────────────────────────
                InstructionOpcode::BitCast | InstructionOpcode::AddrSpaceCast => {
                    if !is_ptr(instr) {
                        continue;
                    }
                    let Some(src_op) = instr.get_operand(0) else {
                        continue;
                    };
                    constraints.push(Constraint::Copy {
                        target: local_name(fn_name, instr),
                        source: local_name(fn_name, src_op),
                    });
                }

                // ── phi (pointer) ─────────────────────────────────────────────
                InstructionOpcode::PHI => {
                    if !is_ptr(instr) {
                        continue;
                    }
                    let target = local_name(fn_name, instr);
                    for (_block, incoming) in instr.get_phi_incomings() {
                        constraints.push(Constraint::Copy {
                            target: target.clone(),
                            source: local_name(fn_name, incoming),
                        });
                    }
                }

                // ── call ───────────────────────────────────────────────────────
                InstructionOpcode::Call => {
                    let Some(callee) = instr.get_called_function() else {
                        continue;
                    };

                    if is_alloc_callee(&callee) {
                        // Each allocation call site gets its own fresh heap region.
                        let region = heap_region(call_site_id);
                        call_site_id += 1;
                        if is_ptr(instr) {
                            constraints.push(Constraint::Seed {
                                target: local_name(fn_name, instr),
                                loc: AbstractLoc::new(region),
                            });
                        }
                    } else if callee != "may_assert" {
                        // Connect actual pointer arguments to the callee's ext regions
                        // so interprocedural field constraints propagate.
                        for (arg_idx, arg) in instr.get_call_args().into_iter().enumerate() {
                            if is_ptr(arg) {
                                constraints.push(Constraint::Copy {
                                    target: ext_region(&callee, arg_idx),
                                    source: local_name(fn_name, arg),
                                });
                            }
                        }
                        // Calls returning a pointer: pts stays empty (unknown provenance)
                        // unless the callee is in the module (handled by parameter flow above).
                    }
                }

                _ => {}
            }
        }
    }

    constraints
}

// ── Worklist solver ───────────────────────────────────────────────────────────

/// Run the worklist fixpoint over `constraints` and return the saturated
/// [`AliasResult`].
///
/// # Algorithm
///
/// 1. Seed `pts` from all [`Constraint::Seed`] entries.
/// 2. Build a reverse index `source → constraint indices` so that when
///    `pts(p)` grows, only the constraints that depend on `p` are re-queued.
/// 3. Initialise the worklist with every constraint whose source already has a
///    non-empty `pts` set (the seeded pointers).
/// 4. Repeatedly pop a constraint and apply it; if any `pts`/`pts_mem` set
///    grows, push the newly-affected constraints back onto the worklist.
///
/// Termination is guaranteed because the pts lattice is finite (bounded by
/// the number of distinct abstract locations in the module) and each
/// worklist step adds at least one element that was not there before.
fn solve(constraints: Vec<Constraint>) -> AliasResult {
    let mut result = AliasResult::default();

    // Seed the initial pts sets.
    for c in &constraints {
        if let Constraint::Seed { target, loc } = c {
            result.insert_pts(target, loc.clone());
        }
    }

    // Build a reverse index: for each pointer name p, the list of constraint
    // indices where p appears as a *source* (so we know which constraints to
    // re-evaluate when pts(p) grows).
    let mut source_to_constraints: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, c) in constraints.iter().enumerate() {
        match c {
            Constraint::Copy { source, .. } | Constraint::StructField { source, .. } => {
                source_to_constraints
                    .entry(source.clone())
                    .or_default()
                    .push(idx);
            }
            Constraint::LoadPtr { source_slot, .. } => {
                source_to_constraints
                    .entry(source_slot.clone())
                    .or_default()
                    .push(idx);
            }
            Constraint::StorePtr {
                target_slot,
                value_ptr,
            } => {
                source_to_constraints
                    .entry(target_slot.clone())
                    .or_default()
                    .push(idx);
                source_to_constraints
                    .entry(value_ptr.clone())
                    .or_default()
                    .push(idx);
            }
            Constraint::Seed { .. } => {}
        }
    }

    // Initialise the worklist with every pointer that already has a non-empty
    // pts set (i.e. the seeded pointers).
    let mut worklist: VecDeque<usize> = VecDeque::new();
    let mut in_worklist: Vec<bool> = vec![false; constraints.len()];

    for (ptr, constraint_indices) in &source_to_constraints {
        if result.pts.contains_key(ptr.as_str()) {
            for &idx in constraint_indices {
                if !in_worklist[idx] {
                    worklist.push_back(idx);
                    in_worklist[idx] = true;
                }
            }
        }
    }

    while let Some(idx) = worklist.pop_front() {
        in_worklist[idx] = false;
        let c = &constraints[idx];

        match c {
            Constraint::Seed { .. } => {}

            Constraint::Copy { target, source } => {
                let src_locs: Vec<AbstractLoc> = result
                    .pts
                    .get(source.as_str())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                for loc in src_locs {
                    if result.insert_pts(target, loc) {
                        // pts(target) grew — re-evaluate constraints with target as source.
                        for &dep in source_to_constraints
                            .get(target.as_str())
                            .unwrap_or(&vec![])
                        {
                            if !in_worklist[dep] {
                                worklist.push_back(dep);
                                in_worklist[dep] = true;
                            }
                        }
                    }
                }
            }

            Constraint::StructField {
                target,
                source,
                field,
            } => {
                let src_locs: Vec<AbstractLoc> = result
                    .pts
                    .get(source.as_str())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                for loc in src_locs {
                    let field_loc = loc.field(*field);
                    if result.insert_pts(target, field_loc) {
                        for &dep in source_to_constraints
                            .get(target.as_str())
                            .unwrap_or(&vec![])
                        {
                            if !in_worklist[dep] {
                                worklist.push_back(dep);
                                in_worklist[dep] = true;
                            }
                        }
                    }
                }
            }

            Constraint::LoadPtr {
                target,
                source_slot,
            } => {
                let slot_locs: Vec<AbstractLoc> = result
                    .pts
                    .get(source_slot.as_str())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                for slot_loc in slot_locs {
                    let mem_locs: Vec<AbstractLoc> = result
                        .pts_mem
                        .get(&slot_loc.0)
                        .cloned()
                        .unwrap_or_default()
                        .into_iter()
                        .collect();
                    for mem_loc in mem_locs {
                        if result.insert_pts(target, mem_loc) {
                            for &dep in source_to_constraints
                                .get(target.as_str())
                                .unwrap_or(&vec![])
                            {
                                if !in_worklist[dep] {
                                    worklist.push_back(dep);
                                    in_worklist[dep] = true;
                                }
                            }
                        }
                    }
                }
            }

            Constraint::StorePtr {
                target_slot,
                value_ptr,
            } => {
                let slot_locs: Vec<AbstractLoc> = result
                    .pts
                    .get(target_slot.as_str())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                let val_locs: Vec<AbstractLoc> = result
                    .pts
                    .get(value_ptr.as_str())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .collect();
                for slot_loc in &slot_locs {
                    for val_loc in &val_locs {
                        if result.insert_pts_mem(&slot_loc.0, val_loc.clone()) {
                            // pts_mem(slot_loc) grew — re-evaluate LoadPtr constraints
                            // that read from slot_loc's region by re-adding all
                            // LoadPtr constraints whose source overlaps with slot_loc.
                            for (c2_idx, c2) in constraints.iter().enumerate() {
                                if let Constraint::LoadPtr { source_slot, .. } = c2 {
                                    if result
                                        .pts
                                        .get(source_slot.as_str())
                                        .map(|s| s.contains(slot_loc))
                                        .unwrap_or(false)
                                        && !in_worklist[c2_idx]
                                    {
                                        worklist.push_back(c2_idx);
                                        in_worklist[c2_idx] = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    result
}

// ── Public entry point ────────────────────────────────────────────────────────

/// Run the whole-module alias analysis on `graphs` and return an [`AliasResult`].
///
/// This is the public entry point. It chains [`collect_constraints`] and
/// [`solve`], and is called by the driver before the summary-inference loop
/// and by [`analyze_with_summaries`] for single-function analysis.
///
/// The resulting [`AliasResult`] is consumed by `resolve_memory_effects`
/// (inside `adapt_with_purity_and_summaries`) to handle pointer operations
/// that the local `PointerEnv` could not resolve:
///
/// - **`PointerStore`**: if `pts(value_ptr)` is a singleton, `target_slot`
///   is bound to that region in the env.
/// - **`PointerLoad`**: if the union of `pts_mem(r)` for all `r ∈ pts(source_slot)`
///   is a singleton, `target_ptr` is bound to that region.
///
/// When the points-to set is empty or ambiguous the effect remains a `Nop`
/// and the downstream analysis treats the pointer as unresolved (conservative).
pub fn run_alias_analysis(graphs: &[FunctionGraph]) -> AliasResult {
    let constraints = collect_constraints(graphs);
    solve(constraints)
}

// ── Unit tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(target: &str, loc: &str) -> Constraint {
        Constraint::Seed {
            target: target.to_string(),
            loc: AbstractLoc::new(loc),
        }
    }

    fn copy(target: &str, source: &str) -> Constraint {
        Constraint::Copy {
            target: target.to_string(),
            source: source.to_string(),
        }
    }

    fn field(target: &str, source: &str, f: u32) -> Constraint {
        Constraint::StructField {
            target: target.to_string(),
            source: source.to_string(),
            field: f,
        }
    }

    fn store_ptr(slot: &str, val: &str) -> Constraint {
        Constraint::StorePtr {
            target_slot: slot.to_string(),
            value_ptr: val.to_string(),
        }
    }

    fn load_ptr(target: &str, slot: &str) -> Constraint {
        Constraint::LoadPtr {
            target: target.to_string(),
            source_slot: slot.to_string(),
        }
    }

    #[test]
    fn seed_populates_pts() {
        let r = solve(vec![seed("p", "stack0")]);
        assert!(r.points_to("p").contains(&AbstractLoc::new("stack0")));
    }

    #[test]
    fn copy_propagates_pts() {
        let r = solve(vec![seed("p", "stack0"), copy("q", "p")]);
        assert!(r.points_to("q").contains(&AbstractLoc::new("stack0")));
    }

    #[test]
    fn struct_field_appends_subscript() {
        let r = solve(vec![seed("p", "stack0"), field("fp", "p", 1)]);
        assert!(r.points_to("fp").contains(&AbstractLoc::new("stack0$f1")));
        assert!(!r.points_to("fp").contains(&AbstractLoc::new("stack0")));
    }

    #[test]
    fn store_and_load_ptr_roundtrip() {
        // store p into slot q, then load from q → should recover p's targets
        let cs = vec![
            seed("p", "stack0"),
            seed("q", "stack1"),
            store_ptr("q", "p"), // pts_mem(stack1) ⊇ pts(p) = {stack0}
            load_ptr("r", "q"),  // pts(r) ⊇ pts_mem(stack1) = {stack0}
        ];
        let r = solve(cs);
        assert!(r.points_to("r").contains(&AbstractLoc::new("stack0")));
    }

    #[test]
    fn chain_of_copies_propagates() {
        let r = solve(vec![
            seed("a", "heap$call0"),
            copy("b", "a"),
            copy("c", "b"),
            copy("d", "c"),
        ]);
        assert!(r.points_to("d").contains(&AbstractLoc::new("heap$call0")));
    }

    #[test]
    fn may_alias_regions_true_for_same() {
        let r = solve(vec![seed("p", "stack0")]);
        assert!(r.may_alias_regions("stack0", "stack0"));
    }

    #[test]
    fn may_alias_regions_false_for_disjoint() {
        let r = solve(vec![seed("p", "stack0"), seed("q", "stack1")]);
        assert!(!r.may_alias_regions("stack0", "stack1"));
    }

    #[test]
    fn may_alias_regions_true_when_ptr_covers_both() {
        // p → {stack0, stack1} (via two copies)
        let r = solve(vec![
            seed("a", "stack0"),
            seed("b", "stack1"),
            copy("p", "a"),
            copy("p", "b"),
        ]);
        assert!(r.may_alias_regions("stack0", "stack1"));
    }

    #[test]
    fn nested_field_chaining() {
        // gep(gep(alloca, 0, 1), 0, 2) → region stack0$f1$f2
        let r = solve(vec![
            seed("base", "stack0"),
            field("fp1", "base", 1),
            field("fp2", "fp1", 2),
        ]);
        assert!(r
            .points_to("fp2")
            .contains(&AbstractLoc::new("stack0$f1$f2")));
    }
}
