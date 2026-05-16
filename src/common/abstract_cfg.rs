//! Abstract control-flow graph, transfer functions, and WP computation.
//!
//! This module is the shared representation that sits between the LLVM
//! lowering layer (`adapter.rs`) and the analysis passes (`backward.rs`,
//! `loops.rs`). It provides three things:
//!
//! 1. **[`AbstractCfg`]** — a directed graph of [`AbstractNode`]s connected
//!    by [`AbstractEdge`]s. Each node carries a [`TransferFn`] (the semantics
//!    of the basic block), and each edge carries a guard and optional
//!    additional effects (typically the branch condition).
//!
//! 2. **[`TransferEffect`]** / **[`TransferFn`]** — a structured, first-order
//!    description of what a basic block *does*: variable assignments, memory
//!    stores, pointer arithmetic, assumptions, and obligations. `TransferFn`
//!    exposes both a weakest-precondition transformer ([`TransferFn::wp`])
//!    for backward propagation and a strongest-postcondition transformer
//!    ([`TransferFn::sp`]) for forward propagation.
//!
//! 3. **Substitution helpers** — public functions that perform capture-free
//!    variable and memory-region substitution inside [`Formula`] and [`Term`]
//!    expressions, used by the WP engine and the backward analysis.
//!
//! # Node and edge ids
//!
//! [`CfgNodeId`] and [`CfgEdgeId`] are opaque integer wrappers allocated
//! monotonically by [`AbstractCfg`]. They are stable for the lifetime of the
//! CFG and safe to store in external maps.
//!
//! # Single-exit invariant
//!
//! The backward analysis requires exactly one exit node. Call
//! [`AbstractCfg::ensure_single_exit`] after construction to enforce this; it
//! inserts a synthetic merge node if multiple concrete `Return` exits were
//! recorded via [`AbstractCfg::mark_exit`].

#![allow(dead_code)]

use crate::common::formula::{Formula, Memory, Term, Var};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use thiserror::Error;

/// An opaque, copy-cheaply handle for a node in an [`AbstractCfg`].
///
/// Ids are allocated sequentially starting at 0 (the entry) and are stable
/// for the lifetime of the CFG. They implement `Ord` so they can be used as
/// `BTreeMap` keys without additional hashing overhead.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct CfgNodeId(pub usize);

/// An opaque, copy-cheaply handle for an edge in an [`AbstractCfg`].
///
/// Like [`CfgNodeId`], ids are allocated sequentially and are stable for the
/// lifetime of the CFG. Storing an edge id is cheaper than cloning the full
/// [`AbstractEdge`] when only the identity (e.g. back-edge detection) matters.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct CfgEdgeId(pub usize);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl SourceLocation {
    pub fn new(file: impl Into<String>, line: u32, column: u32) -> Self {
        Self {
            file: file.into(),
            line,
            column,
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.file.is_empty() {
            if self.column == 0 {
                write!(f, "<unknown>:{}", self.line)
            } else {
                write!(f, "<unknown>:{}:{}", self.line, self.column)
            }
        } else if self.column == 0 {
            write!(f, "{}:{}", self.file, self.line)
        } else {
            write!(f, "{}:{}:{}", self.file, self.line, self.column)
        }
    }
}

impl From<crate::common::source::SourceLocation> for SourceLocation {
    fn from(value: crate::common::source::SourceLocation) -> Self {
        SourceLocation::new(value.file, value.line, value.column)
    }
}

impl From<SourceLocation> for crate::common::source::SourceLocation {
    fn from(value: SourceLocation) -> Self {
        crate::common::source::SourceLocation::new(value.file, value.line, value.column)
    }
}

/// Describes how a call site affects the symbolic memory regions.
///
/// When a callee's full summary is not yet available (or the callee is an
/// external function), the analysis must choose a conservative approximation:
/// - `PreservesMemory` — the callee is side-effect free with respect to the
///   memory regions tracked by the caller. WP treats it as a no-op for memory.
/// - `HavocMemory` — the callee may write any memory cell. WP forgets all
///   memory facts across this call site. This is the sound default for unknown
///   callees.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CallMemoryEffect {
    /// The call does not modify any symbolically-tracked memory region.
    PreservesMemory,
    /// The call may modify any memory region; all memory knowledge is discarded.
    HavocMemory,
}

/// The right-hand side of a [`TransferEffect::Assign`].
///
/// Separating numeric terms from Boolean predicates avoids forcing the WP
/// engine to guess the sort of an assignment target — it can dispatch directly
/// on the variant and call the appropriate substitution helper.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AssignValue {
    /// The target is assigned a numeric (Int or Real) value.
    Term(Term),
    /// The target (a Bool-sorted variable) is assigned a Boolean formula.
    Predicate(Formula),
}

/// A single atomic effect inside a basic-block transfer function.
///
/// Effects are listed in program order inside [`TransferFn::effects`]. The WP
/// transformer in [`TransferFn::wp`] processes them in *reverse* order (last
/// effect first), while `sp` processes them in forward order.
///
/// # WP semantics summary
///
/// | Variant | WP rule |
/// |---|---|
/// | `Assign` | standard substitution: `post[target := value]` |
/// | `Assume(c)` | `c AND post` (violation must pass through the assume) |
/// | `Obligation(c)` | `c AND post` (assertion site) |
/// | `MemoryStore` | memory substitution: `post[region := store(region, off, val)]` |
/// | All pointer / alloca / load / store / call variants | `post` (transparent — memory modelled elsewhere or havoced by `HavocMemory`) |
/// | `Nop` | `post` |
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TransferEffect {
    /// Assign a scalar value to a variable. WP performs capture-free
    /// substitution of `target` by `value` inside the postcondition.
    Assign { target: Var, value: AssignValue },
    /// Record that `target` (an LLVM `alloca` SSA name) points to `region`
    /// at offset 0. Used by [`TransferFn::pointer_resolution`] to build a
    /// [`PointerEnv`]; WP treats this as a no-op.
    Alloca { target: String, region: String },
    /// Record a GEP (pointer offset): `target = base + offset`. Used by
    /// [`TransferFn::pointer_resolution`] to propagate pointer bindings;
    /// WP treats this as a no-op.
    GetElementPtr {
        target: String,
        base: String,
        offset: Term,
    },
    /// An LLVM `load` instruction that the adapter could not fully resolve to
    /// a symbolic `MemoryStore` + `Select`. WP treats it as a no-op (the
    /// loaded variable remains free/unbound). Where possible the adapter
    /// emits `MemoryStore` + `Assign` instead.
    Load { target: Var, source: String },
    /// An LLVM `store` instruction that the adapter could not resolve to a
    /// symbolic `MemoryStore`. WP treats it as a no-op; the caller may apply
    /// `HavocMemory` if unsoundness is a concern.
    Store { target: String, value: Term },
    /// A memory write that the adapter *has* resolved to a concrete region and
    /// offset. WP performs array-update substitution:
    /// `post[region := store(region, offset, value)]`.
    ///
    /// This is the primary way pointer-based writes enter the formula.
    MemoryStore {
        region: String,
        offset: Term,
        value: Term,
    },
    /// Store a pointer value into a pointer-typed slot. Used only for
    /// pointer-environment propagation; WP treats it as transparent.
    PointerStore {
        target_slot: String,
        value_ptr: String,
    },
    /// Load a pointer value from a pointer-typed slot. Used only for
    /// pointer-environment propagation; WP treats it as transparent.
    PointerLoad {
        target_ptr: String,
        source_slot: String,
    },
    /// Declare that two pointer names alias. Used only for
    /// pointer-environment propagation; WP treats it as transparent.
    PointerAlias { target: String, source: String },
    /// A GEP whose final step is a struct field access.
    ///
    /// Instead of incrementing the offset within the base region, the
    /// result pointer is redirected to a dedicated per-field region
    /// `{base_region}$f{field_index}` at offset 0.  This lets the backward
    /// analysis reason about individual struct fields as independent scalar
    /// (or array) variables without needing array-theory lemmas to separate them.
    ///
    /// Used only for pointer-environment propagation; WP treats it as a no-op.
    StructFieldGep {
        target: String,
        base: String,
        field_index: u32,
    },
    /// A path condition that must hold for execution to reach this point.
    /// WP: `condition => post`.
    Assume(Formula),
    /// An assertion or verification obligation. The analysis must prove
    /// `condition` holds whenever this effect is reached.
    /// WP: `condition AND post` (both the obligation and the continuation
    /// must hold).
    Obligation(Formula),
    /// A no-op placeholder. WP: identity on `post`.
    Nop,
    /// An opaque call whose memory effect is captured by [`CallMemoryEffect`].
    /// `PreservesMemory` → WP is transparent; `HavocMemory` → caller
    /// should havoce memory before applying WP (currently handled at the
    /// driver level, not here).
    Call {
        callee: String,
        memory_effect: CallMemoryEffect,
    },
    /// Havoc a specific set of memory regions.
    ///
    /// Emitted by `resolve_memory_effects` when alias analysis identifies the
    /// target regions of an otherwise-unresolved pointer store.  WP drops any
    /// top-level conjunction in `post` that mentions one of the listed regions,
    /// preserving constraints on non-aliasing regions.
    HavocRegions { regions: Vec<String> },
}

/// An ordered sequence of [`TransferEffect`]s that models the semantics of a
/// basic block (or an edge's side effects).
///
/// The two key operations are:
/// - [`TransferFn::wp`] — weakest precondition, used by the backward analysis
///   to propagate violation conditions from post to pre.
/// - [`TransferFn::sp`] — strongest postcondition, used by the forward
///   direction to propagate reach predicates through loop bodies.
///
/// An empty `TransferFn` is the identity transformer for both WP and SP (see
/// [`TransferFn::identity`]).
#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct TransferFn {
    pub effects: Vec<TransferEffect>,
}

impl TransferFn {
    pub fn new(effects: Vec<TransferEffect>) -> Self {
        Self { effects }
    }

    pub fn identity() -> Self {
        Self::default()
    }

    pub fn is_identity(&self) -> bool {
        self.effects.is_empty()
    }

    /// Compute the weakest precondition of `post` through this transfer function.
    ///
    /// Effects are processed in reverse program order (right-to-left
    /// composition). Each effect applies the rule documented on
    /// [`TransferEffect`]: assignments substitute, assumes add implications,
    /// obligations conjoin, memory stores perform array-update substitution,
    /// and all other effects are transparent.
    pub fn wp(&self, post: &Formula) -> Formula {
        self.effects
            .iter()
            .rev()
            .fold(post.clone(), |acc, effect| wp_one(effect, &acc))
    }

    /// Compute the strongest postcondition of `pre` through this transfer function.
    ///
    /// Effects are processed in forward program order. Assignments add
    /// equalities to the current predicate; assumes and obligations conjoin
    /// their conditions; memory effects and pointer bookkeeping are currently
    /// transparent (the forward direction is used only for reach
    /// overapproximation, where memory details are handled separately via
    /// loop invariants).
    pub fn sp(&self, pre: &Formula) -> Formula {
        self.effects
            .iter()
            .fold(pre.clone(), |acc, effect| sp_one(effect, &acc))
    }

    /// Build a [`PointerEnv`] by replaying only the `Alloca` and
    /// `GetElementPtr` effects in this transfer function.
    ///
    /// The resulting environment maps SSA pointer names to `(region, offset)`
    /// pairs and is used by the adapter to resolve load/store targets before
    /// lowering them to `MemoryStore` or `Select` effects.
    pub fn pointer_resolution(&self) -> PointerEnv {
        let mut env = PointerEnv::default();
        for effect in &self.effects {
            match effect {
                TransferEffect::Alloca { target, region } => {
                    env.bind(target.clone(), region.clone(), Term::int(0));
                }
                TransferEffect::GetElementPtr {
                    target,
                    base,
                    offset,
                } => {
                    if let Some(parent) = env.get(base) {
                        env.bind(
                            target.clone(),
                            parent.region.clone(),
                            Term::add(parent.offset.clone(), offset.clone()),
                        );
                    }
                }
                TransferEffect::StructFieldGep {
                    target,
                    base,
                    field_index,
                } => {
                    if let Some(parent) = env.get(base) {
                        let field_region = format!("{}$f{}", parent.region, field_index);
                        env.bind(target.clone(), field_region, Term::int(0));
                    }
                }
                _ => {}
            }
        }
        env
    }
}

/// A partial map from LLVM SSA pointer names to their resolved memory region
/// and integer offset.
///
/// Built incrementally by [`TransferFn::pointer_resolution`] as `Alloca` and
/// `GetElementPtr` effects are replayed. The adapter uses this to resolve
/// `load`/`store` targets to `(region, offset)` pairs before emitting
/// `MemoryStore` / `Select` effects into the abstract transfer function.
///
/// Pointer names that cannot be resolved (e.g. function arguments, GEP bases
/// that are themselves unresolved) are simply absent from the map; callers
/// must handle the `None` case conservatively.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct PointerEnv {
    bindings: HashMap<String, PointerBinding>,
}

impl PointerEnv {
    /// Record that the pointer `pointer` points to `region` at integer `offset`.
    pub fn bind(&mut self, pointer: String, region: String, offset: Term) {
        self.bindings
            .insert(pointer, PointerBinding { region, offset });
    }

    /// Look up the resolved binding for `pointer`, returning `None` if it
    /// was never bound (e.g. it is a function argument or unresolved GEP).
    pub fn get(&self, pointer: &str) -> Option<&PointerBinding> {
        self.bindings.get(pointer)
    }
}

/// A resolved pointer target: the name of the memory region and the integer
/// term giving the offset within that region.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointerBinding {
    /// The logical memory region name (e.g. `stack0`, `fn$__ext_0`).
    pub region: String,
    /// The offset within the region as an integer term (often a constant,
    /// but may involve variables after GEP arithmetic).
    pub offset: Term,
}

/// Classifies the role of a node in the CFG.
///
/// The backward analysis uses this to locate the unique exit point; the
/// forward analysis seeds the entry. `SyntheticExit` nodes are inserted by
/// [`AbstractCfg::ensure_single_exit`] and carry no transfer effects of their
/// own.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum NodeKind {
    /// The unique function entry point, always `CfgNodeId(0)`.
    Entry,
    /// An ordinary basic block with no special structural role.
    Normal,
    /// A concrete function return (one of potentially many before
    /// `ensure_single_exit` is called).
    Exit,
    /// A merge node inserted by `ensure_single_exit` to unify multiple
    /// `Exit` nodes into a single exit. Has no transfer effects.
    SyntheticExit,
}

/// A node in the abstract CFG, corresponding to a basic block.
///
/// `pre` and `post` are scratch fields used by analysis passes to annotate
/// nodes with their computed reach/state predicates; they are initialised to
/// `True` and updated in-place during the analysis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractNode {
    /// Stable id within the parent [`AbstractCfg`].
    pub id: CfgNodeId,
    /// Human-readable label, typically the LLVM basic-block name.
    pub label: String,
    pub kind: NodeKind,
    /// Optional source location extracted from LLVM debug metadata.
    pub source_location: Option<SourceLocation>,
    /// The semantics of this block as a sequence of [`TransferEffect`]s.
    pub transfer: TransferFn,
    /// Scratch field: precondition computed by the analysis (reach or WP).
    pub pre: Formula,
    /// Scratch field: postcondition computed by the analysis.
    pub post: Formula,
}

/// A directed edge in the abstract CFG, corresponding to a control-flow
/// transition between basic blocks.
///
/// An edge carries a `guard` (the branch condition that must hold to take
/// this edge) and an optional list of `effects` (e.g. the `phi`-node
/// assignments lowered at the target's incoming edge). The full transfer
/// function for the edge can be obtained with [`AbstractEdge::transfer`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractEdge {
    pub id: CfgEdgeId,
    pub source: CfgNodeId,
    pub target: CfgNodeId,
    /// The Boolean condition that must be satisfied to take this edge.
    /// `Formula::True` for unconditional jumps.
    pub guard: Formula,
    /// Effects executed when this edge is taken (e.g. phi assignments).
    pub effects: Vec<TransferEffect>,
}

impl AbstractEdge {
    pub fn transfer(&self) -> TransferFn {
        TransferFn::new(self.effects.clone())
    }
}

/// A mutable, directed abstract control-flow graph for one function.
///
/// Nodes represent basic blocks; edges represent control-flow transitions.
/// Construction is incremental: call [`AbstractCfg::new`] to create the entry
/// node, then [`add_node`](AbstractCfg::add_node) /
/// [`add_edge`](AbstractCfg::add_edge) to build the graph, and finally
/// [`ensure_single_exit`](AbstractCfg::ensure_single_exit) to guarantee a
/// unique exit point before handing the CFG to the analysis.
///
/// The struct also exposes graph-structural queries needed by the analysis:
/// [`detect_back_edges`](AbstractCfg::detect_back_edges) for loop detection and
/// [`topological_order`](AbstractCfg::topological_order) /
/// [`topological_order_excluding`](AbstractCfg::topological_order_excluding)
/// for DAG-order traversal once back edges are removed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractCfg {
    nodes: BTreeMap<CfgNodeId, AbstractNode>,
    edges: BTreeMap<CfgEdgeId, AbstractEdge>,
    entry: CfgNodeId,
    /// All nodes marked as concrete function returns via `mark_exit`.
    concrete_exits: BTreeSet<CfgNodeId>,
    /// The unique exit after `ensure_single_exit` has run; `None` until then.
    exit: Option<CfgNodeId>,
    next_node: usize,
    next_edge: usize,
}

impl AbstractCfg {
    pub fn new(entry_label: impl Into<String>) -> Self {
        let entry_id = CfgNodeId(0);
        let entry_node = AbstractNode {
            id: entry_id,
            label: entry_label.into(),
            kind: NodeKind::Entry,
            source_location: None,
            transfer: TransferFn::identity(),
            pre: Formula::True,
            post: Formula::True,
        };
        let mut nodes = BTreeMap::new();
        nodes.insert(entry_id, entry_node);
        Self {
            nodes,
            edges: BTreeMap::new(),
            entry: entry_id,
            concrete_exits: BTreeSet::new(),
            exit: None,
            next_node: 1,
            next_edge: 0,
        }
    }

    /// Return the id of the unique entry node (always `CfgNodeId(0)`).
    pub fn entry(&self) -> CfgNodeId {
        self.entry
    }

    /// Return the unique exit node id, or `None` if
    /// [`ensure_single_exit`](AbstractCfg::ensure_single_exit) has not yet
    /// been called.
    pub fn exit(&self) -> Option<CfgNodeId> {
        self.exit
    }

    pub fn node(&self, id: CfgNodeId) -> Result<&AbstractNode, CfgError> {
        self.nodes.get(&id).ok_or(CfgError::UnknownNode { id })
    }

    pub fn node_mut(&mut self, id: CfgNodeId) -> Result<&mut AbstractNode, CfgError> {
        self.nodes.get_mut(&id).ok_or(CfgError::UnknownNode { id })
    }

    pub fn edge(&self, id: CfgEdgeId) -> Result<&AbstractEdge, CfgError> {
        self.edges.get(&id).ok_or(CfgError::UnknownEdge { id })
    }

    pub fn nodes(&self) -> &BTreeMap<CfgNodeId, AbstractNode> {
        &self.nodes
    }

    pub fn edges(&self) -> &BTreeMap<CfgEdgeId, AbstractEdge> {
        &self.edges
    }

    pub fn node_ids(&self) -> impl Iterator<Item = CfgNodeId> + '_ {
        self.nodes.keys().copied()
    }

    pub fn edge_ids(&self) -> impl Iterator<Item = CfgEdgeId> + '_ {
        self.edges.keys().copied()
    }

    /// Add a new `Normal`-kind node with the given label and transfer function.
    ///
    /// Returns the freshly allocated [`CfgNodeId`]. The node's `pre` and
    /// `post` are initialised to `True`; analysis passes overwrite them.
    pub fn add_node(&mut self, label: impl Into<String>, transfer: TransferFn) -> CfgNodeId {
        let id = CfgNodeId(self.next_node);
        self.next_node += 1;
        self.nodes.insert(
            id,
            AbstractNode {
                id,
                label: label.into(),
                kind: NodeKind::Normal,
                source_location: None,
                transfer,
                pre: Formula::True,
                post: Formula::True,
            },
        );
        id
    }

    pub fn set_entry_transfer(&mut self, transfer: TransferFn) {
        if let Some(entry) = self.nodes.get_mut(&self.entry) {
            entry.transfer = transfer;
        }
    }

    pub fn set_source_location(
        &mut self,
        id: CfgNodeId,
        location: SourceLocation,
    ) -> Result<(), CfgError> {
        self.node_mut(id)?.source_location = Some(location);
        Ok(())
    }

    /// Mark node `id` as a concrete function return point.
    ///
    /// Calling this multiple times (once per `ret` instruction) is normal;
    /// [`ensure_single_exit`](AbstractCfg::ensure_single_exit) will merge them
    /// later. Marking the entry node as an exit is silently ignored because a
    /// zero-instruction function is a degenerate case the analysis doesn't
    /// need to handle.
    pub fn mark_exit(&mut self, id: CfgNodeId) -> Result<(), CfgError> {
        if id != self.entry {
            self.node_mut(id)?.kind = NodeKind::Exit;
            self.concrete_exits.insert(id);
            self.exit = None;
        }
        Ok(())
    }

    /// Add a directed edge from `source` to `target` with the given guard and
    /// edge-level effects.
    ///
    /// Returns `Err` if either node id is unknown. Parallel edges (same source
    /// and target) are allowed and represent multiple branch arms with
    /// different guards.
    pub fn add_edge(
        &mut self,
        source: CfgNodeId,
        target: CfgNodeId,
        guard: Formula,
        effects: Vec<TransferEffect>,
    ) -> Result<CfgEdgeId, CfgError> {
        if !self.nodes.contains_key(&source) {
            return Err(CfgError::UnknownNode { id: source });
        }
        if !self.nodes.contains_key(&target) {
            return Err(CfgError::UnknownNode { id: target });
        }
        let id = CfgEdgeId(self.next_edge);
        self.next_edge += 1;
        self.edges.insert(
            id,
            AbstractEdge {
                id,
                source,
                target,
                guard,
                effects,
            },
        );
        Ok(id)
    }

    pub fn append_edge_effects(
        &mut self,
        id: CfgEdgeId,
        effects: impl IntoIterator<Item = TransferEffect>,
    ) -> Result<(), CfgError> {
        self.edge_mut(id)?.effects.extend(effects);
        Ok(())
    }

    pub fn successors(&self, id: CfgNodeId) -> Vec<CfgNodeId> {
        self.edges
            .values()
            .filter(|edge| edge.source == id)
            .map(|edge| edge.target)
            .collect()
    }

    pub fn predecessors(&self, id: CfgNodeId) -> Vec<CfgNodeId> {
        self.edges
            .values()
            .filter(|edge| edge.target == id)
            .map(|edge| edge.source)
            .collect()
    }

    pub fn outgoing_edges(&self, id: CfgNodeId) -> Vec<CfgEdgeId> {
        self.edges
            .values()
            .filter(|edge| edge.source == id)
            .map(|edge| edge.id)
            .collect()
    }

    pub fn incoming_edges(&self, id: CfgNodeId) -> Vec<CfgEdgeId> {
        self.edges
            .values()
            .filter(|edge| edge.target == id)
            .map(|edge| edge.id)
            .collect()
    }

    /// Ensure the CFG has exactly one exit node, creating a synthetic merge
    /// node if necessary.
    ///
    /// The backward analysis requires a unique exit to seed WP propagation.
    /// This method:
    /// - Returns the existing exit immediately if already resolved.
    /// - Promotes the single concrete exit if there is exactly one.
    /// - Inserts a `SyntheticExit` node and connects all concrete exits to it
    ///   with unconditional `True`-guarded edges if there are multiple exits.
    ///
    /// Returns `Err(CfgError::MissingExit)` if no exit node was ever
    /// registered via [`mark_exit`](AbstractCfg::mark_exit).
    pub fn ensure_single_exit(&mut self) -> Result<CfgNodeId, CfgError> {
        if let Some(exit) = self.exit {
            return Ok(exit);
        }
        match self.concrete_exits.len() {
            0 => Err(CfgError::MissingExit),
            1 => {
                let exit = *self.concrete_exits.iter().next().expect("one exit exists");
                self.exit = Some(exit);
                Ok(exit)
            }
            _ => {
                let synthetic = self.add_node("__synthetic_exit", TransferFn::identity());
                self.node_mut(synthetic)?.kind = NodeKind::SyntheticExit;
                let exits = self.concrete_exits.iter().copied().collect::<Vec<_>>();
                for exit in exits {
                    self.add_edge(exit, synthetic, Formula::True, vec![])?;
                }
                self.exit = Some(synthetic);
                Ok(synthetic)
            }
        }
    }

    /// Return a topological ordering of all nodes, or `None` if the graph
    /// contains a cycle.
    ///
    /// Uses Kahn's algorithm (in-degree queue). The ordering is not unique for
    /// DAGs with multiple source nodes, but is deterministic because the
    /// in-degree map is backed by a `BTreeMap`.
    ///
    /// Returns `None` for any CFG with loops. Use
    /// [`topological_order_excluding`](AbstractCfg::topological_order_excluding)
    /// with the back edges identified by
    /// [`detect_back_edges`](AbstractCfg::detect_back_edges) to obtain an
    /// order over the loop-reduced DAG.
    pub fn topological_order(&self) -> Option<Vec<CfgNodeId>> {
        let mut indegree = self
            .nodes
            .keys()
            .copied()
            .map(|id| (id, 0usize))
            .collect::<BTreeMap<_, _>>();

        for edge in self.edges.values() {
            *indegree.get_mut(&edge.target).expect("target exists") += 1;
        }

        let mut queue = indegree
            .iter()
            .filter_map(|(id, degree)| (*degree == 0).then_some(*id))
            .collect::<Vec<_>>();
        let mut order = Vec::with_capacity(self.nodes.len());

        while let Some(node) = queue.pop() {
            order.push(node);
            for edge in self.edges.values().filter(|edge| edge.source == node) {
                let degree = indegree
                    .get_mut(&edge.target)
                    .expect("target node exists for topological sort");
                *degree -= 1;
                if *degree == 0 {
                    queue.push(edge.target);
                }
            }
        }

        if order.len() == self.nodes.len() {
            Some(order)
        } else {
            None
        }
    }

    /// Return a topological ordering of all nodes after treating the `excluded`
    /// edges as absent, or `None` if removing those edges does not break all
    /// cycles.
    ///
    /// Intended use: pass the back edges returned by
    /// [`detect_back_edges`](AbstractCfg::detect_back_edges) as `excluded` to
    /// obtain a DAG order for the loop-reduced CFG, which is then processed by
    /// the backward WP pass with loop headers treated as cut points.
    pub fn topological_order_excluding(
        &self,
        excluded: &BTreeSet<CfgEdgeId>,
    ) -> Option<Vec<CfgNodeId>> {
        let mut indegree = self
            .nodes
            .keys()
            .copied()
            .map(|id| (id, 0usize))
            .collect::<BTreeMap<_, _>>();

        for edge in self.edges.values() {
            if excluded.contains(&edge.id) {
                continue;
            }
            *indegree.get_mut(&edge.target).expect("target exists") += 1;
        }

        let mut queue = indegree
            .iter()
            .filter_map(|(id, degree)| (*degree == 0).then_some(*id))
            .collect::<Vec<_>>();
        let mut order = Vec::with_capacity(self.nodes.len());

        while let Some(node) = queue.pop() {
            order.push(node);
            for edge in self
                .edges
                .values()
                .filter(|edge| edge.source == node && !excluded.contains(&edge.id))
            {
                let degree = indegree
                    .get_mut(&edge.target)
                    .expect("target node exists for topological sort");
                *degree -= 1;
                if *degree == 0 {
                    queue.push(edge.target);
                }
            }
        }

        if order.len() == self.nodes.len() {
            Some(order)
        } else {
            None
        }
    }

    /// Identify back edges using a DFS from the entry node.
    ///
    /// An edge `(u, v)` is a back edge if `v` is an ancestor of `u` in the
    /// DFS tree, i.e. `v` is currently on the DFS recursion stack when the
    /// edge is first visited. Back edges correspond to loop back-jumps in the
    /// original LLVM IR.
    ///
    /// The returned edge ids are used by the loop analysis in `loops.rs` to
    /// identify loop headers (the targets of back edges) and by
    /// [`topological_order_excluding`](AbstractCfg::topological_order_excluding)
    /// to break cycles for the WP pass.
    pub fn detect_back_edges(&self) -> Vec<CfgEdgeId> {
        let mut visited = BTreeSet::new();
        let mut stack = BTreeSet::new();
        let mut back_edges = Vec::new();
        self.detect_back_edges_from(self.entry, &mut visited, &mut stack, &mut back_edges);
        back_edges
    }

    fn detect_back_edges_from(
        &self,
        node: CfgNodeId,
        visited: &mut BTreeSet<CfgNodeId>,
        stack: &mut BTreeSet<CfgNodeId>,
        back_edges: &mut Vec<CfgEdgeId>,
    ) {
        visited.insert(node);
        stack.insert(node);
        for edge_id in self.outgoing_edges(node) {
            let Ok(edge) = self.edge(edge_id) else {
                continue;
            };
            if stack.contains(&edge.target) {
                back_edges.push(edge.id);
            } else if !visited.contains(&edge.target) {
                self.detect_back_edges_from(edge.target, visited, stack, back_edges);
            }
        }
        stack.remove(&node);
    }

    fn edge_mut(&mut self, id: CfgEdgeId) -> Result<&mut AbstractEdge, CfgError> {
        self.edges.get_mut(&id).ok_or(CfgError::UnknownEdge { id })
    }
}

/// Errors produced by [`AbstractCfg`] mutation and structural query methods.
///
/// These indicate programming mistakes (using a stale id from a different CFG
/// or forgetting to call `mark_exit`) rather than expected analysis outcomes.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum CfgError {
    #[error("unknown node id: {id:?}")]
    UnknownNode { id: CfgNodeId },
    #[error("unknown edge id: {id:?}")]
    UnknownEdge { id: CfgEdgeId },
    /// Returned by [`AbstractCfg::ensure_single_exit`] when no node has been
    /// registered as an exit via [`AbstractCfg::mark_exit`].
    #[error("missing CFG exit")]
    MissingExit,
}

/// Returns `true` if `formula` references the named memory region anywhere in
/// its structure (as `Memory::Var(region)` inside a `select` term).
fn formula_mentions_region(region: &str, formula: &Formula) -> bool {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => false,
        Formula::Not(inner) => formula_mentions_region(region, inner),
        Formula::And(items) | Formula::Or(items) => {
            items.iter().any(|i| formula_mentions_region(region, i))
        }
        Formula::Implies(a, b) => {
            formula_mentions_region(region, a) || formula_mentions_region(region, b)
        }
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => term_mentions_region(region, a) || term_mentions_region(region, b),
        Formula::MemoryEq(a, b) => {
            memory_mentions_region(region, a) || memory_mentions_region(region, b)
        }
    }
}

/// Returns `true` if `term` references the named memory region anywhere in its
/// structure (as `Memory::Var(region)` inside a `select` term).
fn term_mentions_region(region: &str, term: &Term) -> bool {
    match term {
        Term::Int(_) | Term::Real(_) | Term::Var(_) => false,
        Term::BoolToInt(inner) => formula_mentions_region(region, inner),
        Term::Select(mem, idx) => {
            memory_mentions_region(region, mem) || term_mentions_region(region, idx)
        }
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            term_mentions_region(region, a) || term_mentions_region(region, b)
        }
        Term::Neg(inner) => term_mentions_region(region, inner),
    }
}

/// Returns `true` if `memory` is, or recursively contains, the named region.
fn memory_mentions_region(region: &str, memory: &Memory) -> bool {
    match memory {
        Memory::Var(name) => name == region,
        Memory::Store(inner, idx, val) => {
            memory_mentions_region(region, inner)
                || term_mentions_region(region, idx)
                || term_mentions_region(region, val)
        }
    }
}

/// WP helper for `HavocRegions`.
///
/// At `And` nodes, conjuncts that mention `region` are dropped (they become
/// unconstrained after havocing). At other nodes, if `region` is mentioned
/// the entire formula conservatively becomes `True`.  Conjuncts that do not
/// mention `region` are preserved exactly.
fn havoc_region_in_formula(region: &str, formula: Formula) -> Formula {
    if !formula_mentions_region(region, &formula) {
        return formula;
    }
    match formula {
        Formula::And(items) => Formula::and_many(
            items
                .into_iter()
                .filter(|item| !formula_mentions_region(region, item)),
        ),
        _ => Formula::True,
    }
}

fn wp_one(effect: &TransferEffect, post: &Formula) -> Formula {
    match effect {
        TransferEffect::Nop
        | TransferEffect::Alloca { .. }
        | TransferEffect::GetElementPtr { .. }
        | TransferEffect::StructFieldGep { .. }
        | TransferEffect::PointerStore { .. }
        | TransferEffect::PointerLoad { .. }
        | TransferEffect::PointerAlias { .. }
        | TransferEffect::Call { .. }
        | TransferEffect::Load { .. }
        | TransferEffect::Store { .. } => post.clone(),
        TransferEffect::HavocRegions { regions } => {
            let mut result = post.clone();
            for region in regions {
                result = havoc_region_in_formula(region, result);
            }
            result
        }
        TransferEffect::Assign { target, value } => match value {
            AssignValue::Term(term) => substitute_var_in_formula(target, term, post),
            AssignValue::Predicate(predicate) => {
                substitute_bool_var_in_formula(target, predicate, post)
            }
        },
        TransferEffect::Assume(condition) => Formula::and(condition.clone(), post.clone()),
        TransferEffect::Obligation(condition) => Formula::and(condition.clone(), post.clone()),
        TransferEffect::MemoryStore {
            region,
            offset,
            value,
        } => substitute_memory_var_in_formula(
            region,
            &Memory::store(Memory::var(region), offset.clone(), value.clone()),
            post,
        ),
    }
}

fn sp_one(effect: &TransferEffect, pre: &Formula) -> Formula {
    match effect {
        TransferEffect::Nop
        | TransferEffect::Alloca { .. }
        | TransferEffect::GetElementPtr { .. }
        | TransferEffect::StructFieldGep { .. }
        | TransferEffect::PointerStore { .. }
        | TransferEffect::PointerLoad { .. }
        | TransferEffect::PointerAlias { .. }
        | TransferEffect::Load { .. }
        | TransferEffect::Store { .. }
        | TransferEffect::MemoryStore { .. }
        | TransferEffect::Call { .. }
        | TransferEffect::HavocRegions { .. } => pre.clone(),
        TransferEffect::Assign { target, value } => match value {
            AssignValue::Term(term) => Formula::and(
                pre.clone(),
                Formula::eq(Term::Var(target.clone()), term.clone()),
            ),
            AssignValue::Predicate(predicate) => Formula::and(
                pre.clone(),
                Formula::and(
                    Formula::implies(Formula::Var(target.clone()), predicate.clone()),
                    Formula::implies(predicate.clone(), Formula::Var(target.clone())),
                ),
            ),
        },
        TransferEffect::Assume(condition) | TransferEffect::Obligation(condition) => {
            Formula::and(pre.clone(), condition.clone())
        }
    }
}

pub fn substitute_var_in_formula(target: &Var, replacement: &Term, formula: &Formula) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => Formula::not(substitute_var_in_formula(target, replacement, inner)),
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_var_in_formula(target, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_var_in_formula(target, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_var_in_formula(target, replacement, lhs),
            substitute_var_in_formula(target, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_var_in_memory(target, replacement, lhs),
            substitute_var_in_memory(target, replacement, rhs),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
    }
}

pub fn substitute_var_in_term(target: &Var, replacement: &Term, term: &Term) -> Term {
    match term {
        Term::Var(var) if var == target => replacement.clone(),
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(inner) => {
            Term::bool_to_int(substitute_var_in_formula(target, replacement, inner))
        }
        Term::Select(memory, index) => Term::select(
            substitute_var_in_memory(target, replacement, memory),
            substitute_var_in_term(target, replacement, index),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Rem(lhs, rhs) => Term::rem(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Neg(inner) => Term::neg(substitute_var_in_term(target, replacement, inner)),
    }
}

pub fn substitute_var_in_memory(target: &Var, replacement: &Term, memory: &Memory) -> Memory {
    match memory {
        Memory::Var(name) => Memory::var(name),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_var_in_memory(target, replacement, inner),
            substitute_var_in_term(target, replacement, index),
            substitute_var_in_term(target, replacement, value),
        ),
    }
}

pub fn substitute_bool_var_in_formula(
    target: &Var,
    replacement: &Formula,
    formula: &Formula,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) if var == target => replacement.clone(),
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => {
            Formula::not(substitute_bool_var_in_formula(target, replacement, inner))
        }
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_bool_var_in_formula(target, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_bool_var_in_formula(target, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_bool_var_in_formula(target, replacement, lhs),
            substitute_bool_var_in_formula(target, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(lhs.clone(), rhs.clone()),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(lhs.clone(), rhs.clone()),
        Formula::Lt(lhs, rhs) => Formula::lt(lhs.clone(), rhs.clone()),
        Formula::Le(lhs, rhs) => Formula::le(lhs.clone(), rhs.clone()),
        Formula::Gt(lhs, rhs) => Formula::gt(lhs.clone(), rhs.clone()),
        Formula::Ge(lhs, rhs) => Formula::ge(lhs.clone(), rhs.clone()),
    }
}

pub fn substitute_memory_var_in_formula(
    region: &str,
    replacement: &Memory,
    formula: &Formula,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => {
            Formula::not(substitute_memory_var_in_formula(region, replacement, inner))
        }
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_memory_var_in_formula(region, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_memory_var_in_formula(region, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_memory_var_in_formula(region, replacement, lhs),
            substitute_memory_var_in_formula(region, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_memory_var_in_memory(region, replacement, lhs),
            substitute_memory_var_in_memory(region, replacement, rhs),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
    }
}

pub fn substitute_memory_var_in_term(region: &str, replacement: &Memory, term: &Term) -> Term {
    match term {
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(inner) => {
            Term::bool_to_int(substitute_memory_var_in_formula(region, replacement, inner))
        }
        Term::Select(memory, index) => Term::select(
            substitute_memory_var_in_memory(region, replacement, memory),
            substitute_memory_var_in_term(region, replacement, index),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Rem(lhs, rhs) => Term::rem(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Neg(inner) => Term::neg(substitute_memory_var_in_term(region, replacement, inner)),
    }
}

pub fn substitute_memory_var_in_memory(
    region: &str,
    replacement: &Memory,
    memory: &Memory,
) -> Memory {
    match memory {
        Memory::Var(name) if name == region => replacement.clone(),
        Memory::Var(name) => Memory::var(name),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_memory_var_in_memory(region, replacement, inner),
            substitute_memory_var_in_term(region, replacement, index),
            substitute_memory_var_in_term(region, replacement, value),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wp_assignment_substitutes_target() {
        let transfer = TransferFn::new(vec![TransferEffect::Assign {
            target: Var::int("x"),
            value: AssignValue::Term(Term::int(1)),
        }]);
        let post = Formula::eq(
            Term::var("x", crate::common::formula::Sort::Int),
            Term::int(3),
        );
        let pre = transfer.wp(&post);
        assert_eq!(pre, Formula::eq(Term::int(1), Term::int(3)));
    }

    #[test]
    fn wp_assume_creates_conjunction() {
        // In the violation analysis, a trace must pass through assume(c) to reach an
        // assertion, so c must be true.  The violation precondition is therefore
        // `c AND post`, not the Hoare-style implication `c => post`.
        let transfer = TransferFn::new(vec![TransferEffect::Assume(Formula::bool_var("c"))]);
        let pre = transfer.wp(&Formula::bool_var("p"));
        assert_eq!(
            pre,
            Formula::and(Formula::bool_var("c"), Formula::bool_var("p"))
        );
    }

    #[test]
    fn wp_obligation_creates_conjunction() {
        let transfer = TransferFn::new(vec![TransferEffect::Obligation(Formula::bool_var("c"))]);
        let pre = transfer.wp(&Formula::bool_var("p"));
        assert_eq!(
            pre,
            Formula::and(Formula::bool_var("c"), Formula::bool_var("p"))
        );
    }

    #[test]
    fn wp_composes_in_reverse_order() {
        let transfer = TransferFn::new(vec![
            TransferEffect::Assign {
                target: Var::int("x"),
                value: AssignValue::Term(Term::int(1)),
            },
            TransferEffect::Assign {
                target: Var::int("y"),
                value: AssignValue::Term(Term::var("x", crate::common::formula::Sort::Int)),
            },
        ]);
        let post = Formula::eq(
            Term::var("y", crate::common::formula::Sort::Int),
            Term::int(0),
        );
        let pre = transfer.wp(&post);
        assert_eq!(pre, Formula::eq(Term::int(1), Term::int(0)));
    }

    #[test]
    fn sp_assignment_adds_equality() {
        let transfer = TransferFn::new(vec![TransferEffect::Assign {
            target: Var::int("x"),
            value: AssignValue::Term(Term::int(8)),
        }]);
        let sp = transfer.sp(&Formula::bool_var("r"));
        assert_eq!(
            sp,
            Formula::and(
                Formula::bool_var("r"),
                Formula::eq(
                    Term::var("x", crate::common::formula::Sort::Int),
                    Term::int(8)
                ),
            )
        );
    }

    #[test]
    fn topological_order_accepts_dag_and_rejects_cycle() {
        let mut dag = AbstractCfg::new("entry");
        let n1 = dag.add_node("n1", TransferFn::identity());
        let n2 = dag.add_node("n2", TransferFn::identity());
        dag.add_edge(dag.entry(), n1, Formula::True, vec![])
            .unwrap();
        dag.add_edge(n1, n2, Formula::True, vec![]).unwrap();
        assert!(dag.topological_order().is_some());

        let mut cyclic = AbstractCfg::new("entry");
        let a = cyclic.add_node("a", TransferFn::identity());
        cyclic
            .add_edge(cyclic.entry(), a, Formula::True, vec![])
            .unwrap();
        cyclic
            .add_edge(a, cyclic.entry(), Formula::True, vec![])
            .unwrap();
        assert!(cyclic.topological_order().is_none());
    }

    #[test]
    fn ensure_single_exit_creates_synthetic_exit_for_multiple() {
        let mut cfg = AbstractCfg::new("entry");
        let a = cfg.add_node("a", TransferFn::identity());
        let b = cfg.add_node("b", TransferFn::identity());
        cfg.mark_exit(a).unwrap();
        cfg.mark_exit(b).unwrap();
        let exit = cfg.ensure_single_exit().unwrap();
        assert_eq!(cfg.node(exit).unwrap().kind, NodeKind::SyntheticExit);
        assert_eq!(cfg.predecessors(exit).len(), 2);
    }

    #[test]
    fn pointer_resolution_chains_alloca_and_gep() {
        let transfer = TransferFn::new(vec![
            TransferEffect::Alloca {
                target: "%p".to_string(),
                region: "r0".to_string(),
            },
            TransferEffect::GetElementPtr {
                target: "%q".to_string(),
                base: "%p".to_string(),
                offset: Term::int(4),
            },
        ]);
        let env = transfer.pointer_resolution();
        let q = env.get("%q").unwrap();
        assert_eq!(q.region, "r0");
        assert_eq!(q.offset, Term::add(Term::int(0), Term::int(4)));
    }

    #[test]
    fn memory_store_wp_substitutes_memory_region() {
        let transfer = TransferFn::new(vec![TransferEffect::MemoryStore {
            region: "mem".to_string(),
            offset: Term::int(3),
            value: Term::int(9),
        }]);
        let post = Formula::eq(Term::select(Memory::var("mem"), Term::int(3)), Term::int(9));
        let pre = transfer.wp(&post);
        assert!(pre.to_string().contains("(store mem 3 9)"));
    }

    #[test]
    fn source_location_from_source_module() {
        let source = crate::common::source::SourceLocation::new("f.c", 10, 2);
        let lowered: SourceLocation = source.into();
        assert_eq!(lowered.to_string(), "f.c:10:2");
    }
}
