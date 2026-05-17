#![allow(dead_code)]

//! Instruction-level LLVM graph construction.
//!
//! This is the fixed LLVM-facing foundation for the paper-style lowering. The
//! graph stays at instruction granularity, but `may_assert` and obvious noise
//! calls are removed so later analysis layers work on semantic steps rather
//! than frontend scaffolding.
//!
//! `AGENTS.md` treats this file as the fixed foundation for the later paper
//! lowering. The analysis stack may be reconstructed around it, but this raw
//! graph construction remains the source of truth for visible LLVM control and
//! data-flow structure, including the loops and call sites that later become
//! summary/invariant boundaries.

use crate::common::errors::*;
use crate::common::llvm_utils::llvm_wrap::*;
use crate::common::source::SourceLocation;
use dot::Labeller;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};
use std::fs;

const NOISE_CALLS: &[&str] = &["printf", "putchar"];

/// One vertex in the instruction-level CFG.
///
/// `instr` is the LLVM instruction this node represents.
/// `predecessors` and `successors` are the direct control-flow neighbours at
/// instruction granularity — not at basic-block granularity. Within a block,
/// consecutive visible instructions are linked in sequence; across blocks, the
/// last visible instruction of a predecessor block is linked to the first
/// visible instruction of each successor block.
///
/// Predecessors and successors are stored as `BTreeSet` to give a
/// deterministic iteration order (which matters for formula generation).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node {
    pub predecessors: BTreeSet<Instruction>,
    pub instr: Instruction,
    pub successors: BTreeSet<Instruction>,
}

/// A `may_assert` call site extracted from the LLVM IR.
///
/// The `may_assert` call itself is **not** inserted as a graph node — it is
/// stripped from the visible-instruction list. Instead, each call site is
/// recorded here so that the backward analysis knows what to verify and where
/// to anchor it in the CFG.
///
/// Fields:
/// - `asserted_value`: the first argument to `may_assert(cond)` — the `i1`
///   value that must be non-zero on all reachable executions.
/// - `predecessor`: the last visible instruction before the `may_assert` call
///   in the same basic block, if any. Used to attach the obligation at the
///   right program point.
/// - `successor`: the first visible instruction after the `may_assert` call
///   in the same basic block, if any.
/// - `source_location`: file/line/column from DWARF debug info, used in
///   human-readable diagnostic output.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssertSite {
    pub asserted_value: Instruction,
    pub predecessor: Option<Instruction>,
    pub successor: Option<Instruction>,
    pub source_location: SourceLocation,
}

/// A `may_assume` or `may_type_bound` call site extracted from the LLVM IR.
///
/// Both calls are stripped from the visible-instruction list. The adapter
/// injects either `TransferEffect::Assume` or `TransferEffect::TypeBound`
/// onto the nearest CFG node, depending on `is_type_bound`.
///
/// Fields:
/// - `assumed_value`: the first argument — the `i1` condition.
/// - `predecessor`: the last visible instruction before the call in the same
///   basic block, if any. The adapter prefers to attach the effect here.
/// - `successor`: the first visible instruction after the call, used as a
///   fallback when there is no predecessor in the block.
/// - `source_location`: file/line/column from DWARF debug info.
/// - `is_type_bound`: true for `may_type_bound` calls (type-system facts that
///   narrow the forward reach but have no backward WP effect).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssumeSite {
    pub assumed_value: Instruction,
    pub predecessor: Option<Instruction>,
    pub successor: Option<Instruction>,
    pub source_location: SourceLocation,
    pub is_type_bound: bool,
}

/// The instruction-level control-flow graph for a single LLVM function.
///
/// This is the raw graph that the adapter (`adapter.rs`) further lowers into
/// the abstract CFG used by the backward analysis. It operates at instruction
/// granularity rather than basic-block granularity, which simplifies reasoning
/// about individual data-flow steps.
///
/// Key design choices:
/// - `may_assert` calls are **removed** from `vertices`/`edges` and recorded
///   separately in `asserts`. This prevents them from interfering with
///   control-flow edge construction while still capturing the obligation.
/// - "Noise" calls (e.g. `printf`) are also stripped from the graph; they
///   have no effect on the verification properties of interest.
/// - `vars` maps SSA names to their defining instructions, providing a fast
///   lookup used during formula construction.
/// - `pointer_param_indices` records which parameters have pointer type; the
///   adapter uses this to distinguish `ext_region` parameters from scalar ones.
#[derive(Clone, Debug)]
pub struct FunctionGraph {
    /// The function name as it appears in the LLVM IR (e.g. `"foo"`, `"bar"`).
    pub name: String,
    /// Display names of the formal parameters, in declaration order.
    pub params: Vec<String>,
    /// Indices into `params` that have pointer type; these become `ext_region`
    /// symbols in the lowered abstract CFG.
    pub pointer_param_indices: Vec<usize>,
    /// All visible instructions in program order (may_assert and noise calls
    /// excluded).
    pub vertices: Vec<Instruction>,
    /// Adjacency map: each visible instruction → its [`Node`] (predecessors
    /// and successors).
    pub edges: HashMap<Instruction, Node>,
    /// First visible instruction of the function entry block, i.e. the graph
    /// entry point.
    pub start: Option<Instruction>,
    /// All `ret` instructions in the function; these are the graph exit points.
    pub end: Vec<Instruction>,
    /// Maps SSA variable names (without `%`) to their defining instructions.
    /// Used by the adapter to resolve operand references during lowering.
    pub vars: HashMap<String, Instruction>,
    /// All `may_assert` call sites found in the function, in source order.
    pub asserts: Vec<AssertSite>,
    /// All `may_assume` call sites found in the function, in source order.
    pub assumes: Vec<AssumeSite>,
    /// The module's data-layout string, copied at graph-build time.
    /// Used by the adapter to construct a [`TargetData`] for accurate GEP
    /// offset calculation without needing to hold the LLVM `Module` reference.
    pub data_layout_str: String,
    /// Maps alloca `Instruction` → source variable name, derived from
    /// `#dbg_declare` records in the LLVM IR.  Used by the adapter to build
    /// the `debug_names` map on [`AdaptedProcedure`].  Empty when compiled
    /// without debug info (`-g`).
    pub debug_names: HashMap<Instruction, String>,
}

impl<'a> Labeller<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new(self.name.clone()).unwrap()
    }

    fn node_id(&'a self, node: &Instruction) -> dot::Id<'a> {
        let index = self
            .vertices
            .iter()
            .position(|candidate| candidate == node)
            .unwrap();
        dot::Id::new(format!("N{index}")).unwrap()
    }

    fn node_label(&'a self, node: &Instruction) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(node.print().into())
    }
}

impl<'a> dot::GraphWalk<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, Instruction> {
        Cow::Owned(self.vertices.clone())
    }

    fn edges(&'a self) -> dot::Edges<'a, (Instruction, Instruction)> {
        let mut edges = Vec::new();
        for (source, node) in &self.edges {
            for target in &node.successors {
                edges.push((*source, *target));
            }
        }
        Cow::Owned(edges)
    }

    fn source(&'a self, edge: &(Instruction, Instruction)) -> Instruction {
        edge.0
    }

    fn target(&'a self, edge: &(Instruction, Instruction)) -> Instruction {
        edge.1
    }
}

impl FunctionGraph {
    /// Build the instruction-level CFG for `function`.
    ///
    /// Returns `Err(ProgError::NoDefinitionForGraph)` for declaration-only
    /// functions (no basic blocks). All other errors are propagated up.
    ///
    /// Construction proceeds in two passes:
    ///
    /// 1. **Intra-block pass** — for each basic block, the full instruction
    ///    list is scanned to:
    ///    - record `may_assert` call sites in `asserts` (with their visible
    ///      predecessor/successor),
    ///    - compute the *visible* instruction list by filtering with
    ///      [`should_skip_instruction`],
    ///    - populate `vars` and `end`,
    ///    - call [`add_instruction`](FunctionGraph::add_instruction) for each
    ///      visible instruction.
    ///
    /// 2. **Inter-block pass** — for each block's visible list, consecutive
    ///    pairs are linked with [`add_edge`](FunctionGraph::add_edge), and the
    ///    block's visible terminator is linked to the first visible instruction
    ///    of each successor block.
    ///
    /// `start` is set to the first visible instruction of the entry block
    /// (the first basic block in LLVM's block list).
    pub fn new(function: Function, data_layout_str: String) -> Result<FunctionGraph> {
        if function.get_basic_block_count() == 0 {
            return Err(ProgError::NoDefinitionForGraph(function.get_name()));
        }

        let params = function.get_params();
        let mut graph = FunctionGraph {
            name: function.get_name(),
            params: params
                .iter()
                .into_iter()
                .map(|param| param.display_name())
                .collect(),
            pointer_param_indices: params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| {
                    matches!(
                        param.get_type().map(|ty| ty.kind()),
                        Some(TypeKind::Pointer)
                    )
                    .then_some(index)
                })
                .collect(),
            vertices: Vec::new(),
            edges: HashMap::new(),
            start: None,
            end: Vec::new(),
            vars: HashMap::new(),
            asserts: Vec::new(),
            assumes: Vec::new(),
            data_layout_str,
            debug_names: function.collect_alloca_debug_names(),
        };

        let basic_blocks = function.get_all_basic_blocks();
        let mut visible_by_block = HashMap::<BasicBlock, Vec<Instruction>>::new();

        for basic_block in &basic_blocks {
            let instructions = basic_block.get_all_instructions();
            if instructions.is_empty() {
                visible_by_block.insert(*basic_block, Vec::new());
                continue;
            }

            for (index, instruction) in instructions.iter().copied().enumerate() {
                if is_may_assert_call(instruction) {
                    let asserted_value = instruction
                        .get_call_args()
                        .into_iter()
                        .next()
                        .unwrap_or(instruction);
                    let source_location = instruction.get_debug_location().unwrap_or_default();
                    graph.asserts.push(AssertSite {
                        asserted_value,
                        predecessor: previous_visible_instruction(&instructions, index),
                        successor: next_visible_instruction(&instructions, index),
                        source_location,
                    });
                }
                if is_may_assume_call(instruction) || is_may_type_bound_call(instruction) {
                    let assumed_value = instruction
                        .get_call_args()
                        .into_iter()
                        .next()
                        .unwrap_or(instruction);
                    let source_location = instruction.get_debug_location().unwrap_or_default();
                    graph.assumes.push(AssumeSite {
                        assumed_value,
                        predecessor: previous_visible_instruction(&instructions, index),
                        successor: next_visible_instruction(&instructions, index),
                        source_location,
                        is_type_bound: is_may_type_bound_call(instruction),
                    });
                }
            }

            let visible = instructions
                .iter()
                .copied()
                .filter(|instruction| !should_skip_instruction(*instruction))
                .collect::<Vec<_>>();

            if graph.start.is_none() {
                graph.start = visible.first().copied();
            }

            for instruction in &visible {
                if let Some(name) = instruction.get_assignment_var() {
                    graph.vars.insert(name, *instruction);
                }
                if instruction.is_return_instruction() {
                    graph.end.push(*instruction);
                }
                graph.add_instruction(*instruction);
            }

            visible_by_block.insert(*basic_block, visible);
        }

        for visible in visible_by_block.values() {
            for pair in visible.windows(2) {
                graph.add_edge(pair[0], pair[1])?;
            }
        }

        for basic_block in &basic_blocks {
            let Some(visible) = visible_by_block.get(basic_block) else {
                continue;
            };
            let Some(terminator) = visible.last().copied() else {
                continue;
            };
            if !terminator.is_terminator_instruction() {
                continue;
            }
            for successor_block in terminator.get_successor_blocks() {
                let Some(successor_visible) = visible_by_block.get(&successor_block) else {
                    continue;
                };
                let Some(first) = successor_visible.first().copied() else {
                    continue;
                };
                graph.add_edge(terminator, first)?;
            }
        }

        Ok(graph)
    }

    /// Insert `instruction` into the graph as an isolated vertex (no edges).
    ///
    /// If `instruction` is already present the call is a no-op, preserving
    /// existing predecessor/successor sets. This idempotency means callers
    /// can unconditionally call `add_instruction` before `add_edge` without
    /// worrying about duplicate nodes.
    pub fn add_instruction(&mut self, instruction: Instruction) {
        if self.vertices.contains(&instruction) {
            return;
        }
        self.vertices.push(instruction);
        self.edges.insert(
            instruction,
            Node {
                predecessors: BTreeSet::new(),
                instr: instruction,
                successors: BTreeSet::new(),
            },
        );
    }

    /// Add a directed CFG edge `from → to`, inserting both endpoints as
    /// isolated vertices first if they are not already present.
    ///
    /// Updates both `from`'s successor set and `to`'s predecessor set
    /// atomically (both must succeed). Returns an error if either node is
    /// missing after insertion, which should only happen if the graph is in
    /// an inconsistent state.
    pub fn add_edge(&mut self, from: Instruction, to: Instruction) -> Result<()> {
        self.add_instruction(from);
        self.add_instruction(to);

        {
            let source = self.edges.get_mut(&from).ok_or_else(|| {
                ProgError::GraphError(from, "missing source while adding successor".to_string())
            })?;
            source.successors.insert(to);
        }
        {
            let target = self.edges.get_mut(&to).ok_or_else(|| {
                ProgError::GraphError(to, "missing target while adding predecessor".to_string())
            })?;
            target.predecessors.insert(from);
        }

        Ok(())
    }

    pub fn generate_dot_file(&self, dirpath: &str) -> Result<()> {
        if !std::path::Path::new(dirpath).exists() {
            fs::create_dir(dirpath)?;
        }
        let mut file =
            fs::File::create(std::path::PathBuf::from(dirpath).join(format!("{}.dot", self.name)))?;
        dot::render(self, &mut file)?;
        Ok(())
    }
}

/// Build instruction-level CFGs for all function definitions in `module`.
///
/// Declaration-only functions (no body) are silently skipped. Any other error
/// during graph construction is propagated immediately, aborting processing of
/// the remaining functions.
///
/// The returned vector contains one [`FunctionGraph`] per function definition,
/// in the order functions appear in the module.
pub fn generate_program_graph(module: &Module) -> Result<Vec<FunctionGraph>> {
    let mut graphs = Vec::new();
    let layout = module.get_data_layout_str();
    for function in module.get_all_functions() {
        match FunctionGraph::new(function, layout.clone()) {
            Ok(graph) => graphs.push(graph),
            Err(ProgError::NoDefinitionForGraph(_)) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(graphs)
}

pub fn dump_graphs(graphs: &[FunctionGraph], outdir: &str) {
    for graph in graphs {
        let _ = graph.generate_dot_file(outdir);
    }
}

/// Return `true` if `instruction` should be excluded from the visible-
/// instruction graph.
///
/// Instructions are skipped when they carry no semantic information relevant
/// to the assertion being verified:
/// - `may_assert` calls are handled separately via `AssertSite` recording.
/// - `may_assume` calls are handled separately via `AssumeSite` recording.
/// - "Noise" calls (currently `printf`, `putchar`) are I/O side-effects with
///   no effect on program state as modelled by the analysis.
///
/// **Invariant**: any instruction skipped here must not appear in `vertices`
/// or `edges`, but it MAY appear as a callee name in `asserts` or `assumes`.
fn should_skip_instruction(instruction: Instruction) -> bool {
    is_may_assert_call(instruction)
        || is_may_assume_call(instruction)
        || is_may_type_bound_call(instruction)
        || is_noise_call(instruction)
}

/// Return `true` if `instruction` is a direct call to `may_assert`.
///
/// `may_assert` is the sentinel function that marks assertion sites. Its
/// single argument is the `i1` condition that must hold. The call is stripped
/// from the CFG but recorded as an [`AssertSite`].
fn is_may_assert_call(instruction: Instruction) -> bool {
    instruction.get_called_function().as_deref() == Some("may_assert")
}

/// Return `true` if `instruction` is a direct call to `may_assume`.
fn is_may_assume_call(instruction: Instruction) -> bool {
    instruction.get_called_function().as_deref() == Some("may_assume")
}

/// Return `true` if `instruction` is a direct call to `may_type_bound`.
///
/// `may_type_bound` marks type-system facts (e.g. "unsigned int >= 0") that
/// always hold in well-typed programs.  Like `may_assume`, the call is stripped
/// from the visible CFG and recorded as an [`AssumeSite`] with `is_type_bound`
/// set to true.  The adapter injects a `TransferEffect::TypeBound` (WP =
/// identity, SP = `pre AND cond`) rather than a regular `Assume`.
fn is_may_type_bound_call(instruction: Instruction) -> bool {
    instruction.get_called_function().as_deref() == Some("may_type_bound")
}

fn is_noise_call(instruction: Instruction) -> bool {
    let Some(callee) = instruction.get_called_function() else {
        return false;
    };
    NOISE_CALLS.iter().any(|noise| *noise == callee)
}

/// Return the nearest visible instruction that precedes `instructions[index]`
/// within the same basic block.
///
/// Searches backwards from `index - 1`, skipping any instructions that
/// [`should_skip_instruction`] would filter out. Returns `None` if no visible
/// instruction exists before `index` in the block.
///
/// Used to populate `AssertSite::predecessor` so the backward analysis knows
/// the last real program point before an assertion.
fn previous_visible_instruction(instructions: &[Instruction], index: usize) -> Option<Instruction> {
    instructions[..index]
        .iter()
        .rev()
        .copied()
        .find(|instruction| !should_skip_instruction(*instruction))
}

/// Return the nearest visible instruction that follows `instructions[index]`
/// within the same basic block.
///
/// Searches forwards from `index + 1`, skipping any instructions that
/// [`should_skip_instruction`] would filter out. Returns `None` if no visible
/// instruction exists after `index` in the block.
///
/// Used to populate `AssertSite::successor` so the backward analysis can
/// resume propagation past the assertion site.
fn next_visible_instruction(instructions: &[Instruction], index: usize) -> Option<Instruction> {
    instructions[index + 1..]
        .iter()
        .copied()
        .find(|instruction| !should_skip_instruction(*instruction))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_graphs(ir: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
    }

    #[test]
    fn branch_terminator_successors_exist() {
        with_graphs(
            r#"
                define void @main(i1 %cond) {
                entry:
                    br i1 %cond, label %then, label %else
                then:
                    ret void
                else:
                    ret void
                }
            "#,
            |graphs| {
                let graph = &graphs[0];
                let branch = graph
                    .vertices
                    .iter()
                    .copied()
                    .find(|instruction| instruction.print().contains("br i1 %cond"))
                    .unwrap();
                let successors = &graph.edges.get(&branch).unwrap().successors;
                assert_eq!(successors.len(), 2);
            },
        );
    }

    #[test]
    fn may_assert_is_recorded_but_not_emitted_as_a_node() {
        with_graphs(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %cond) {
                entry:
                    call void @may_assert(i1 %cond)
                    ret void
                }
            "#,
            |graphs| {
                let graph = &graphs[0];
                assert_eq!(graph.asserts.len(), 1);
                assert!(graph
                    .vertices
                    .iter()
                    .all(|instruction| !instruction.print().contains("@may_assert")));
                assert_eq!(
                    graph.asserts[0].asserted_value.display_name(),
                    "%cond".to_string()
                );
            },
        );
    }

    #[test]
    fn may_assume_is_recorded_but_not_emitted_as_a_node() {
        with_graphs(
            r#"
                declare void @may_assume(i1)

                define void @main(i1 %cond) {
                entry:
                    call void @may_assume(i1 %cond)
                    ret void
                }
            "#,
            |graphs| {
                let graph = &graphs[0];
                assert_eq!(graph.assumes.len(), 1);
                assert!(graph
                    .vertices
                    .iter()
                    .all(|instruction| !instruction.print().contains("@may_assume")));
                assert_eq!(
                    graph.assumes[0].assumed_value.display_name(),
                    "%cond".to_string()
                );
            },
        );
    }

    #[test]
    fn declaration_only_modules_are_handled_cleanly() {
        with_graphs(
            r#"
                declare void @helper()

                define void @main() {
                entry:
                    ret void
                }
            "#,
            |graphs| {
                assert_eq!(graphs.len(), 1);
                assert_eq!(graphs[0].name, "main");
            },
        );
    }
}
