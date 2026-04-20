//! LLVM-to-paper edge adapter (`Option A`).
//!
//! This module builds:
//!
//! - a paper-shaped `PaperProcedure`;
//! - an external `EdgeId -> LlvmEdgeMetadata` registry.
//!
//! Paper correspondence:
//!
//! ```text
//! LLVM function CFG            -> procedure P
//! LLVM instruction successor   -> edge e
//! adapted edge metadata        -> implementation detail for Gamma_e lookup
//! ```
//!
//! The paper modules (`cfg`, `rules`, `state`, `summaries`) remain LLVM-free.
//! LLVM details stay here and are consumed by `analysis::transfer`.
//! This file should not own SMT encoding or solver operations.

use crate::analysis::cfg::{EdgeKind, EdgeTransition, PaperEdge, PaperProcedure};
use crate::analysis::formula::Predicate;
use crate::analysis::vocabulary::{EdgeId, NodeId, ProcedureName};
use crate::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode};
use crate::llvm_utils::program_graph::FunctionGraph;
use log::debug;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdapterError {
    EmptyFunction {
        function: String,
    },
    MissingEntry {
        function: String,
    },
    MissingNode {
        function: String,
        instruction: String,
    },
}

impl fmt::Display for AdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AdapterError::EmptyFunction { function } => {
                write!(f, "cannot adapt empty function graph: {function}")
            }
            AdapterError::MissingEntry { function } => {
                write!(f, "function graph has no start instruction: {function}")
            }
            AdapterError::MissingNode {
                function,
                instruction,
            } => write!(
                f,
                "missing node mapping while adapting {function}: {instruction}"
            ),
        }
    }
}

impl std::error::Error for AdapterError {}

pub type AdapterResult<T> = std::result::Result<T, AdapterError>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmEdgeMetadata {
    pub edge_id: EdgeId,
    pub from: NodeId,
    pub to: NodeId,
    pub opcode: InstructionOpcode,
    pub instruction_text: String,
    pub assignment: Option<String>,
    pub called_function: Option<String>,
    pub operands: Vec<String>,
    pub branch_condition: Option<String>,
    pub successor_index: Option<usize>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LlvmEdgeRegistry {
    by_edge: HashMap<EdgeId, LlvmEdgeMetadata>,
}

impl LlvmEdgeRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, metadata: LlvmEdgeMetadata) -> Option<LlvmEdgeMetadata> {
        self.by_edge.insert(metadata.edge_id, metadata)
    }

    pub fn metadata(&self, edge_id: EdgeId) -> Option<&LlvmEdgeMetadata> {
        self.by_edge.get(&edge_id)
    }

    pub fn len(&self) -> usize {
        self.by_edge.len()
    }

    pub fn is_empty(&self) -> bool {
        self.by_edge.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &LlvmEdgeMetadata> {
        self.by_edge.values()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdaptedProcedure {
    pub procedure: PaperProcedure,
    pub registry: LlvmEdgeRegistry,
}

pub fn adapt_function_graph(graph: &FunctionGraph) -> AdapterResult<AdaptedProcedure> {
    if graph.vertices.is_empty() {
        return Err(AdapterError::EmptyFunction {
            function: graph.name.clone(),
        });
    }

    let node_ids = assign_node_ids(&graph.vertices);
    let entry_instr = graph.start.ok_or_else(|| AdapterError::MissingEntry {
        function: graph.name.clone(),
    })?;
    let exit_instr = graph
        .end
        .first()
        .copied()
        .or_else(|| graph.vertices.last().copied())
        .ok_or_else(|| AdapterError::EmptyFunction {
            function: graph.name.clone(),
        })?;
    let entry = node_id_for(&node_ids, entry_instr, graph)?;
    let exit = node_id_for(&node_ids, exit_instr, graph)?;

    let mut procedure = PaperProcedure::new(ProcedureName::new(graph.name.clone()), entry, exit);
    for node_id in node_ids.values().copied() {
        procedure.add_node(node_id);
    }

    let mut registry = LlvmEdgeRegistry::new();
    let mut next_edge = 0usize;

    for src in &graph.vertices {
        debug!(
            "Adapting instruction in {}: {}",
            graph.name,
            one_line_instruction(*src)
        );
        let Some(node) = graph.edges.get(src) else {
            continue;
        };

        let opcode = src.get_opcode();
        let successor_count = node.successors.len();
        let is_conditional_branch = opcode == InstructionOpcode::Br && successor_count == 2;
        let ordered_successors = if is_conditional_branch {
            Some(src.get_successors())
        } else {
            None
        };
        for dst in &node.successors {
            debug!(
                "Adapting edge candidate in {}: {} -> {}",
                graph.name,
                one_line_instruction(*src),
                one_line_instruction(*dst)
            );
            let edge_id = EdgeId(next_edge);
            let from = node_id_for(&node_ids, *src, graph)?;
            debug!("Resolved source node {} for edge {}", from, edge_id);
            let to = node_id_for(&node_ids, *dst, graph)?;
            debug!("Resolved target node {} for edge {}", to, edge_id);
            let successor_index = if is_conditional_branch {
                ordered_successors
                    .as_ref()
                    .and_then(|ordered| ordered.iter().position(|candidate| candidate == dst))
            } else {
                None
            };
            let edge_kind = classify_edge(opcode, successor_count, src, successor_index);

            let edge = PaperEdge {
                id: edge_id,
                from,
                to,
                gamma: gamma_atom(&graph.name, edge_id),
                transition: EdgeTransition {
                    kind: edge_kind,
                    post_under_approx: None,
                    pre_over_approx: None,
                },
            };
            procedure.add_edge(edge);

            let instruction_text = one_line_instruction(*src);
            let assignment = src.get_assignment_var().map(normalize_name);
            let called_function = src.get_called_function();
            let operands = src.get_operands().into_iter().map(display_value).collect();
            let branch_condition = if is_conditional_branch {
                src.get_branch_condition().map(display_value)
            } else {
                None
            };
            let metadata = LlvmEdgeMetadata {
                edge_id,
                from,
                to,
                opcode,
                instruction_text,
                assignment,
                called_function,
                operands,
                branch_condition,
                successor_index,
            };
            registry.insert(metadata);
            debug!("Adapted edge {} in {}", edge_id, graph.name);
            next_edge += 1;
        }
    }

    Ok(AdaptedProcedure {
        procedure,
        registry,
    })
}

fn assign_node_ids(vertices: &[Instruction]) -> HashMap<Instruction, NodeId> {
    vertices
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, instruction)| (instruction, NodeId(idx)))
        .collect()
}

fn node_id_for(
    ids: &HashMap<Instruction, NodeId>,
    instruction: Instruction,
    graph: &FunctionGraph,
) -> AdapterResult<NodeId> {
    ids.get(&instruction)
        .copied()
        .ok_or_else(|| AdapterError::MissingNode {
            function: graph.name.clone(),
            instruction: one_line_instruction(instruction),
        })
}

fn classify_edge(
    opcode: InstructionOpcode,
    successor_count: usize,
    src: &Instruction,
    successor_index: Option<usize>,
) -> EdgeKind {
    match opcode {
        InstructionOpcode::Br => {
            if successor_count == 2 {
                match successor_index {
                    Some(0) => EdgeKind::BranchTrue,
                    Some(1) => EdgeKind::BranchFalse,
                    _ => EdgeKind::Unknown("missing branch successor index".to_string()),
                }
            } else {
                EdgeKind::Local
            }
        }
        InstructionOpcode::Call => src
            .get_called_function()
            .map(|callee| EdgeKind::Call {
                callee: ProcedureName::new(callee),
            })
            .unwrap_or_else(|| EdgeKind::Unknown("indirect or unresolved call".to_string())),
        InstructionOpcode::Ret => EdgeKind::Return,
        _ => EdgeKind::Local,
    }
}

fn gamma_atom(function: &str, edge_id: EdgeId) -> Predicate {
    Predicate::atom(format!("Gamma({function}, {edge_id})"))
}

fn normalize_name(name: String) -> String {
    if name.starts_with('%') || name.starts_with('@') {
        name
    } else {
        format!("%{name}")
    }
}

fn display_value(value: Instruction) -> String {
    if let Some(constant) = value.as_constant_int() {
        constant.to_string()
    } else if let Some(name) = value.get_name().or_else(|| value.get_assignment_var()) {
        normalize_name(name)
    } else {
        one_line_instruction(value)
    }
}

fn one_line_instruction(instruction: Instruction) -> String {
    let text = instruction.print().replace('\n', " ");
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}
