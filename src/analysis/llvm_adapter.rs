//! Lowering from LLVM instruction graphs into the paper-shaped CFG plus
//! normalized node/edge effects.
//!
//! `cfg.rs` owns only nodes, edges, and edge-local guards. This adapter is the
//! LLVM-specific place that turns instruction opcodes into `transfer.rs`
//! effects.
//!
//! It is also where the current procedure interface is recovered for
//! interprocedural reasoning:
//!
//! - formal parameter names
//! - a distinguished scalar return slot
//! - call arguments and optional scalar return targets
//!
//! The driver relies on this interface metadata when it creates callee queries,
//! alpha-renames summary variables, and substitutes caller-side actuals back
//! into discovered summaries.

use crate::analysis::cfg::{Cfg, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, Sort, Term, Var};
use crate::analysis::transfer::{AssignValue, CallArgument, CallMemoryEffect, TransferEffect};
use crate::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode, TypeKind};
use crate::llvm_utils::program_graph::{AssertSite, FunctionGraph};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use thiserror::Error;

/// Scalar interface recovered for one lowered procedure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProcedureInterface {
    pub parameters: Vec<String>,
    pub return_value: Option<Var>,
}

/// One lowered procedure ready for the paper CFG/transfer pipeline.
#[derive(Clone, Debug)]
pub struct AdaptedProcedure {
    pub name: String,
    pub interface: ProcedureInterface,
    pub cfg: Cfg,
    pub node_effects: BTreeMap<CfgNodeId, Vec<TransferEffect>>,
    pub edge_effects: BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
    /// Lowered assertion sites keyed by the CFG node where the obligation is checked.
    pub assertions_by_node: BTreeMap<CfgNodeId, Vec<AdaptedAssertionSite>>,
    pub instruction_nodes: HashMap<Instruction, CfgNodeId>,
}

impl AdaptedProcedure {
    pub fn node_for_instruction(&self, instruction: Instruction) -> Option<CfgNodeId> {
        self.instruction_nodes.get(&instruction).copied()
    }
}

/// Assertion obligation attached to one lowered CFG node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdaptedAssertionSite {
    /// Stable 1-based identifier in the source graph assertion order.
    pub id: usize,
    /// Human-readable location used in CLI reports.
    pub location: String,
    /// Negated assertion formula checked at this node.
    pub obligation: Formula,
}

/// Adapter failures for the currently supported LLVM subset.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum AdapterError {
    #[error("function graph has no visible start node")]
    MissingStart,
    #[error("unsupported floating-point instruction: {instruction}")]
    UnsupportedFloatingPointInstruction { instruction: String },
    #[error("unsupported instruction in current lowering: {instruction}")]
    UnsupportedInstruction { instruction: String },
    #[error("missing assignment target for instruction: {instruction}")]
    MissingAssignmentTarget { instruction: String },
    #[error("unable to infer a supported sort for value: {value}")]
    UnsupportedValue { value: String },
    #[error("unable to match phi predecessor for instruction: {instruction}")]
    PhiPredecessorMismatch { instruction: String },
    #[error("CFG construction failed: {0}")]
    Cfg(String),
}

pub fn adapt_function_graph(graph: &FunctionGraph) -> Result<AdaptedProcedure, AdapterError> {
    adapt_function_graph_with_purity(graph, &BTreeSet::new())
}

pub fn adapt_function_graph_with_purity(
    graph: &FunctionGraph,
    memory_pure_functions: &BTreeSet<String>,
) -> Result<AdaptedProcedure, AdapterError> {
    let start = graph.start.ok_or(AdapterError::MissingStart)?;
    let mut cfg = Cfg::new(start.print());
    let mut instruction_nodes = HashMap::<Instruction, CfgNodeId>::new();
    let allocation_regions = allocation_regions(graph);
    let return_value = infer_return_value(graph)?;
    instruction_nodes.insert(start, cfg.entry());

    for instruction in &graph.vertices {
        if *instruction == start {
            continue;
        }
        let id = cfg.add_node(instruction.print());
        instruction_nodes.insert(*instruction, id);
    }

    for exit in &graph.end {
        let node = instruction_nodes[exit];
        cfg.mark_exit(node)
            .map_err(|error| AdapterError::Cfg(error.to_string()))?;
    }

    let mut node_effects = BTreeMap::<CfgNodeId, Vec<TransferEffect>>::new();
    for instruction in &graph.vertices {
        let effects = lower_node_effects(*instruction, memory_pure_functions, &allocation_regions)?;
        if !effects.is_empty() {
            node_effects.insert(instruction_nodes[instruction], effects);
        }
    }

    let mut edge_effects = BTreeMap::<CfgEdgeId, Vec<TransferEffect>>::new();
    let mut edge_ids = HashMap::<(Instruction, Instruction), CfgEdgeId>::new();
    for (source, node) in &graph.edges {
        for target in &node.successors {
            let relation = lower_edge_relation(*source, *target)?;
            let edge = cfg
                .add_edge(
                    instruction_nodes[source],
                    instruction_nodes[target],
                    relation,
                )
                .map_err(|error| AdapterError::Cfg(error.to_string()))?;
            edge_ids.insert((*source, *target), edge);
        }
    }

    lower_phi_edge_effects(graph, &edge_ids, &mut edge_effects)?;
    let assertions_by_node =
        lower_assert_obligations(graph, &instruction_nodes, &mut node_effects)?;

    cfg.ensure_single_exit()
        .map_err(|error| AdapterError::Cfg(error.to_string()))?;

    Ok(AdaptedProcedure {
        name: graph.name.clone(),
        interface: ProcedureInterface {
            parameters: graph.params.clone(),
            return_value,
        },
        cfg,
        node_effects,
        edge_effects,
        assertions_by_node,
        instruction_nodes,
    })
}

pub fn infer_memory_pure_functions(graphs: &[FunctionGraph]) -> BTreeSet<String> {
    let mut memory_pure = graphs
        .iter()
        .map(|graph| graph.name.clone())
        .collect::<BTreeSet<_>>();

    loop {
        let previous = memory_pure.clone();
        memory_pure.retain(|name| {
            let graph = graphs
                .iter()
                .find(|graph| graph.name == *name)
                .expect("graph should exist while computing memory purity");
            preserves_memory(graph, &previous)
        });
        if memory_pure == previous {
            return memory_pure;
        }
    }
}

fn lower_node_effects(
    instruction: Instruction,
    memory_pure_functions: &BTreeSet<String>,
    allocation_regions: &HashMap<Instruction, String>,
) -> Result<Vec<TransferEffect>, AdapterError> {
    let effect = match instruction.get_opcode() {
        InstructionOpcode::Add
        | InstructionOpcode::Sub
        | InstructionOpcode::Mul
        | InstructionOpcode::SDiv
        | InstructionOpcode::UDiv => {
            let target = assigned_var(instruction)?;
            let sort = sort_for_value(instruction)?;
            let lhs = lower_numeric_value(instruction.get_operand(0).unwrap())?;
            let rhs = lower_numeric_value(instruction.get_operand(1).unwrap())?;
            if sort != Sort::Int {
                return Err(AdapterError::UnsupportedValue {
                    value: instruction.print(),
                });
            }
            let value = match instruction.get_opcode() {
                InstructionOpcode::Add => Term::add(lhs, rhs),
                InstructionOpcode::Sub => Term::sub(lhs, rhs),
                InstructionOpcode::Mul => Term::mul(lhs, rhs),
                InstructionOpcode::SDiv | InstructionOpcode::UDiv => Term::div(lhs, rhs),
                _ => unreachable!(),
            };
            Some(TransferEffect::Assign {
                target,
                value: AssignValue::Term(value),
            })
        }
        InstructionOpcode::ICmp => {
            let target = assigned_var(instruction)?;
            let lhs = lower_numeric_value(instruction.get_operand(0).unwrap())?;
            let rhs = lower_numeric_value(instruction.get_operand(1).unwrap())?;
            let predicate = instruction.get_icmp_predicate().ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?;
            let value = match predicate {
                "==" => Formula::eq(lhs, rhs),
                "!=" => Formula::not(Formula::eq(lhs, rhs)),
                ">" => Formula::gt(lhs, rhs),
                ">=" => Formula::ge(lhs, rhs),
                "<" => Formula::lt(lhs, rhs),
                "<=" => Formula::le(lhs, rhs),
                _ => {
                    return Err(AdapterError::UnsupportedInstruction {
                        instruction: instruction.print(),
                    });
                }
            };
            Some(TransferEffect::Assign {
                target,
                value: AssignValue::Predicate(value),
            })
        }
        InstructionOpcode::And | InstructionOpcode::Or | InstructionOpcode::Xor => {
            let result_sort = sort_for_value(instruction)?;
            if result_sort != Sort::Bool {
                return Err(AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                });
            }
            let target = assigned_var(instruction)?;
            let lhs = lower_bool_value(instruction.get_operand(0).unwrap())?;
            let rhs = lower_bool_value(instruction.get_operand(1).unwrap())?;
            let value = match instruction.get_opcode() {
                InstructionOpcode::And => Formula::and(lhs, rhs),
                InstructionOpcode::Or => Formula::or(lhs, rhs),
                InstructionOpcode::Xor => Formula::or(
                    Formula::and(lhs.clone(), Formula::not(rhs.clone())),
                    Formula::and(Formula::not(lhs), rhs),
                ),
                _ => unreachable!(),
            };
            Some(TransferEffect::Assign {
                target,
                value: AssignValue::Predicate(value),
            })
        }
        InstructionOpcode::Alloca => Some(TransferEffect::Alloca {
            target: pointer_name(instruction)?,
            region: allocation_regions
                .get(&instruction)
                .cloned()
                .ok_or_else(|| AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                })?,
        }),
        InstructionOpcode::Load => Some(TransferEffect::Load {
            target: assigned_var(instruction)?,
            source: pointer_name(instruction.get_operand(0).ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?)?,
        }),
        InstructionOpcode::Store => Some(TransferEffect::Store {
            target: pointer_name(instruction.get_operand(1).ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?)?,
            value: lower_integer_value(instruction.get_operand(0).ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?)?,
        }),
        InstructionOpcode::GetElementPtr => Some(TransferEffect::GetElementPtr {
            target: pointer_name(instruction)?,
            base: pointer_name(instruction.get_operand(0).ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?)?,
            offset: lower_gep_offset(instruction)?,
        }),
        InstructionOpcode::PHI | InstructionOpcode::Br => None,
        InstructionOpcode::Ret => lower_return_effect(instruction)?,
        InstructionOpcode::Call => {
            let callee = instruction.get_called_function().ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?;
            if callee == "may_assert" {
                None
            } else {
                Some(TransferEffect::Call {
                    callee: callee.clone(),
                    arguments: lower_call_arguments(instruction)?,
                    return_target: lower_call_return_target(instruction)?,
                    memory_effect: if memory_pure_functions.contains(&callee) {
                        CallMemoryEffect::PreservesMemory
                    } else {
                        CallMemoryEffect::HavocMemory
                    },
                })
            }
        }
        InstructionOpcode::FNeg
        | InstructionOpcode::FAdd
        | InstructionOpcode::FSub
        | InstructionOpcode::FMul
        | InstructionOpcode::FDiv
        | InstructionOpcode::FRem
        | InstructionOpcode::FCmp => {
            return Err(AdapterError::UnsupportedFloatingPointInstruction {
                instruction: instruction.print(),
            });
        }
        _ => {
            return Err(AdapterError::UnsupportedInstruction {
                instruction: instruction.print(),
            });
        }
    };

    Ok(effect.into_iter().collect())
}

fn infer_return_value(graph: &FunctionGraph) -> Result<Option<Var>, AdapterError> {
    let mut return_sort = None;
    for instruction in &graph.end {
        let Some(value) = instruction.get_operand(0) else {
            continue;
        };
        let sort = sort_for_value(value)?;
        if return_sort.is_none() {
            return_sort = Some(sort);
        }
    }
    Ok(return_sort.map(return_var))
}

fn lower_return_effect(instruction: Instruction) -> Result<Option<TransferEffect>, AdapterError> {
    let Some(value) = instruction.get_operand(0) else {
        return Ok(None);
    };
    let sort = sort_for_value(value)?;
    let target = return_var(sort);
    let value = match sort {
        Sort::Bool => AssignValue::Predicate(lower_bool_value(value)?),
        Sort::Int | Sort::Real => AssignValue::Term(lower_numeric_value(value)?),
    };
    Ok(Some(TransferEffect::Assign { target, value }))
}

fn lower_call_arguments(instruction: Instruction) -> Result<Vec<CallArgument>, AdapterError> {
    let mut arguments = Vec::new();
    for argument in instruction.get_call_args() {
        if is_pointer_value(argument) {
            arguments.push(CallArgument::Pointer(pointer_name(argument)?));
            continue;
        }
        let sort = sort_for_value(argument)?;
        let lowered = match sort {
            Sort::Bool => CallArgument::Predicate(lower_bool_value(argument)?),
            Sort::Int | Sort::Real => CallArgument::Term(lower_numeric_value(argument)?),
        };
        arguments.push(lowered);
    }
    Ok(arguments)
}

fn lower_call_return_target(instruction: Instruction) -> Result<Option<Var>, AdapterError> {
    let Some(ty) = instruction.get_type() else {
        return Ok(None);
    };
    match ty.kind() {
        TypeKind::Void => Ok(None),
        TypeKind::Pointer => Ok(None),
        _ => Ok(Some(assigned_var(instruction)?)),
    }
}

fn allocation_regions(graph: &FunctionGraph) -> HashMap<Instruction, String> {
    let mut regions = HashMap::new();
    let mut next_region = 0usize;
    for instruction in &graph.vertices {
        if instruction.get_opcode() == InstructionOpcode::Alloca {
            regions.insert(*instruction, format!("{}$stack{}", graph.name, next_region));
            next_region += 1;
        }
    }
    regions
}

fn preserves_memory(graph: &FunctionGraph, memory_pure_functions: &BTreeSet<String>) -> bool {
    let local_pointers = infer_local_pointer_names(graph);
    for instruction in &graph.vertices {
        match instruction.get_opcode() {
            InstructionOpcode::Store => {
                let Some(pointer) = instruction.get_operand(1) else {
                    return false;
                };
                if !is_local_pointer_value(pointer, &local_pointers) {
                    return false;
                }
            }
            InstructionOpcode::Call => {
                let Some(callee) = instruction.get_called_function() else {
                    return false;
                };
                if !memory_pure_functions.contains(&callee) {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

fn infer_local_pointer_names(graph: &FunctionGraph) -> BTreeSet<String> {
    let mut locals = BTreeSet::new();
    loop {
        let mut changed = false;
        for instruction in &graph.vertices {
            match instruction.get_opcode() {
                InstructionOpcode::Alloca => {
                    changed |= locals.insert(instruction.display_name());
                }
                InstructionOpcode::GetElementPtr => {
                    if let Some(base) = instruction.get_operand(0) {
                        if is_local_pointer_value(base, &locals) {
                            changed |= locals.insert(instruction.display_name());
                        }
                    }
                }
                InstructionOpcode::PHI => {
                    if is_pointer_value(*instruction)
                        && instruction
                            .get_phi_incomings()
                            .iter()
                            .all(|(_, incoming)| is_local_pointer_value(*incoming, &locals))
                    {
                        changed |= locals.insert(instruction.display_name());
                    }
                }
                _ => {}
            }
        }
        if !changed {
            return locals;
        }
    }
}

fn is_local_pointer_value(value: Instruction, locals: &BTreeSet<String>) -> bool {
    is_pointer_value(value) && locals.contains(&value.display_name())
}

fn lower_edge_relation(source: Instruction, target: Instruction) -> Result<Formula, AdapterError> {
    match source.get_opcode() {
        InstructionOpcode::Br => {
            let Some(condition) = source.get_branch_condition() else {
                return Ok(Formula::True);
            };
            let target_block = target.get_parent_basic_block().ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: target.print(),
                }
            })?;
            let successors = source.get_successor_blocks();
            if successors.len() != 2 {
                return Ok(Formula::True);
            }
            if target_block == successors[0] {
                lower_bool_value(condition)
            } else if target_block == successors[1] {
                Ok(Formula::not(lower_bool_value(condition)?))
            } else {
                Err(AdapterError::UnsupportedInstruction {
                    instruction: source.print(),
                })
            }
        }
        InstructionOpcode::Switch | InstructionOpcode::IndirectBr | InstructionOpcode::Invoke => {
            Err(AdapterError::UnsupportedInstruction {
                instruction: source.print(),
            })
        }
        _ => Ok(Formula::True),
    }
}

fn lower_phi_edge_effects(
    graph: &FunctionGraph,
    edge_ids: &HashMap<(Instruction, Instruction), CfgEdgeId>,
    edge_effects: &mut BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
) -> Result<(), AdapterError> {
    for instruction in &graph.vertices {
        if instruction.get_opcode() != InstructionOpcode::PHI {
            continue;
        }
        let target = assigned_var(*instruction)?;
        let target_sort = sort_for_value(*instruction)?;
        for (incoming_block, incoming_value) in instruction.get_phi_incomings() {
            let matching_edge = edge_ids
                .iter()
                .find_map(|((source, target_instruction), edge)| {
                    if *target_instruction != *instruction {
                        return None;
                    }
                    let parent = source.get_parent_basic_block()?;
                    if parent == incoming_block {
                        Some(*edge)
                    } else {
                        None
                    }
                })
                .ok_or_else(|| AdapterError::PhiPredecessorMismatch {
                    instruction: instruction.print(),
                })?;
            let effect = match target_sort {
                Sort::Bool => TransferEffect::Assign {
                    target: target.clone(),
                    value: AssignValue::Predicate(lower_bool_value(incoming_value)?),
                },
                Sort::Int | Sort::Real => TransferEffect::Assign {
                    target: target.clone(),
                    value: AssignValue::Term(lower_numeric_value(incoming_value)?),
                },
            };
            edge_effects.entry(matching_edge).or_default().push(effect);
        }
    }
    Ok(())
}

fn lower_assert_obligations(
    graph: &FunctionGraph,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
    node_effects: &mut BTreeMap<CfgNodeId, Vec<TransferEffect>>,
) -> Result<BTreeMap<CfgNodeId, Vec<AdaptedAssertionSite>>, AdapterError> {
    let mut assertions_by_node = BTreeMap::<CfgNodeId, Vec<AdaptedAssertionSite>>::new();
    for (index, site) in graph.asserts.iter().enumerate() {
        let node = choose_assert_node(site, instruction_nodes).ok_or(AdapterError::MissingStart)?;
        let obligation = Formula::not(lower_bool_value(site.asserted_value)?);
        let location = assertion_location(site);
        let effect = TransferEffect::Obligation(obligation.clone());
        assertions_by_node
            .entry(node)
            .or_default()
            .push(AdaptedAssertionSite {
                id: index + 1,
                location,
                obligation: obligation.clone(),
            });
        node_effects.entry(node).or_default().push(effect);
    }
    Ok(assertions_by_node)
}

fn choose_assert_node(
    site: &AssertSite,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
) -> Option<CfgNodeId> {
    instruction_nodes
        .get(&site.asserted_value)
        .copied()
        .or_else(|| {
            site.predecessor
                .and_then(|instruction| instruction_nodes.get(&instruction).copied())
        })
        .or_else(|| {
            site.successor
                .and_then(|instruction| instruction_nodes.get(&instruction).copied())
        })
}

fn assertion_location(site: &AssertSite) -> String {
    if let Some(predecessor) = site.predecessor {
        format!("after {}", normalize_label(&predecessor.print()))
    } else if let Some(successor) = site.successor {
        format!("before {}", normalize_label(&successor.print()))
    } else {
        normalize_label(&site.asserted_value.print())
    }
}

fn assigned_var(instruction: Instruction) -> Result<Var, AdapterError> {
    let sort = sort_for_value(instruction)?;
    let name = instruction.display_name();
    match sort {
        Sort::Bool => Ok(Var::bool(name)),
        Sort::Int => Ok(Var::int(name)),
        Sort::Real => Ok(Var::real(name)),
    }
}

fn lower_integer_value(value: Instruction) -> Result<Term, AdapterError> {
    match sort_for_value(value)? {
        Sort::Int => lower_numeric_value(value),
        Sort::Real => Err(AdapterError::UnsupportedFloatingPointInstruction {
            instruction: value.print(),
        }),
        Sort::Bool => Err(AdapterError::UnsupportedInstruction {
            instruction: value.print(),
        }),
    }
}

fn lower_numeric_value(value: Instruction) -> Result<Term, AdapterError> {
    match sort_for_value(value)? {
        Sort::Int => {
            if let Some(constant) = value.as_constant_int() {
                Ok(Term::int(constant))
            } else {
                Ok(Term::var(value.display_name(), Sort::Int))
            }
        }
        Sort::Real => Err(AdapterError::UnsupportedFloatingPointInstruction {
            instruction: value.print(),
        }),
        Sort::Bool => Err(AdapterError::UnsupportedValue {
            value: value.print(),
        }),
    }
}

fn lower_gep_offset(instruction: Instruction) -> Result<Term, AdapterError> {
    // APPROX_HEAVY: the temporary memory model treats each region as an integer
    // array and lowers GEP by summing raw indices, ignoring LLVM element sizes
    // and aggregate layout.
    let mut offset = Term::int(0);
    for operand in instruction.get_operands().into_iter().skip(1) {
        let index = lower_integer_value(operand)?;
        offset = Term::add(offset, index);
    }
    Ok(offset)
}

fn pointer_name(value: Instruction) -> Result<String, AdapterError> {
    if is_pointer_value(value) {
        Ok(value.display_name())
    } else {
        Err(AdapterError::UnsupportedInstruction {
            instruction: value.print(),
        })
    }
}

fn return_var(sort: Sort) -> Var {
    match sort {
        Sort::Bool => Var::bool("__return"),
        Sort::Int => Var::int("__return"),
        Sort::Real => Var::real("__return"),
    }
}

fn is_pointer_value(value: Instruction) -> bool {
    value
        .get_type()
        .map(|ty| ty.kind() == TypeKind::Pointer)
        .unwrap_or(false)
}

fn normalize_label(label: &str) -> String {
    label.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn lower_bool_value(value: Instruction) -> Result<Formula, AdapterError> {
    match sort_for_value(value)? {
        Sort::Bool => {
            if let Some(constant) = value.as_constant_int() {
                Ok(if constant == 0 {
                    Formula::False
                } else {
                    Formula::True
                })
            } else {
                Ok(Formula::bool_var(value.display_name()))
            }
        }
        Sort::Int | Sort::Real => Err(AdapterError::UnsupportedValue {
            value: value.print(),
        }),
    }
}

fn sort_for_value(value: Instruction) -> Result<Sort, AdapterError> {
    let Some(ty) = value.get_type() else {
        return Err(AdapterError::UnsupportedValue {
            value: value.print(),
        });
    };
    match ty.kind() {
        TypeKind::Integer(1) => Ok(Sort::Bool),
        TypeKind::Integer(_) => Ok(Sort::Int),
        TypeKind::Half | TypeKind::Float | TypeKind::Double => {
            Err(AdapterError::UnsupportedFloatingPointInstruction {
                instruction: value.print(),
            })
        }
        TypeKind::Void | TypeKind::Pointer => Err(AdapterError::UnsupportedValue {
            value: value.print(),
        }),
        _ => Err(AdapterError::UnsupportedValue {
            value: value.print(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::cfg::CfgNodeKind;
    use crate::analysis::formula::{Formula, Term};
    use crate::analysis::transfer::{CallMemoryEffect, TransferEffect};
    use crate::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::llvm_utils::program_graph::generate_program_graph;

    fn adapt_first(ir: &str) -> AdaptedProcedure {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let pure = infer_memory_pure_functions(&graphs);
        adapt_function_graph_with_purity(&graphs[0], &pure).unwrap()
    }

    fn adapt_first_err(ir: &str) -> AdapterError {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        adapt_function_graph_with_purity(&graphs[0], &BTreeSet::new()).unwrap_err()
    }

    #[test]
    fn branch_guards_lower_to_cfg_edge_relations() {
        let adapted = adapt_first(
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
        );
        let relations = adapted
            .cfg
            .edges()
            .values()
            .map(|edge| edge.relation.clone())
            .collect::<Vec<_>>();
        assert!(relations.contains(&Formula::bool_var("%cond")));
        assert!(relations.contains(&Formula::not(Formula::bool_var("%cond"))));
    }

    #[test]
    fn phi_merges_lower_to_predecessor_specific_edge_effects() {
        let adapted = adapt_first(
            r#"
                define i32 @main(i1 %cond) {
                entry:
                    br i1 %cond, label %then, label %else
                then:
                    br label %merge
                else:
                    br label %merge
                merge:
                    %x = phi i32 [ 1, %then ], [ 2, %else ]
                    ret i32 %x
                }
            "#,
        );
        let effects = adapted
            .edge_effects
            .values()
            .flat_map(|effects| effects.iter())
            .cloned()
            .collect::<Vec<_>>();
        assert!(effects.contains(&TransferEffect::Assign {
            target: Var::int("%x"),
            value: AssignValue::Term(Term::int(1)),
        }));
        assert!(effects.contains(&TransferEffect::Assign {
            target: Var::int("%x"),
            value: AssignValue::Term(Term::int(2)),
        }));
    }

    #[test]
    fn may_assert_lowers_to_a_negated_obligation() {
        let adapted = adapt_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %cond) {
                entry:
                    call void @may_assert(i1 %cond)
                    ret void
                }
            "#,
        );
        let effects = adapted
            .node_effects
            .values()
            .flat_map(|effects| effects.iter())
            .cloned()
            .collect::<Vec<_>>();
        assert!(effects.contains(&TransferEffect::Obligation(Formula::not(
            Formula::bool_var("%cond")
        ))));
    }

    #[test]
    fn non_assert_calls_survive_as_normalized_call_effects() {
        let adapted = adapt_first(
            r#"
                declare void @helper()

                define void @main() {
                entry:
                    call void @helper()
                    ret void
                }
            "#,
        );
        let effects = adapted
            .node_effects
            .values()
            .flat_map(|effects| effects.iter())
            .cloned()
            .collect::<Vec<_>>();
        assert!(effects.contains(&TransferEffect::Call {
            callee: "helper".to_string(),
            arguments: Vec::new(),
            return_target: None,
            memory_effect: CallMemoryEffect::HavocMemory,
        }));
    }

    #[test]
    fn multiple_returns_yield_one_synthetic_exit() {
        let adapted = adapt_first(
            r#"
                define i32 @main(i1 %cond) {
                entry:
                    br i1 %cond, label %left, label %right
                left:
                    ret i32 1
                right:
                    ret i32 0
                }
            "#,
        );
        let exit = adapted.cfg.exit().unwrap();
        assert_eq!(
            adapted.cfg.node(exit).unwrap().kind,
            CfgNodeKind::SyntheticExit
        );
        assert_eq!(adapted.cfg.incoming_edges(exit).unwrap().len(), 2);
    }

    #[test]
    fn memory_instructions_lower_to_explicit_effects() {
        let adapted = adapt_first(
            r#"
                define i32 @main() {
                entry:
                    %ptr = alloca i32
                    store i32 1, ptr %ptr
                    %value = load i32, ptr %ptr
                    ret i32 %value
                }
            "#,
        );
        let effects = adapted
            .node_effects
            .values()
            .flat_map(|effects| effects.iter())
            .cloned()
            .collect::<Vec<_>>();
        assert!(effects.contains(&TransferEffect::Alloca {
            target: "%ptr".to_string(),
            region: "main$stack0".to_string(),
        }));
        assert!(effects.contains(&TransferEffect::Store {
            target: "%ptr".to_string(),
            value: Term::int(1),
        }));
        assert!(effects.contains(&TransferEffect::Load {
            target: Var::int("%value"),
            source: "%ptr".to_string(),
        }));
    }

    #[test]
    fn local_stack_memory_keeps_a_helper_memory_pure() {
        initialize_target();
        let context = Context::new();
        let module = context
            .parse_ir_str(
                r#"
                    define void @helper() {
                    entry:
                        %ptr = alloca i32
                        store i32 1, ptr %ptr
                        %v = load i32, ptr %ptr
                        ret void
                    }

                    define void @main() {
                    entry:
                        call void @helper()
                        ret void
                    }
                "#,
                "test",
            )
            .unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let pure = infer_memory_pure_functions(&graphs);
        assert!(pure.contains("helper"));
        assert!(pure.contains("main"));
    }

    #[test]
    fn stores_through_parameters_make_a_helper_impure() {
        initialize_target();
        let context = Context::new();
        let module = context
            .parse_ir_str(
                r#"
                    define void @touch(ptr %p) {
                    entry:
                        store i32 1, ptr %p
                        ret void
                    }
                "#,
                "test",
            )
            .unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let pure = infer_memory_pure_functions(&graphs);
        assert!(!pure.contains("touch"));
    }

    #[test]
    fn pointer_phis_are_still_rejected() {
        let error = adapt_first_err(
            r#"
                define ptr @main(i1 %cond, ptr %left, ptr %right) {
                entry:
                    br i1 %cond, label %lhs, label %rhs
                lhs:
                    br label %merge
                rhs:
                    br label %merge
                merge:
                    %p = phi ptr [ %left, %lhs ], [ %right, %rhs ]
                    ret ptr %p
                }
            "#,
        );
        assert!(matches!(error, AdapterError::UnsupportedValue { .. }));
    }
}
