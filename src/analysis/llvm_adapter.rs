//! Lowering from LLVM instruction graphs into the paper-shaped CFG plus
//! normalized node/edge effects.
//!
//! `cfg.rs` owns only nodes, edges, and edge-local guards. This adapter is the
//! LLVM-specific place that turns instruction opcodes into `transfer.rs`
//! effects.

use crate::analysis::cfg::{Cfg, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, Sort, Term, Var};
use crate::analysis::transfer::{AssignValue, TransferEffect};
use crate::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode, TypeKind};
use crate::llvm_utils::program_graph::{AssertSite, FunctionGraph};
use std::collections::{BTreeMap, HashMap};
use thiserror::Error;

#[derive(Clone, Debug)]
pub struct AdaptedProcedure {
    pub cfg: Cfg,
    pub node_effects: BTreeMap<CfgNodeId, Vec<TransferEffect>>,
    pub edge_effects: BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
    pub instruction_nodes: HashMap<Instruction, CfgNodeId>,
}

impl AdaptedProcedure {
    pub fn node_for_instruction(&self, instruction: Instruction) -> Option<CfgNodeId> {
        self.instruction_nodes.get(&instruction).copied()
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum AdapterError {
    #[error("function graph has no visible start node")]
    MissingStart,
    #[error("unsupported memory-heavy instruction: {instruction}")]
    UnsupportedMemoryInstruction { instruction: String },
    #[error("unsupported floating-point instruction: {instruction}")]
    UnsupportedFloatingPointInstruction { instruction: String },
    #[error("unsupported instruction in current lowering: {instruction}")]
    UnsupportedInstruction { instruction: String },
    #[error("call results are not supported yet: {instruction}")]
    UnsupportedCallResult { instruction: String },
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
    let start = graph.start.ok_or(AdapterError::MissingStart)?;
    let mut cfg = Cfg::new(start.print());
    let mut instruction_nodes = HashMap::<Instruction, CfgNodeId>::new();
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
        let effects = lower_node_effects(*instruction)?;
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
    lower_assert_obligations(graph, &instruction_nodes, &mut node_effects)?;

    cfg.ensure_single_exit()
        .map_err(|error| AdapterError::Cfg(error.to_string()))?;

    Ok(AdaptedProcedure {
        cfg,
        node_effects,
        edge_effects,
        instruction_nodes,
    })
}

fn lower_node_effects(instruction: Instruction) -> Result<Vec<TransferEffect>, AdapterError> {
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
        InstructionOpcode::PHI | InstructionOpcode::Br | InstructionOpcode::Ret => None,
        InstructionOpcode::Call => {
            let callee = instruction.get_called_function().ok_or_else(|| {
                AdapterError::UnsupportedInstruction {
                    instruction: instruction.print(),
                }
            })?;
            if callee == "may_assert" {
                None
            } else {
                match instruction
                    .get_type()
                    .map(|ty| ty.kind())
                    .unwrap_or(TypeKind::Other)
                {
                    TypeKind::Void => Some(TransferEffect::Call { callee }),
                    _ => {
                        return Err(AdapterError::UnsupportedCallResult {
                            instruction: instruction.print(),
                        });
                    }
                }
            }
        }
        InstructionOpcode::Alloca
        | InstructionOpcode::Load
        | InstructionOpcode::Store
        | InstructionOpcode::GetElementPtr => {
            return Err(AdapterError::UnsupportedMemoryInstruction {
                instruction: instruction.print(),
            });
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
) -> Result<(), AdapterError> {
    for site in &graph.asserts {
        let node = choose_assert_node(site, instruction_nodes).ok_or(AdapterError::MissingStart)?;
        let obligation =
            TransferEffect::Obligation(Formula::not(lower_bool_value(site.asserted_value)?));
        node_effects.entry(node).or_default().push(obligation);
    }
    Ok(())
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

fn assigned_var(instruction: Instruction) -> Result<Var, AdapterError> {
    let sort = sort_for_value(instruction)?;
    let name = instruction.display_name();
    match sort {
        Sort::Bool => Ok(Var::bool(name)),
        Sort::Int => Ok(Var::int(name)),
        Sort::Real => Ok(Var::real(name)),
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
        TypeKind::Void => Err(AdapterError::UnsupportedValue {
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
    use crate::analysis::transfer::TransferEffect;
    use crate::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::llvm_utils::program_graph::generate_program_graph;

    fn adapt_first(ir: &str) -> AdaptedProcedure {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        adapt_function_graph(&graphs[0]).unwrap()
    }

    fn adapt_first_err(ir: &str) -> AdapterError {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        adapt_function_graph(&graphs[0]).unwrap_err()
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
    fn unsupported_memory_instructions_are_rejected() {
        let error = adapt_first_err(
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
        assert!(matches!(
            error,
            AdapterError::UnsupportedMemoryInstruction { .. }
        ));
    }
}
