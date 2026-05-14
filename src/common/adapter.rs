#![allow(dead_code)]

use crate::common::abstract_cfg::{
    AbstractCfg, AssignValue, CallMemoryEffect, CfgEdgeId, CfgNodeId, PointerEnv, SourceLocation,
    TransferEffect, TransferFn,
};
use crate::common::formula::{Formula, Rational, Sort, Term, Var};
use crate::common::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode, TypeKind};
use crate::common::llvm_utils::program_graph::FunctionGraph;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug)]
pub struct AdaptedProcedure {
    pub name: String,
    pub cfg: AbstractCfg,
    pub assertions: Vec<AssertionSite>,
    pub instruction_nodes: HashMap<Instruction, CfgNodeId>,
}

#[derive(Clone, Debug)]
pub struct AssertionSite {
    pub id: usize,
    pub node: CfgNodeId,
    pub source_location: SourceLocation,
    pub location: String,
    pub obligation: Formula,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WriteEffectSummary {
    pub param_index: usize,
    pub ext_region_name: String,
    pub obs_name: String,
    pub relation: Formula,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReturnSummary {
    pub function: String,
    pub formal_parameters: Vec<String>,
    pub retval_name: String,
    pub relation: Formula,
    pub write_effects: Vec<WriteEffectSummary>,
}

#[derive(Clone, Debug, Default)]
pub struct CallSummaryRegistry {
    summaries: BTreeMap<String, ReturnSummary>,
    next_call_site: Cell<usize>,
}

impl CallSummaryRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, summary: ReturnSummary) {
        self.summaries.insert(summary.function.clone(), summary);
    }

    pub fn get(&self, callee: &str) -> Option<&ReturnSummary> {
        self.summaries.get(callee)
    }

    pub fn summaries(&self) -> &BTreeMap<String, ReturnSummary> {
        &self.summaries
    }

    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    pub fn next_call_site_id(&self) -> usize {
        let id = self.next_call_site.get();
        self.next_call_site.set(id + 1);
        id
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AdapterError {
    #[error("function graph missing start instruction")]
    MissingStart,
    #[error("function graph missing exit instruction")]
    MissingExit,
    #[error("unsupported floating-point instruction: {0}")]
    UnsupportedFloatingPointInstruction(String),
    #[error("unsupported instruction: {0}")]
    UnsupportedInstruction(String),
    #[error("unsupported value: {0}")]
    UnsupportedValue(String),
    #[error("PHI predecessor mismatch: {0}")]
    PhiPredecessorMismatch(String),
    #[error("CFG error: {0}")]
    Cfg(String),
}

pub fn adapt(graph: &FunctionGraph) -> Result<AdaptedProcedure, AdapterError> {
    adapt_with_purity(graph, &BTreeSet::new())
}

pub fn adapt_with_purity(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
) -> Result<AdaptedProcedure, AdapterError> {
    adapt_with_purity_and_summaries(graph, memory_pure, &CallSummaryRegistry::new())
}

pub fn adapt_with_purity_and_summaries(
    graph: &FunctionGraph,
    memory_pure: &BTreeSet<String>,
    summaries: &CallSummaryRegistry,
) -> Result<AdaptedProcedure, AdapterError> {
    let function_name = &graph.name;
    let start = graph.start.ok_or(AdapterError::MissingStart)?;

    let mut allocation_regions = HashMap::<Instruction, String>::new();
    let mut stack_index = 0usize;
    for instruction in &graph.vertices {
        if instruction.get_opcode() == InstructionOpcode::Alloca {
            allocation_regions.insert(*instruction, format!("{function_name}$stack{stack_index}"));
            stack_index += 1;
        }
    }

    let mut cfg = AbstractCfg::new(start.print());
    cfg.set_entry_transfer(lower_node_transfer(
        function_name,
        start,
        memory_pure,
        &allocation_regions,
        summaries,
    )?);
    let mut instruction_nodes = HashMap::new();
    instruction_nodes.insert(start, cfg.entry());

    for instruction in &graph.vertices {
        if *instruction == start {
            continue;
        }
        let transfer = lower_node_transfer(
            function_name,
            *instruction,
            memory_pure,
            &allocation_regions,
            summaries,
        )?;
        let node_id = cfg.add_node(instruction.print(), transfer);
        instruction_nodes.insert(*instruction, node_id);
    }

    for exit in &graph.end {
        if let Some(node) = instruction_nodes.get(exit).copied() {
            cfg.mark_exit(node)
                .map_err(|error| AdapterError::Cfg(error.to_string()))?;
        }
    }

    let mut edge_ids = HashMap::<(Instruction, Instruction), CfgEdgeId>::new();
    for (source, node) in &graph.edges {
        for target in &node.successors {
            let source_node = *instruction_nodes
                .get(source)
                .ok_or(AdapterError::MissingStart)?;
            let target_node = *instruction_nodes
                .get(target)
                .ok_or(AdapterError::MissingStart)?;
            let guard = lower_edge_guard(function_name, *source, *target)?;
            let edge_id = cfg
                .add_edge(source_node, target_node, guard, vec![])
                .map_err(|error| AdapterError::Cfg(error.to_string()))?;
            edge_ids.insert((*source, *target), edge_id);
        }
    }

    lower_phi_edge_effects(
        function_name,
        graph,
        &mut cfg,
        &instruction_nodes,
        &edge_ids,
    )?;
    let assertions = lower_assertions(function_name, graph, &mut cfg, &instruction_nodes)?;
    cfg.ensure_single_exit()
        .map_err(|error| AdapterError::Cfg(error.to_string()))?;
    resolve_memory_effects(&mut cfg);

    Ok(AdaptedProcedure {
        name: graph.name.clone(),
        cfg,
        assertions,
        instruction_nodes,
    })
}

pub fn infer_memory_pure_functions(graphs: &[FunctionGraph]) -> BTreeSet<String> {
    let mut impure = BTreeSet::<String>::new();
    for graph in graphs {
        for instruction in &graph.vertices {
            if matches!(instruction.get_opcode(), InstructionOpcode::Store) {
                impure.insert(graph.name.clone());
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for graph in graphs {
            if impure.contains(&graph.name) {
                continue;
            }
            let mut local_impure = false;
            for instruction in &graph.vertices {
                if instruction.get_opcode() != InstructionOpcode::Call {
                    continue;
                }
                if let Some(callee) = instruction.get_called_function() {
                    if callee == "may_assert" {
                        continue;
                    }
                    if impure.contains(&callee) {
                        local_impure = true;
                        break;
                    }
                }
            }
            if local_impure {
                impure.insert(graph.name.clone());
                changed = true;
            }
        }
    }

    graphs
        .iter()
        .map(|graph| graph.name.clone())
        .filter(|name| !impure.contains(name))
        .collect()
}

pub fn collect_callee_names(graphs: &[FunctionGraph]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for graph in graphs {
        for instruction in &graph.vertices {
            if instruction.get_opcode() != InstructionOpcode::Call {
                continue;
            }
            if let Some(callee) = instruction.get_called_function() {
                if callee != "may_assert" {
                    names.insert(callee);
                }
            }
        }
    }
    names
}

pub fn compute_return_summary(
    graph: &FunctionGraph,
    procedure: &AdaptedProcedure,
) -> Option<ReturnSummary> {
    let order = procedure.cfg.topological_order()?;
    let exit = procedure.cfg.exit()?;
    let retval_name = synthetic_retval_name(&procedure.name);
    let retval_obs_name = format!("{retval_name}$obs");

    let mut state = procedure
        .cfg
        .node_ids()
        .map(|id| (id, Formula::False))
        .collect::<BTreeMap<_, _>>();

    let post_at_exit = Formula::eq(
        Term::Var(Var::int(retval_name.clone())),
        Term::Var(Var::int(retval_obs_name.clone())),
    );
    let seeded = procedure.cfg.node(exit).ok()?.transfer.wp(&post_at_exit);
    state.insert(exit, seeded);

    for node in order.iter().rev() {
        for edge_id in procedure.cfg.incoming_edges(*node) {
            let edge = procedure.cfg.edge(edge_id).ok()?;
            let target_state = state.get(&edge.target).cloned().unwrap_or(Formula::False);
            let edge_pre = edge.transfer().wp(&target_state);
            let post_at_source = Formula::and(edge.guard.clone(), edge_pre);
            let pre_at_source = procedure
                .cfg
                .node(edge.source)
                .ok()?
                .transfer
                .wp(&post_at_source);
            let previous = state.get(&edge.source).cloned().unwrap_or(Formula::False);
            state.insert(edge.source, Formula::or(previous, pre_at_source));
        }
    }

    let entry_state = state
        .get(&procedure.cfg.entry())
        .cloned()
        .unwrap_or(Formula::False);
    let relation = rename_vars_in_formula(&entry_state, |name| {
        if name == retval_obs_name {
            retval_name.clone()
        } else {
            name.to_string()
        }
    });

    if !formula_contains_var(&relation, &retval_name) {
        return None;
    }

    Some(ReturnSummary {
        function: procedure.name.clone(),
        formal_parameters: formal_parameter_names(graph, &procedure.name),
        retval_name,
        relation,
        write_effects: Vec::new(),
    })
}

fn formal_parameter_names(graph: &FunctionGraph, function_name: &str) -> Vec<String> {
    graph
        .params
        .iter()
        .map(|parameter| format!("{function_name}${parameter}"))
        .collect()
}

pub fn local_name(function_name: &str, instruction: Instruction) -> String {
    format!("{function_name}${}", instruction.display_name())
}

pub fn synthetic_retval_name(function_name: &str) -> String {
    format!("{function_name}$__retval")
}

pub fn ext_region_name(function_name: &str, index: usize) -> String {
    format!("{function_name}$__ext_{index}")
}

pub fn ext_obs_name(function_name: &str, index: usize) -> String {
    format!("{function_name}$__ext_{index}_obs")
}

fn assigned_var(function_name: &str, instruction: Instruction) -> Result<Var, AdapterError> {
    let name = local_name(function_name, instruction);
    let sort = sort_of_instruction_value(instruction)?;
    Ok(Var::new(name, sort))
}

fn sort_of_instruction_value(instruction: Instruction) -> Result<Sort, AdapterError> {
    let Some(ty) = instruction.get_type() else {
        return Err(AdapterError::UnsupportedValue(instruction.print()));
    };
    match ty.kind() {
        TypeKind::Integer(width) if width == 1 => Ok(Sort::Bool),
        TypeKind::Integer(_) | TypeKind::Pointer => Ok(Sort::Int),
        TypeKind::Half | TypeKind::Float | TypeKind::Double => Ok(Sort::Real),
        _ => Err(AdapterError::UnsupportedValue(instruction.print())),
    }
}

fn lower_numeric_value(function_name: &str, value: Instruction) -> Result<Term, AdapterError> {
    if let Some(constant) = value.as_constant_int() {
        return Ok(Term::int(constant));
    }
    if let Some(constant) = value.as_constant_real() {
        if constant.is_finite() {
            let scaled = (constant * 1_000_000.0).round() as i64;
            return Ok(Term::real(Rational::new(scaled, 1_000_000)));
        }
    }
    match sort_of_instruction_value(value)? {
        Sort::Int => Ok(Term::Var(Var::int(local_name(function_name, value)))),
        Sort::Real => Ok(Term::Var(Var::real(local_name(function_name, value)))),
        Sort::Bool => Err(AdapterError::UnsupportedValue(value.print())),
    }
}

fn lower_integer_value(function_name: &str, value: Instruction) -> Result<Term, AdapterError> {
    if let Some(constant) = value.as_constant_int() {
        return Ok(Term::int(constant));
    }
    match sort_of_instruction_value(value)? {
        Sort::Int => Ok(Term::Var(Var::int(local_name(function_name, value)))),
        sort => Err(AdapterError::UnsupportedValue(format!(
            "expected integer value, found {sort}: {}",
            value.print()
        ))),
    }
}

fn lower_bool_value(function_name: &str, value: Instruction) -> Result<Formula, AdapterError> {
    if let Some(constant) = value.as_constant_int() {
        return Ok(if constant == 0 {
            Formula::False
        } else {
            Formula::True
        });
    }
    match sort_of_instruction_value(value)? {
        Sort::Bool => Ok(Formula::Var(Var::bool(local_name(function_name, value)))),
        _ => Err(AdapterError::UnsupportedValue(value.print())),
    }
}

fn pointer_name(function_name: &str, value: Instruction) -> String {
    local_name(function_name, value)
}

fn lower_gep_offset(function_name: &str, instruction: Instruction) -> Result<Term, AdapterError> {
    let mut offset = Term::int(0);
    for operand in instruction.get_operands().into_iter().skip(1) {
        let term = lower_integer_value(function_name, operand)?;
        offset = Term::add(offset, term);
    }
    Ok(offset)
}

fn lower_node_transfer(
    function_name: &str,
    instruction: Instruction,
    memory_pure: &BTreeSet<String>,
    allocation_regions: &HashMap<Instruction, String>,
    summaries: &CallSummaryRegistry,
) -> Result<TransferFn, AdapterError> {
    let mut effects = Vec::<TransferEffect>::new();

    match instruction.get_opcode() {
        InstructionOpcode::Add
        | InstructionOpcode::Sub
        | InstructionOpcode::Mul
        | InstructionOpcode::SDiv
        | InstructionOpcode::UDiv
        | InstructionOpcode::FAdd
        | InstructionOpcode::FSub
        | InstructionOpcode::FMul
        | InstructionOpcode::FDiv => {
            let target = assigned_var(function_name, instruction)?;
            let lhs = lower_numeric_value(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let rhs = lower_numeric_value(
                function_name,
                instruction
                    .get_operand(1)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let term = match instruction.get_opcode() {
                InstructionOpcode::Add | InstructionOpcode::FAdd => Term::add(lhs, rhs),
                InstructionOpcode::Sub | InstructionOpcode::FSub => Term::sub(lhs, rhs),
                InstructionOpcode::Mul | InstructionOpcode::FMul => Term::mul(lhs, rhs),
                InstructionOpcode::SDiv | InstructionOpcode::UDiv | InstructionOpcode::FDiv => {
                    Term::div(lhs, rhs)
                }
                _ => unreachable!(),
            };
            effects.push(TransferEffect::Assign {
                target,
                value: AssignValue::Term(term),
            });
        }
        InstructionOpcode::ICmp | InstructionOpcode::FCmp => {
            let target = assigned_var(function_name, instruction)?;
            let lhs = lower_numeric_value(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let rhs = lower_numeric_value(
                function_name,
                instruction
                    .get_operand(1)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let predicate_name = if instruction.get_opcode() == InstructionOpcode::ICmp {
                instruction
                    .get_icmp_predicate()
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?
            } else {
                instruction
                    .get_fcmp_predicate()
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?
            };
            let predicate = match predicate_name {
                "==" => Formula::eq(lhs, rhs),
                "!=" => Formula::not(Formula::eq(lhs, rhs)),
                ">" => Formula::gt(lhs, rhs),
                ">=" => Formula::ge(lhs, rhs),
                "<" => Formula::lt(lhs, rhs),
                "<=" => Formula::le(lhs, rhs),
                _ => return Err(AdapterError::UnsupportedInstruction(instruction.print())),
            };
            effects.push(TransferEffect::Assign {
                target,
                value: AssignValue::Predicate(predicate),
            });
        }
        InstructionOpcode::And | InstructionOpcode::Or | InstructionOpcode::Xor => {
            let target = assigned_var(function_name, instruction)?;
            let lhs = lower_bool_value(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let rhs = lower_bool_value(
                function_name,
                instruction
                    .get_operand(1)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            let predicate = match instruction.get_opcode() {
                InstructionOpcode::And => Formula::and(lhs, rhs),
                InstructionOpcode::Or => Formula::or(lhs, rhs),
                InstructionOpcode::Xor => Formula::or(
                    Formula::and(lhs.clone(), Formula::not(rhs.clone())),
                    Formula::and(Formula::not(lhs), rhs),
                ),
                _ => unreachable!(),
            };
            effects.push(TransferEffect::Assign {
                target,
                value: AssignValue::Predicate(predicate),
            });
        }
        InstructionOpcode::SExt | InstructionOpcode::ZExt | InstructionOpcode::Trunc => {
            let target = assigned_var(function_name, instruction)?;
            let source = instruction
                .get_operand(0)
                .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?;
            let value = match sort_of_instruction_value(source)? {
                Sort::Bool => {
                    AssignValue::Term(Term::bool_to_int(lower_bool_value(function_name, source)?))
                }
                Sort::Int | Sort::Real => {
                    AssignValue::Term(lower_numeric_value(function_name, source)?)
                }
            };
            effects.push(TransferEffect::Assign { target, value });
        }
        InstructionOpcode::Alloca => {
            let target = pointer_name(function_name, instruction);
            let region = allocation_regions
                .get(&instruction)
                .cloned()
                .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?;
            effects.push(TransferEffect::Alloca { target, region });
        }
        InstructionOpcode::Load => {
            let source = pointer_name(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            );
            if matches!(
                instruction.get_type().map(|ty| ty.kind()),
                Some(TypeKind::Pointer)
            ) {
                effects.push(TransferEffect::PointerLoad {
                    target_ptr: pointer_name(function_name, instruction),
                    source_slot: source,
                });
            } else {
                let target = assigned_var(function_name, instruction)?;
                effects.push(TransferEffect::Load { target, source });
            }
        }
        InstructionOpcode::Store => {
            let target = pointer_name(
                function_name,
                instruction
                    .get_operand(1)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            );
            let stored = instruction
                .get_operand(0)
                .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?;
            if matches!(
                stored.get_type().map(|ty| ty.kind()),
                Some(TypeKind::Pointer)
            ) {
                effects.push(TransferEffect::PointerStore {
                    target_slot: target,
                    value_ptr: pointer_name(function_name, stored),
                });
            } else {
                let value = lower_numeric_value(function_name, stored)?;
                effects.push(TransferEffect::Store { target, value });
            }
        }
        InstructionOpcode::GetElementPtr => {
            let target = pointer_name(function_name, instruction);
            let base = pointer_name(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            );
            let offset = lower_gep_offset(function_name, instruction)?;
            effects.push(TransferEffect::GetElementPtr {
                target,
                base,
                offset,
            });
        }
        InstructionOpcode::PHI | InstructionOpcode::Br => {}
        InstructionOpcode::Ret => {
            if let Some(ret_value) = instruction.get_operand(0) {
                if sort_of_instruction_value(ret_value)? == Sort::Int {
                    effects.push(TransferEffect::Assign {
                        target: Var::int(synthetic_retval_name(function_name)),
                        value: AssignValue::Term(lower_numeric_value(function_name, ret_value)?),
                    });
                }
            }
        }
        InstructionOpcode::Call => {
            let callee = instruction
                .get_called_function()
                .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?;
            if callee != "may_assert" {
                let memory_effect = if memory_pure.contains(&callee) {
                    CallMemoryEffect::PreservesMemory
                } else {
                    CallMemoryEffect::HavocMemory
                };
                effects.push(TransferEffect::Call {
                    callee: callee.clone(),
                    memory_effect,
                });
                if let Some(obligation) =
                    summary_assume_for_call(function_name, instruction, &callee, summaries)?
                {
                    effects.push(obligation);
                }
            }
        }
        InstructionOpcode::FNeg => {
            let target = assigned_var(function_name, instruction)?;
            let source = lower_numeric_value(
                function_name,
                instruction
                    .get_operand(0)
                    .ok_or_else(|| AdapterError::UnsupportedInstruction(instruction.print()))?,
            )?;
            effects.push(TransferEffect::Assign {
                target,
                value: AssignValue::Term(Term::neg(source)),
            });
        }
        InstructionOpcode::FRem => {
            return Err(AdapterError::UnsupportedFloatingPointInstruction(
                instruction.print(),
            ));
        }
        InstructionOpcode::FPExt
        | InstructionOpcode::FPTrunc
        | InstructionOpcode::SIToFP
        | InstructionOpcode::UIToFP
        | InstructionOpcode::FPToSI
        | InstructionOpcode::FPToUI
        | InstructionOpcode::BitCast
        | InstructionOpcode::AddrSpaceCast => {}
        InstructionOpcode::Switch | InstructionOpcode::IndirectBr => {}
        InstructionOpcode::Invoke => {
            return Err(AdapterError::UnsupportedInstruction(instruction.print()));
        }
        _ => {
            let printed = instruction.print();
            if printed.trim_start().starts_with("br ") {
                // Some toolchains can surface branch opcodes through generic/unknown variants.
                // Branch transfer is encoded via edge guards, so node-local effects stay empty.
            } else {
                return Err(AdapterError::UnsupportedInstruction(printed));
            }
        }
    }

    Ok(TransferFn::new(effects))
}

fn lower_edge_guard(
    function_name: &str,
    source: Instruction,
    target: Instruction,
) -> Result<Formula, AdapterError> {
    if source.is_branch_instruction() {
        if let Some(condition) = source.get_branch_condition() {
            let successors = source.get_successor_blocks();
            if successors.len() == 1 {
                return Ok(Formula::True);
            }
            if successors.len() != 2 {
                return Err(AdapterError::UnsupportedInstruction(source.print()));
            }
            let target_block = target
                .get_parent_basic_block()
                .ok_or_else(|| AdapterError::UnsupportedInstruction(target.print()))?;
            let predicate = lower_bool_value(function_name, condition)?;
            if successors[0] == target_block {
                Ok(predicate)
            } else if successors[1] == target_block {
                Ok(Formula::not(predicate))
            } else {
                Err(AdapterError::UnsupportedInstruction(source.print()))
            }
        } else {
            Ok(Formula::True)
        }
    } else {
        match source.get_opcode() {
            InstructionOpcode::Switch | InstructionOpcode::IndirectBr => Ok(Formula::True),
            InstructionOpcode::Invoke => Err(AdapterError::UnsupportedInstruction(source.print())),
            _ => Ok(Formula::True),
        }
    }
}

fn lower_phi_edge_effects(
    function_name: &str,
    graph: &FunctionGraph,
    cfg: &mut AbstractCfg,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
    edge_ids: &HashMap<(Instruction, Instruction), CfgEdgeId>,
) -> Result<(), AdapterError> {
    for instruction in &graph.vertices {
        if instruction.get_opcode() != InstructionOpcode::PHI {
            continue;
        }
        let target = assigned_var(function_name, *instruction)?;
        for (incoming_block, incoming_value) in instruction.get_phi_incomings() {
            let source = graph
                .vertices
                .iter()
                .copied()
                .find(|candidate| {
                    candidate
                        .get_parent_basic_block()
                        .map(|block| block == incoming_block)
                        .unwrap_or(false)
                        && graph
                            .edges
                            .get(candidate)
                            .map(|node| node.successors.contains(instruction))
                            .unwrap_or(false)
                })
                .ok_or_else(|| {
                    AdapterError::PhiPredecessorMismatch(format!(
                        "could not match PHI incoming for {}",
                        instruction.print()
                    ))
                })?;
            let edge_id = *edge_ids
                .get(&(source, *instruction))
                .ok_or_else(|| AdapterError::PhiPredecessorMismatch(instruction.print()))?;

            let assign = match sort_of_instruction_value(incoming_value)? {
                Sort::Bool => TransferEffect::Assign {
                    target: target.clone(),
                    value: AssignValue::Predicate(lower_bool_value(function_name, incoming_value)?),
                },
                Sort::Int | Sort::Real => TransferEffect::Assign {
                    target: target.clone(),
                    value: AssignValue::Term(lower_numeric_value(function_name, incoming_value)?),
                },
            };
            cfg.append_edge_effects(edge_id, [assign])
                .map_err(|error| AdapterError::Cfg(error.to_string()))?;
        }
    }
    let _ = instruction_nodes;
    Ok(())
}

fn lower_assertions(
    function_name: &str,
    graph: &FunctionGraph,
    _cfg: &mut AbstractCfg,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
) -> Result<Vec<AssertionSite>, AdapterError> {
    let mut sites = Vec::new();
    for (index, site) in graph.asserts.iter().enumerate() {
        let node = choose_assert_node(site, instruction_nodes).ok_or(AdapterError::MissingStart)?;
        let obligation = lower_bool_value(function_name, site.asserted_value)?;
        sites.push(AssertionSite {
            id: index + 1,
            node,
            source_location: SourceLocation::default(),
            location: assertion_location(site),
            obligation,
        });
    }
    Ok(sites)
}

fn choose_assert_node(
    site: &crate::common::llvm_utils::program_graph::AssertSite,
    instruction_nodes: &HashMap<Instruction, CfgNodeId>,
) -> Option<CfgNodeId> {
    instruction_nodes
        .get(&site.asserted_value)
        .copied()
        .or_else(|| {
            site.predecessor
                .and_then(|inst| instruction_nodes.get(&inst).copied())
        })
        .or_else(|| {
            site.successor
                .and_then(|inst| instruction_nodes.get(&inst).copied())
        })
}

fn assertion_location(site: &crate::common::llvm_utils::program_graph::AssertSite) -> String {
    if let Some(predecessor) = site.predecessor {
        format!("after {}", predecessor.display_name())
    } else if let Some(successor) = site.successor {
        format!("before {}", successor.display_name())
    } else {
        site.asserted_value.display_name()
    }
}

fn resolve_memory_effects(cfg: &mut AbstractCfg) {
    let order = cfg
        .topological_order()
        .unwrap_or_else(|| cfg.node_ids().collect::<Vec<_>>());

    let mut env = PointerEnv::default();
    for node_id in order {
        let effects = match cfg.node_mut(node_id) {
            Ok(node) => std::mem::take(&mut node.transfer.effects),
            Err(_) => continue,
        };

        let mut rewritten = Vec::new();
        for effect in effects {
            match effect {
                TransferEffect::Alloca { target, region } => {
                    env.bind(target.clone(), region.clone(), Term::int(0));
                    rewritten.push(TransferEffect::Alloca { target, region });
                }
                TransferEffect::GetElementPtr {
                    target,
                    base,
                    offset,
                } => {
                    if let Some(parent) = env.get(&base) {
                        env.bind(
                            target.clone(),
                            parent.region.clone(),
                            Term::add(parent.offset.clone(), offset.clone()),
                        );
                    }
                    rewritten.push(TransferEffect::GetElementPtr {
                        target,
                        base,
                        offset,
                    });
                }
                TransferEffect::Load { target, source } => {
                    if let Some(binding) = env.get(&source) {
                        if target.sort() == Sort::Real {
                            if let Some(slot) =
                                scalar_memory_slot_var(&binding.region, &binding.offset, Sort::Real)
                            {
                                rewritten.push(TransferEffect::Assign {
                                    target,
                                    value: AssignValue::Term(Term::Var(slot)),
                                });
                            } else {
                                rewritten.push(TransferEffect::Load { target, source });
                            }
                        } else {
                            rewritten.push(TransferEffect::Assign {
                                target,
                                value: AssignValue::Term(Term::select(
                                    crate::common::formula::Memory::var(&binding.region),
                                    binding.offset.clone(),
                                )),
                            });
                        }
                    } else {
                        rewritten.push(TransferEffect::Load { target, source });
                    }
                }
                TransferEffect::Store { target, value } => {
                    if let Some(binding) = env.get(&target) {
                        if value.sort().ok() == Some(Sort::Real) {
                            if let Some(slot) =
                                scalar_memory_slot_var(&binding.region, &binding.offset, Sort::Real)
                            {
                                rewritten.push(TransferEffect::Assign {
                                    target: slot,
                                    value: AssignValue::Term(value),
                                });
                            } else {
                                rewritten.push(TransferEffect::Store { target, value });
                            }
                        } else {
                            rewritten.push(TransferEffect::MemoryStore {
                                region: binding.region.clone(),
                                offset: binding.offset.clone(),
                                value,
                            });
                        }
                    } else {
                        rewritten.push(TransferEffect::Store { target, value });
                    }
                }
                TransferEffect::PointerStore {
                    target_slot,
                    value_ptr,
                } => {
                    if let Some(binding) = env.get(&value_ptr).cloned() {
                        env.bind(target_slot.clone(), binding.region, binding.offset);
                    }
                    rewritten.push(TransferEffect::Nop);
                }
                TransferEffect::PointerLoad {
                    target_ptr,
                    source_slot,
                } => {
                    if let Some(binding) = env.get(&source_slot).cloned() {
                        env.bind(target_ptr, binding.region, binding.offset);
                    }
                    rewritten.push(TransferEffect::Nop);
                }
                other => rewritten.push(other),
            }
        }

        if let Ok(node) = cfg.node_mut(node_id) {
            node.transfer.effects = rewritten;
        }
    }
}

fn scalar_memory_slot_var(region: &str, offset: &Term, sort: Sort) -> Option<Var> {
    match offset {
        Term::Int(value) => Some(Var::new(format!("{region}$slot{value}"), sort)),
        _ => None,
    }
}

fn summary_assume_for_call(
    caller: &str,
    instruction: Instruction,
    callee: &str,
    summaries: &CallSummaryRegistry,
) -> Result<Option<TransferEffect>, AdapterError> {
    let Some(summary) = summaries.get(callee).cloned() else {
        return Ok(None);
    };

    let mut mapping = BTreeMap::<String, String>::new();
    let actual_args = instruction.get_call_args();
    for (formal, actual) in summary.formal_parameters.iter().zip(actual_args.iter()) {
        if actual.as_constant_int().is_some() {
            continue;
        }
        mapping.insert(formal.clone(), local_name(caller, *actual));
    }
    mapping.insert(summary.retval_name.clone(), local_name(caller, instruction));

    let call_site_id = summaries.next_call_site_id();
    let local_prefix = format!("{caller}$call{call_site_id}");
    let renamed = rename_callee_vars(
        &summary.relation,
        &mapping,
        &summary.function,
        &local_prefix,
    );

    let mut substituted = renamed;
    for (formal, actual) in summary.formal_parameters.iter().zip(actual_args.iter()) {
        if let Some(constant) = actual.as_constant_int() {
            substituted = substitute_var_name_with_term(&substituted, formal, &Term::int(constant));
        }
    }

    Ok(Some(TransferEffect::Obligation(substituted)))
}

fn rename_callee_vars(
    formula: &Formula,
    mapping: &BTreeMap<String, String>,
    callee_name: &str,
    local_prefix: &str,
) -> Formula {
    let callee_prefix = format!("{callee_name}$");
    rename_vars_in_formula(formula, |name| {
        if let Some(mapped) = mapping.get(name) {
            return mapped.clone();
        }
        if let Some(suffix) = name.strip_prefix(&callee_prefix) {
            format!("{local_prefix}${suffix}")
        } else {
            name.to_string()
        }
    })
}

pub fn rename_vars_in_formula(
    formula: &Formula,
    rename: impl Fn(&str) -> String + Copy,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(Var::new(rename(var.name()), var.sort())),
        Formula::Not(inner) => Formula::not(rename_vars_in_formula(inner, rename)),
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| rename_vars_in_formula(item, rename)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| rename_vars_in_formula(item, rename)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            rename_vars_in_formula(lhs, rename),
            rename_vars_in_formula(rhs, rename),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            rename_vars_in_memory(lhs, rename),
            rename_vars_in_memory(rhs, rename),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
    }
}

pub fn rename_vars_in_term(term: &Term, rename: impl Fn(&str) -> String + Copy) -> Term {
    match term {
        Term::Var(var) => Term::Var(Var::new(rename(var.name()), var.sort())),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(value) => Term::bool_to_int(rename_vars_in_formula(value, rename)),
        Term::Select(memory, index) => Term::select(
            rename_vars_in_memory(memory, rename),
            rename_vars_in_term(index, rename),
        ),
        Term::Add(lhs, rhs) => Term::add(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Term::Div(lhs, rhs) => Term::div(
            rename_vars_in_term(lhs, rename),
            rename_vars_in_term(rhs, rename),
        ),
        Term::Neg(inner) => Term::neg(rename_vars_in_term(inner, rename)),
    }
}

pub fn rename_vars_in_memory(
    memory: &crate::common::formula::Memory,
    rename: impl Fn(&str) -> String + Copy,
) -> crate::common::formula::Memory {
    match memory {
        crate::common::formula::Memory::Var(name) => {
            crate::common::formula::Memory::var(rename(name))
        }
        crate::common::formula::Memory::Store(inner, index, value) => {
            crate::common::formula::Memory::store(
                rename_vars_in_memory(inner, rename),
                rename_vars_in_term(index, rename),
                rename_vars_in_term(value, rename),
            )
        }
    }
}

fn substitute_var_name_with_term(formula: &Formula, name: &str, replacement: &Term) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => {
            Formula::not(substitute_var_name_with_term(inner, name, replacement))
        }
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_var_name_with_term(item, name, replacement)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_var_name_with_term(item, name, replacement)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_var_name_with_term(lhs, name, replacement),
            substitute_var_name_with_term(rhs, name, replacement),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_var_name_with_term_memory(lhs, name, replacement),
            substitute_var_name_with_term_memory(rhs, name, replacement),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
    }
}

fn substitute_var_name_with_term_term(term: &Term, name: &str, replacement: &Term) -> Term {
    match term {
        Term::Var(var) if var.name() == name => replacement.clone(),
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(value) => {
            Term::bool_to_int(substitute_var_name_with_term(value, name, replacement))
        }
        Term::Select(memory, index) => Term::select(
            substitute_var_name_with_term_memory(memory, name, replacement),
            substitute_var_name_with_term_term(index, name, replacement),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_var_name_with_term_term(lhs, name, replacement),
            substitute_var_name_with_term_term(rhs, name, replacement),
        ),
        Term::Neg(inner) => Term::neg(substitute_var_name_with_term_term(inner, name, replacement)),
    }
}

fn substitute_var_name_with_term_memory(
    memory: &crate::common::formula::Memory,
    name: &str,
    replacement: &Term,
) -> crate::common::formula::Memory {
    match memory {
        crate::common::formula::Memory::Var(memory_name) => {
            crate::common::formula::Memory::var(memory_name)
        }
        crate::common::formula::Memory::Store(inner, index, value) => {
            crate::common::formula::Memory::store(
                substitute_var_name_with_term_memory(inner, name, replacement),
                substitute_var_name_with_term_term(index, name, replacement),
                substitute_var_name_with_term_term(value, name, replacement),
            )
        }
    }
}

fn formula_contains_var(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::True | Formula::False => false,
        Formula::Var(var) => var.name() == name,
        Formula::Not(inner) => formula_contains_var(inner, name),
        Formula::And(items) | Formula::Or(items) => {
            items.iter().any(|item| formula_contains_var(item, name))
        }
        Formula::Implies(lhs, rhs) => {
            formula_contains_var(lhs, name) || formula_contains_var(rhs, name)
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => term_contains_var(lhs, name) || term_contains_var(rhs, name),
        Formula::MemoryEq(lhs, rhs) => {
            memory_contains_var(lhs, name) || memory_contains_var(rhs, name)
        }
    }
}

fn term_contains_var(term: &Term, name: &str) -> bool {
    match term {
        Term::Var(var) => var.name() == name,
        Term::Int(_) | Term::Real(_) => false,
        Term::BoolToInt(value) => formula_contains_var(value, name),
        Term::Select(memory, index) => {
            memory_contains_var(memory, name) || term_contains_var(index, name)
        }
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            term_contains_var(lhs, name) || term_contains_var(rhs, name)
        }
        Term::Neg(inner) => term_contains_var(inner, name),
    }
}

fn memory_contains_var(memory: &crate::common::formula::Memory, name: &str) -> bool {
    match memory {
        crate::common::formula::Memory::Var(memory_name) => memory_name == name,
        crate::common::formula::Memory::Store(inner, index, value) => {
            memory_contains_var(inner, name)
                || term_contains_var(index, name)
                || term_contains_var(value, name)
        }
    }
}

pub fn build_horn_model(
    graph: &FunctionGraph,
    procedure: &AdaptedProcedure,
) -> Option<crate::may_must_analysis::chc::HornModel> {
    let summary = compute_return_summary(graph, procedure)?;
    let retval_var = Var::int(summary.retval_name.clone());
    let params = summary
        .formal_parameters
        .iter()
        .map(|name| Var::int(name.clone()))
        .collect::<Vec<_>>();
    let call_refs = graph
        .vertices
        .iter()
        .filter_map(|instruction| {
            if instruction.get_opcode() != InstructionOpcode::Call {
                return None;
            }
            let callee = instruction.get_called_function()?;
            if callee == "may_assert" || callee.starts_with("llvm.") {
                return None;
            }
            let result_var = Var::int(local_name(&graph.name, *instruction));
            if !formula_contains_var(&summary.relation, result_var.name()) {
                return None;
            }
            let actual_args = instruction
                .get_call_args()
                .into_iter()
                .filter_map(|arg| lower_numeric_value(&graph.name, arg).ok())
                .collect::<Vec<_>>();
            Some(crate::may_must_analysis::chc::CallRef {
                callee,
                actual_args,
                result_var,
                result_sort: Sort::Int,
            })
        })
        .collect();
    Some(crate::may_must_analysis::chc::HornModel {
        function: summary.function,
        params,
        retval_var,
        summary_formula: summary.relation,
        call_refs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::TransferEffect;
    use crate::common::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::common::llvm_utils::program_graph::generate_program_graph;

    fn with_graphs(ir: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
    }

    #[test]
    fn adapted_variables_are_prefixed_by_function_name() {
        with_graphs(
            r#"
                define i32 @main(i32 %x) {
                entry:
                    %a = add i32 %x, 1
                    ret i32 %a
                }
            "#,
            |graphs| {
                let adapted = adapt(&graphs[0]).unwrap();
                let entry = adapted.cfg.entry();
                let node = adapted.cfg.node(entry).unwrap();
                assert!(node
                    .transfer
                    .effects
                    .iter()
                    .any(|effect| matches!(effect, TransferEffect::Assign { target, .. } if target.name().starts_with("main$"))));
            },
        );
    }

    #[test]
    fn collect_callee_names_finds_calls() {
        with_graphs(
            r#"
                declare i32 @inc(i32)
                define i32 @main(i32 %x) {
                entry:
                    %v = call i32 @inc(i32 %x)
                    ret i32 %v
                }
            "#,
            |graphs| {
                let names = collect_callee_names(graphs);
                assert!(names.contains("inc"));
            },
        );
    }

    #[test]
    fn return_summary_is_computed_for_single_return_function() {
        with_graphs(
            r#"
                define i32 @inc(i32 %x) {
                entry:
                    %v = add i32 %x, 1
                    ret i32 %v
                }
            "#,
            |graphs| {
                let adapted = adapt(&graphs[0]).unwrap();
                let summary = compute_return_summary(&graphs[0], &adapted).unwrap();
                assert_eq!(summary.function, "inc");
                assert!(summary.relation.to_string().contains("inc$__retval"));
            },
        );
    }

    #[test]
    fn call_summary_is_lowered_as_obligation() {
        with_graphs(
            r#"
                declare i32 @inc(i32)
                define i32 @main(i32 %x) {
                entry:
                    %v = call i32 @inc(i32 %x)
                    ret i32 %v
                }
            "#,
            |graphs| {
                let mut registry = CallSummaryRegistry::new();
                registry.insert(ReturnSummary {
                    function: "inc".to_string(),
                    formal_parameters: vec!["inc$%x".to_string()],
                    retval_name: "inc$__retval".to_string(),
                    relation: Formula::eq(
                        Term::Var(Var::int("inc$__retval")),
                        Term::add(
                            Term::Var(Var::int("inc$%x")),
                            Term::Var(Var::int("inc$tmp")),
                        ),
                    ),
                    write_effects: Vec::new(),
                });
                let adapted =
                    adapt_with_purity_and_summaries(&graphs[0], &BTreeSet::new(), &registry)
                        .unwrap();
                let has_obligation = adapted
                    .cfg
                    .nodes()
                    .values()
                    .flat_map(|node| node.transfer.effects.iter())
                    .any(|effect| matches!(effect, TransferEffect::Obligation(_)));
                assert!(has_obligation);
            },
        );
    }

    #[test]
    fn repeated_calls_get_distinct_callsite_prefixes() {
        with_graphs(
            r#"
                declare i32 @inc(i32)
                define i32 @main(i32 %x) {
                entry:
                    %a = call i32 @inc(i32 %x)
                    %b = call i32 @inc(i32 %a)
                    ret i32 %b
                }
            "#,
            |graphs| {
                let mut registry = CallSummaryRegistry::new();
                registry.insert(ReturnSummary {
                    function: "inc".to_string(),
                    formal_parameters: vec!["inc$%x".to_string()],
                    retval_name: "inc$__retval".to_string(),
                    relation: Formula::eq(
                        Term::Var(Var::int("inc$__retval")),
                        Term::add(
                            Term::Var(Var::int("inc$%x")),
                            Term::Var(Var::int("inc$tmp")),
                        ),
                    ),
                    write_effects: Vec::new(),
                });

                let adapted =
                    adapt_with_purity_and_summaries(&graphs[0], &BTreeSet::new(), &registry)
                        .unwrap();
                let rendered = adapted
                    .cfg
                    .nodes()
                    .values()
                    .flat_map(|node| node.transfer.effects.iter())
                    .filter_map(|effect| {
                        if let TransferEffect::Obligation(formula) = effect {
                            Some(formula.to_string())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                assert!(rendered.contains("main$call0$tmp"));
                assert!(rendered.contains("main$call1$tmp"));
            },
        );
    }
}
