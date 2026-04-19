//! SMT-backed LLVM instruction transfer functions.
//!
//! This module implements the first small forward transfer relation over
//! `SmtPathState`. It deliberately does not mutate the existing toy analyzer.
//! Unsupported LLVM instructions return an explicit error so the future SMT
//! engine can report `UNKNOWN` instead of silently dropping semantics.

#![allow(dead_code)]

use crate::analysis::predicates::{Formula, IntTerm, PredicateError};
use crate::analysis::smt_path::SmtPathState;
use crate::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransferError {
    UnsupportedOpcode {
        opcode: InstructionOpcode,
        instruction: String,
    },
    MissingAssignment {
        instruction: String,
    },
    MissingOperand {
        instruction: String,
        index: usize,
    },
    UnsupportedIcmpPredicate {
        instruction: String,
        predicate: String,
    },
    Solver(PredicateError),
}

impl fmt::Display for TransferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TransferError::UnsupportedOpcode {
                opcode,
                instruction,
            } => write!(f, "unsupported opcode {opcode:?} in {instruction}"),
            TransferError::MissingAssignment { instruction } => {
                write!(f, "instruction has no assignment target: {instruction}")
            }
            TransferError::MissingOperand { instruction, index } => {
                write!(f, "instruction is missing operand {index}: {instruction}")
            }
            TransferError::UnsupportedIcmpPredicate {
                instruction,
                predicate,
            } => write!(
                f,
                "unsupported icmp predicate {predicate} in instruction {instruction}"
            ),
            TransferError::Solver(err) => write!(f, "{err}"),
        }
    }
}

impl std::error::Error for TransferError {}

impl From<PredicateError> for TransferError {
    fn from(value: PredicateError) -> Self {
        TransferError::Solver(value)
    }
}

pub type TransferResult<T> = std::result::Result<T, TransferError>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BranchStates {
    pub true_state: Option<SmtPathState>,
    pub false_state: Option<SmtPathState>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransferOutcome {
    Continue(SmtPathState),
    Branch(BranchStates),
    Return(SmtPathState),
}

pub struct TransferFunctions;

impl TransferFunctions {
    pub fn transfer(
        instruction: Instruction,
        state: SmtPathState,
    ) -> TransferResult<TransferOutcome> {
        match instruction.get_opcode() {
            // Temporary stack-memory subset: alloca is only used as a stable
            // pointer name for later store/load map entries. It does not create
            // an SMT object, address, or allocation summary yet.
            InstructionOpcode::Alloca => Ok(TransferOutcome::Continue(state)),
            InstructionOpcode::Store => transfer_store(instruction, state),
            InstructionOpcode::Load => transfer_load(instruction, state),
            InstructionOpcode::Add | InstructionOpcode::Sub | InstructionOpcode::Mul => {
                transfer_binary_int(instruction, state)
            }
            InstructionOpcode::ICmp => transfer_icmp(instruction, state),
            InstructionOpcode::Br => transfer_branch(instruction, state),
            InstructionOpcode::Ret => transfer_return(instruction, state),
            opcode => Err(TransferError::UnsupportedOpcode {
                opcode,
                instruction: one_line_instruction(instruction),
            }),
        }
    }
}

fn transfer_store(
    instruction: Instruction,
    mut state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    let value = instruction
        .get_operand(0)
        .ok_or_else(|| TransferError::MissingOperand {
            instruction: one_line_instruction(instruction),
            index: 0,
        })?;
    let ptr = instruction
        .get_operand(1)
        .ok_or_else(|| TransferError::MissingOperand {
            instruction: one_line_instruction(instruction),
            index: 1,
        })?;

    state.bind_memory_int(pointer_key(ptr), int_value(value, &state));
    Ok(TransferOutcome::Continue(state))
}

fn transfer_load(
    instruction: Instruction,
    mut state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    let target = assigned_name(instruction).ok_or_else(|| TransferError::MissingAssignment {
        instruction: one_line_instruction(instruction),
    })?;
    let ptr = instruction
        .get_operand(0)
        .ok_or_else(|| TransferError::MissingOperand {
            instruction: one_line_instruction(instruction),
            index: 0,
        })?;
    let ptr = pointer_key(ptr);
    // Unknown loads are preserved as fresh scalar terms instead of being
    // treated as concrete values. This is conservative for the current
    // intraprocedural tests, but it is not a real alias-aware memory read.
    let value = state
        .memory_int_value(&ptr)
        .unwrap_or_else(|| IntTerm::ssa(format!("load({ptr})")));

    state.bind_int(target, value);
    Ok(TransferOutcome::Continue(state))
}

fn transfer_binary_int(
    instruction: Instruction,
    mut state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    let target = assigned_name(instruction).ok_or_else(|| TransferError::MissingAssignment {
        instruction: one_line_instruction(instruction),
    })?;
    let left = int_operand(instruction, &state, 0)?;
    let right = int_operand(instruction, &state, 1)?;
    let value = binary_int_term(instruction.get_opcode(), left, right).ok_or_else(|| {
        TransferError::UnsupportedOpcode {
            opcode: instruction.get_opcode(),
            instruction: one_line_instruction(instruction),
        }
    })?;

    state.bind_int(target, value);
    Ok(TransferOutcome::Continue(state))
}

fn transfer_icmp(
    instruction: Instruction,
    mut state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    let target = assigned_name(instruction).ok_or_else(|| TransferError::MissingAssignment {
        instruction: one_line_instruction(instruction),
    })?;
    let left = int_operand(instruction, &state, 0)?;
    let right = int_operand(instruction, &state, 1)?;
    let predicate = instruction.get_icmp_predicate().ok_or_else(|| {
        TransferError::UnsupportedIcmpPredicate {
            instruction: one_line_instruction(instruction),
            predicate: "?".to_string(),
        }
    })?;
    let formula = compare_int_terms(predicate, left, right).ok_or_else(|| {
        TransferError::UnsupportedIcmpPredicate {
            instruction: one_line_instruction(instruction),
            predicate: predicate.to_string(),
        }
    })?;

    state.bind_bool(target, formula);
    Ok(TransferOutcome::Continue(state))
}

fn transfer_branch(
    instruction: Instruction,
    state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    let successors = instruction.get_successors();
    if successors.len() < 2 {
        return Ok(TransferOutcome::Continue(state));
    }

    let Some(condition) = instruction.get_branch_condition() else {
        return Ok(TransferOutcome::Continue(state));
    };

    let condition = bool_value(condition, &state);
    let branches = fork_branch_states(&state, condition)?;
    Ok(TransferOutcome::Branch(branches))
}

fn transfer_return(
    instruction: Instruction,
    mut state: SmtPathState,
) -> TransferResult<TransferOutcome> {
    if let Some(value) = instruction.get_operand(0) {
        let value = int_value(value, &state);
        state.bind_return_int(value);
    }

    Ok(TransferOutcome::Return(state))
}

pub fn fork_branch_states(
    state: &SmtPathState,
    condition: Formula,
) -> TransferResult<BranchStates> {
    let true_state = state.fork_with_assumption(condition.clone())?;
    let false_state = state.fork_with_assumption(condition.negate())?;

    Ok(BranchStates {
        true_state,
        false_state,
    })
}

pub fn binary_int_term(
    opcode: InstructionOpcode,
    left: IntTerm,
    right: IntTerm,
) -> Option<IntTerm> {
    match opcode {
        InstructionOpcode::Add => Some(IntTerm::add(left, right)),
        InstructionOpcode::Sub => Some(IntTerm::sub(left, right)),
        InstructionOpcode::Mul => Some(IntTerm::mul(left, right)),
        _ => None,
    }
}

pub fn compare_int_terms(predicate: &str, left: IntTerm, right: IntTerm) -> Option<Formula> {
    match predicate {
        "==" => Some(Formula::eq(left, right)),
        "!=" => Some(Formula::ne(left, right)),
        ">" => Some(Formula::gt(left, right)),
        ">=" => Some(Formula::ge(left, right)),
        "<" => Some(Formula::lt(left, right)),
        "<=" => Some(Formula::le(left, right)),
        _ => None,
    }
}

fn int_operand(
    instruction: Instruction,
    state: &SmtPathState,
    index: usize,
) -> TransferResult<IntTerm> {
    let operand = instruction
        .get_operand(index)
        .ok_or_else(|| TransferError::MissingOperand {
            instruction: one_line_instruction(instruction),
            index,
        })?;
    Ok(int_value(operand, state))
}

fn int_value(value: Instruction, state: &SmtPathState) -> IntTerm {
    if let Some(value) = value.as_constant_int() {
        return IntTerm::int(value);
    }

    if let Some(name) = value_name(value) {
        return state.int_value(name);
    }

    IntTerm::ssa(one_line_instruction(value))
}

fn bool_value(value: Instruction, state: &SmtPathState) -> Formula {
    if let Some(value) = value.as_constant_int() {
        return if value == 0 {
            Formula::False
        } else {
            Formula::True
        };
    }

    if let Some(name) = value_name(value) {
        return state.bool_value(name);
    }

    Formula::bool_ssa(one_line_instruction(value))
}

fn assigned_name(instruction: Instruction) -> Option<String> {
    instruction.get_assignment_var().map(normalize_name)
}

fn value_name(value: Instruction) -> Option<String> {
    value
        .get_name()
        .or_else(|| value.get_assignment_var())
        .map(normalize_name)
}

fn pointer_key(value: Instruction) -> String {
    // Temporary simplification: pointer identity is the LLVM value name or a
    // one-line printed operand. This is good enough for direct stack slots like
    // `%1`, but not for aliases, GEP-derived addresses, globals, or heap cells.
    value_name(value).unwrap_or_else(|| one_line_instruction(value))
}

fn normalize_name(name: impl AsRef<str>) -> String {
    let name = name.as_ref();
    if name.starts_with('%') {
        name.to_string()
    } else {
        format!("%{name}")
    }
}

fn one_line_instruction(instruction: Instruction) -> String {
    let text = instruction.print().replace('\n', " ");
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_transfer_terms_fold_constants() {
        assert_eq!(
            binary_int_term(InstructionOpcode::Add, IntTerm::int(1), IntTerm::int(2)),
            Some(IntTerm::int(3))
        );
        assert_eq!(
            binary_int_term(InstructionOpcode::Mul, IntTerm::ssa("%x"), IntTerm::int(1)),
            Some(IntTerm::ssa("%x"))
        );
    }

    #[test]
    fn compare_terms_builds_smt_formula() {
        let x = IntTerm::ssa("%x");
        let formula = compare_int_terms(">=", x.clone(), IntTerm::int(4)).unwrap();

        assert!(Formula::eq(x, IntTerm::int(5))
            .entails_in(&formula, "main")
            .unwrap());
    }

    #[test]
    fn branch_fork_uses_smt_to_prune_edges() {
        let mut state = SmtPathState::new("main");
        state.bind_int("%x", IntTerm::int(4));

        let condition = Formula::eq(state.int_value("%x"), IntTerm::int(4));
        let branches = fork_branch_states(&state, condition).unwrap();

        assert!(branches.true_state.is_some());
        assert!(branches.false_state.is_none());
    }
}
