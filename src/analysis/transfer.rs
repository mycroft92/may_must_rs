//! Local transfer semantics over normalized effects produced by
//! `llvm_adapter.rs`.
//!
//! Ordinary branch guards belong on CFG edges as `Gamma_e`; this module only
//! interprets normalized local effects:
//!
//! - scalar assignments
//! - integer-array memory operations
//! - trusted assumptions / obligations
//! - call-side memory havoc or preservation
//!
//! Calls preserve their interface data here so the rule driver can later build
//! interprocedural queries and instantiate summaries, including visible memory
//! ports on pointer arguments. The bounded executor still treats scalar returns
//! conservatively unless a richer summary path is available.

use crate::analysis::formula::{Formula, Memory, Sort, Term, Var};
use crate::analysis::state::NodeState;
use thiserror::Error;

/// How one call affects the tracked integer-array memory state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallMemoryEffect {
    PreservesMemory,
    HavocMemory,
}

/// Normalized call-site argument passed to the rule driver or bounded executor.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallArgument {
    Term(Term),
    Predicate(Formula),
    Pointer(PointerArgument),
}

/// Pointer actual passed at one call site.
///
/// Before rewrite, `memory_before` / `memory_after` are absent and `region`
/// still names the raw pointer SSA value. The rule-query rewrite resolves that
/// pointer to a canonical region plus offset and snapshots the pre/post memory
/// expressions seen around the call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointerArgument {
    region: String,
    offset: Term,
    memory_before: Option<Memory>,
    memory_after: Option<Memory>,
}

impl PointerArgument {
    pub fn raw(region: impl Into<String>) -> Self {
        Self {
            region: region.into(),
            offset: Term::int(0),
            memory_before: None,
            memory_after: None,
        }
    }

    pub fn resolved(
        region: impl Into<String>,
        offset: Term,
        memory_before: Memory,
        memory_after: Memory,
    ) -> Self {
        Self {
            region: region.into(),
            offset,
            memory_before: Some(memory_before),
            memory_after: Some(memory_after),
        }
    }

    pub fn region(&self) -> &str {
        &self.region
    }

    pub fn offset(&self) -> &Term {
        &self.offset
    }

    pub fn memory_before(&self) -> Option<&Memory> {
        self.memory_before.as_ref()
    }

    pub fn memory_after(&self) -> Option<&Memory> {
        self.memory_after.as_ref()
    }
}

/// One normalized local effect interpreted by `apply_effect`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransferEffect {
    Assign {
        target: Var,
        value: AssignValue,
    },
    Alloca {
        target: String,
        region: String,
    },
    GetElementPtr {
        target: String,
        base: String,
        offset: Term,
    },
    Load {
        target: Var,
        source: String,
    },
    Store {
        target: String,
        value: Term,
    },
    Assume(Formula),
    Obligation(Formula),
    Nop,
    Call {
        callee: String,
        arguments: Vec<CallArgument>,
        return_target: Option<Var>,
        memory_effect: CallMemoryEffect,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssignValue {
    Term(Term),
    Predicate(Formula),
}

impl AssignValue {
    fn sort(&self) -> Result<Sort, TransferError> {
        match self {
            AssignValue::Term(term) => term
                .sort()
                .map_err(|_| TransferError::ExpectedNumericTarget { found: Sort::Bool }),
            AssignValue::Predicate(formula) => {
                formula
                    .validate()
                    .map_err(|_| TransferError::ExpectedBooleanTarget { found: Sort::Int })?;
                Ok(Sort::Bool)
            }
        }
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum TransferError {
    #[error("expected a numeric target but found {found}")]
    ExpectedNumericTarget { found: Sort },
    #[error("expected a Boolean target but found {found}")]
    ExpectedBooleanTarget { found: Sort },
    #[error("expected an integer memory value but found {found}")]
    ExpectedIntegerMemoryValue { found: Sort },
    #[error("assignment sorts do not match: {target} vs {value}")]
    MismatchedAssignmentSort { target: Sort, value: Sort },
}

pub fn apply_effect(state: &mut NodeState, effect: &TransferEffect) -> Result<(), TransferError> {
    match effect {
        TransferEffect::Assign { target, value } => apply_assignment(state, target, value),
        TransferEffect::Alloca { target, region } => {
            state.bind_alloca_pointer(target.clone(), region.clone());
            Ok(())
        }
        TransferEffect::GetElementPtr {
            target,
            base,
            offset,
        } => {
            ensure_integer_term(offset)?;
            state.bind_pointer_offset(target.clone(), base, offset.clone());
            Ok(())
        }
        TransferEffect::Load { target, source } => {
            if target.sort() != Sort::Int {
                return Err(TransferError::ExpectedIntegerMemoryValue {
                    found: target.sort(),
                });
            }
            state.load_from_pointer(target, source);
            Ok(())
        }
        TransferEffect::Store { target, value } => {
            ensure_integer_term(value)?;
            state.store_to_pointer(target, value.clone());
            Ok(())
        }
        TransferEffect::Assume(formula) => {
            state.path_summary_mut().refine(formula.clone());
            Ok(())
        }
        TransferEffect::Obligation(formula) => {
            state.obligations_mut().push(formula.clone());
            Ok(())
        }
        TransferEffect::Nop => Ok(()),
        TransferEffect::Call {
            callee: _,
            arguments: _,
            return_target: _,
            memory_effect,
        } => {
            if *memory_effect == CallMemoryEffect::HavocMemory {
                state.havoc_memory();
            }
            Ok(())
        }
    }
}

fn apply_assignment(
    state: &mut NodeState,
    target: &Var,
    value: &AssignValue,
) -> Result<(), TransferError> {
    let value_sort = value.sort()?;
    if target.sort() != value_sort {
        return Err(TransferError::MismatchedAssignmentSort {
            target: target.sort(),
            value: value_sort,
        });
    }
    match value {
        AssignValue::Term(term) => {
            if target.sort() == Sort::Bool {
                return Err(TransferError::ExpectedNumericTarget {
                    found: target.sort(),
                });
            }
            state
                .facts_mut()
                .push(Formula::eq(Term::Var(target.clone()), term.clone()));
            Ok(())
        }
        AssignValue::Predicate(formula) => {
            if target.sort() != Sort::Bool {
                return Err(TransferError::ExpectedBooleanTarget {
                    found: target.sort(),
                });
            }
            state
                .facts_mut()
                .push(Formula::iff(Formula::Var(target.clone()), formula.clone()));
            Ok(())
        }
    }
}

fn ensure_integer_term(term: &Term) -> Result<(), TransferError> {
    match term.sort() {
        Ok(Sort::Int) => Ok(()),
        Ok(found) => Err(TransferError::ExpectedIntegerMemoryValue { found }),
        Err(_) => Err(TransferError::ExpectedIntegerMemoryValue { found: Sort::Bool }),
    }
}

pub fn apply_effects(
    state: &mut NodeState,
    effects: &[TransferEffect],
) -> Result<(), TransferError> {
    for effect in effects {
        apply_effect(state, effect)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Memory, Predicate, Sort};

    #[test]
    fn arithmetic_assignment_produces_an_equality_fact() {
        let mut state = NodeState::entry();
        let effect = TransferEffect::Assign {
            target: Var::int("x"),
            value: AssignValue::Term(Term::add(Term::var("y", Sort::Int), Term::int(1))),
        };
        apply_effect(&mut state, &effect).unwrap();
        assert_eq!(
            state.facts().collapse(),
            Formula::eq(
                Term::Var(Var::int("x")),
                Term::add(Term::var("y", Sort::Int), Term::int(1))
            )
        );
    }

    #[test]
    fn predicate_assignment_produces_boolean_equivalence() {
        let mut state = NodeState::entry();
        let effect = TransferEffect::Assign {
            target: Var::bool("p"),
            value: AssignValue::Predicate(Formula::and(
                Formula::bool_var("q"),
                Formula::bool_var("r"),
            )),
        };
        apply_effect(&mut state, &effect).unwrap();
        assert_eq!(
            state.facts().collapse(),
            Formula::iff(
                Formula::Var(Var::bool("p")),
                Formula::and(Formula::bool_var("q"), Formula::bool_var("r"))
            )
        );
    }

    #[test]
    fn assumptions_refine_path_summaries() {
        let mut state = NodeState::entry();
        apply_effect(
            &mut state,
            &TransferEffect::Assume(Formula::bool_var("guard")),
        )
        .unwrap();
        assert_eq!(
            state.path_summary().predicate(),
            &Predicate::bool_var("guard")
        );
    }

    #[test]
    fn obligations_remain_separate_from_facts() {
        let mut state = NodeState::entry();
        apply_effect(
            &mut state,
            &TransferEffect::Assign {
                target: Var::bool("p"),
                value: AssignValue::Predicate(Formula::bool_var("q")),
            },
        )
        .unwrap();
        apply_effect(
            &mut state,
            &TransferEffect::Obligation(Formula::not(Formula::bool_var("safe"))),
        )
        .unwrap();
        assert_eq!(state.facts().formulas().len(), 1);
        assert_eq!(state.obligations().formulas().len(), 1);
    }

    #[test]
    fn sequencing_composes_local_effects() {
        let mut state = NodeState::entry();
        apply_effects(
            &mut state,
            &[
                TransferEffect::Assume(Formula::bool_var("guard")),
                TransferEffect::Assign {
                    target: Var::int("x"),
                    value: AssignValue::Term(Term::int(5)),
                },
            ],
        )
        .unwrap();
        assert_eq!(
            state.path_summary().predicate(),
            &Formula::bool_var("guard")
        );
        assert_eq!(state.facts().formulas().len(), 1);
    }

    #[test]
    fn bad_sort_assignments_are_rejected() {
        let mut state = NodeState::entry();
        let error = apply_effect(
            &mut state,
            &TransferEffect::Assign {
                target: Var::int("x"),
                value: AssignValue::Term(Term::real(1, 2)),
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            TransferError::MismatchedAssignmentSort {
                target: Sort::Int,
                value: Sort::Real,
            }
        );
    }

    #[test]
    fn memory_loads_and_stores_use_integer_arrays() {
        let mut state = NodeState::entry();
        apply_effect(
            &mut state,
            &TransferEffect::Alloca {
                target: "%ptr".to_string(),
                region: "stack.ptr".to_string(),
            },
        )
        .unwrap();
        apply_effect(
            &mut state,
            &TransferEffect::Store {
                target: "%ptr".to_string(),
                value: Term::int(9),
            },
        )
        .unwrap();
        apply_effect(
            &mut state,
            &TransferEffect::Load {
                target: Var::int("%x"),
                source: "%ptr".to_string(),
            },
        )
        .unwrap();
        assert_eq!(
            state.facts().collapse(),
            Formula::eq(
                Term::Var(Var::int("%x")),
                Term::select(
                    Memory::store(Memory::var("stack.ptr$mem0"), Term::int(0), Term::int(9),),
                    Term::int(0),
                ),
            )
        );
    }

    #[test]
    fn impure_calls_havoc_memory() {
        let mut state = NodeState::entry();
        apply_effect(
            &mut state,
            &TransferEffect::Alloca {
                target: "%ptr".to_string(),
                region: "stack.ptr".to_string(),
            },
        )
        .unwrap();
        apply_effect(
            &mut state,
            &TransferEffect::Call {
                callee: "touch".to_string(),
                arguments: vec![CallArgument::Pointer(PointerArgument::raw("%ptr"))],
                return_target: None,
                memory_effect: CallMemoryEffect::HavocMemory,
            },
        )
        .unwrap();
        assert_eq!(state.memory_summary(), "[stack.ptr=stack.ptr$mem1]");
    }
}
