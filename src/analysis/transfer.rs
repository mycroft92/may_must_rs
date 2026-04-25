//! Local transfer semantics over normalized effects produced by
//! `llvm_adapter.rs`.
//!
//! Ordinary branch guards belong on CFG edges as `Gamma_e`; this module only
//! interprets assignment, assumption, obligation, and call effects.

use crate::analysis::formula::{Formula, Sort, Term, Var};
use crate::analysis::state::NodeState;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransferEffect {
    Assign { target: Var, value: AssignValue },
    Assume(Formula),
    Obligation(Formula),
    Nop,
    Call { callee: String },
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
    #[error("assignment sorts do not match: {target} vs {value}")]
    MismatchedAssignmentSort { target: Sort, value: Sort },
    #[error("calls are not supported in phase 1 transfer semantics: {callee}")]
    UnsupportedCall { callee: String },
}

pub fn apply_effect(state: &mut NodeState, effect: &TransferEffect) -> Result<(), TransferError> {
    match effect {
        TransferEffect::Assign { target, value } => apply_assignment(state, target, value),
        TransferEffect::Assume(formula) => {
            state.path_summary_mut().refine(formula.clone());
            Ok(())
        }
        TransferEffect::Obligation(formula) => {
            state.obligations_mut().push(formula.clone());
            Ok(())
        }
        TransferEffect::Nop => Ok(()),
        TransferEffect::Call { callee } => Err(TransferError::UnsupportedCall {
            callee: callee.clone(),
        }),
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
    use crate::analysis::formula::{Predicate, Sort};

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
    fn calls_are_rejected_as_unsupported() {
        let mut state = NodeState::entry();
        let error = apply_effect(
            &mut state,
            &TransferEffect::Call {
                callee: "helper".to_string(),
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            TransferError::UnsupportedCall {
                callee: "helper".to_string(),
            }
        );
    }
}
