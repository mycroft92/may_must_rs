//! LLVM-backed transition layer for `analysis2` (`Option A`).
//!
//! This module does not modify the paper rules.  It provides a bridge from
//! `EdgeId -> LlvmEdgeMetadata` into `TransitionOracle` operations:
//!
//! - under-approx post image (`theta`) for `MUST-POST`;
//! - over-approx pre image (`beta`) for `NOTMAY-PRE`.

use crate::analysis2::cfg::PaperEdge;
use crate::analysis2::formula::Predicate;
use crate::analysis2::llvm_adapter::{LlvmEdgeMetadata, LlvmEdgeRegistry};
use crate::analysis2::oracle::{OracleError, OracleResult, TransitionOracle};
use crate::llvm_utils::llvm_wrap::InstructionOpcode;

/// Transfer-function-like interface over adapted LLVM edge metadata.
///
/// `analysis2::rules` calls `TransitionOracle`; this trait is the LLVM-backed
/// implementation detail that produces the guard/effect pieces consumed by that
/// oracle.
pub trait LlvmEdgeTransfer {
    fn edge_guard(&self, metadata: &LlvmEdgeMetadata) -> Predicate;
    fn edge_effect(&self, metadata: &LlvmEdgeMetadata) -> Predicate;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct SyntacticLlvmTransfer;

impl LlvmEdgeTransfer for SyntacticLlvmTransfer {
    fn edge_guard(&self, metadata: &LlvmEdgeMetadata) -> Predicate {
        if metadata.opcode != InstructionOpcode::Br {
            return Predicate::True;
        }

        let condition = Predicate::atom(
            metadata
                .branch_condition
                .clone()
                .unwrap_or_else(|| format!("br_cond({})", metadata.edge_id)),
        );
        match metadata.successor_index {
            Some(0) => condition,
            Some(1) => Predicate::not(condition),
            _ => Predicate::True,
        }
    }

    fn edge_effect(&self, metadata: &LlvmEdgeMetadata) -> Predicate {
        Predicate::atom(effect_label(metadata))
    }
}

#[derive(Clone, Debug)]
pub struct LlvmTransitionOracle<'a, T = SyntacticLlvmTransfer> {
    registry: &'a LlvmEdgeRegistry,
    transfer: T,
}

impl<'a> LlvmTransitionOracle<'a, SyntacticLlvmTransfer> {
    pub fn new(registry: &'a LlvmEdgeRegistry) -> Self {
        Self {
            registry,
            transfer: SyntacticLlvmTransfer,
        }
    }
}

impl<'a, T> LlvmTransitionOracle<'a, T> {
    pub fn with_transfer(registry: &'a LlvmEdgeRegistry, transfer: T) -> Self {
        Self { registry, transfer }
    }
}

impl<T> LlvmTransitionOracle<'_, T>
where
    T: LlvmEdgeTransfer,
{
    fn metadata<'a>(&'a self, edge: &PaperEdge) -> OracleResult<&'a LlvmEdgeMetadata> {
        self.registry.metadata(edge.id).ok_or_else(|| {
            OracleError::UnknownTransition(format!("no LLVM metadata found for {}", edge.id))
        })
    }
}

impl<T> TransitionOracle for LlvmTransitionOracle<'_, T>
where
    T: LlvmEdgeTransfer,
{
    fn post_under_approx(&self, edge: &PaperEdge, source: &Predicate) -> OracleResult<Predicate> {
        let metadata = self.metadata(edge)?;
        let guard = self.transfer.edge_guard(metadata);
        let effect = self.transfer.edge_effect(metadata);
        Ok(Predicate::and([source.clone(), guard, effect]))
    }

    fn pre_over_approx(&self, edge: &PaperEdge, _target: &Predicate) -> OracleResult<Predicate> {
        let metadata = self.metadata(edge)?;
        // Deliberately conservative: for branches this is the branch guard;
        // for non-branches this falls back to `true`.
        Ok(self.transfer.edge_guard(metadata))
    }
}

fn effect_label(metadata: &LlvmEdgeMetadata) -> String {
    match metadata.opcode {
        InstructionOpcode::Add => binary_effect(metadata, "add"),
        InstructionOpcode::Sub => binary_effect(metadata, "sub"),
        InstructionOpcode::Mul => binary_effect(metadata, "mul"),
        InstructionOpcode::ICmp => binary_effect(metadata, "icmp"),
        InstructionOpcode::Load => {
            let lhs = metadata
                .assignment
                .clone()
                .unwrap_or_else(|| "%tmp".to_string());
            let ptr = metadata
                .operands
                .first()
                .cloned()
                .unwrap_or_else(|| "%ptr".to_string());
            format!("{lhs}' = load({ptr}) @{}", metadata.edge_id)
        }
        InstructionOpcode::Store => {
            let value = metadata
                .operands
                .first()
                .cloned()
                .unwrap_or_else(|| "%val".to_string());
            let ptr = metadata
                .operands
                .get(1)
                .cloned()
                .unwrap_or_else(|| "%ptr".to_string());
            format!("mem' = store({ptr}, {value}) @{}", metadata.edge_id)
        }
        InstructionOpcode::Call => {
            let callee = metadata
                .called_function
                .clone()
                .unwrap_or_else(|| "unknown".to_string());
            let args = if metadata.operands.is_empty() {
                String::new()
            } else {
                metadata.operands.join(", ")
            };
            if let Some(lhs) = &metadata.assignment {
                format!("{lhs}' = call {callee}({args}) @{}", metadata.edge_id)
            } else {
                format!("call {callee}({args}) @{}", metadata.edge_id)
            }
        }
        InstructionOpcode::Ret => {
            let value = metadata
                .operands
                .first()
                .cloned()
                .unwrap_or_else(|| "void".to_string());
            format!("ret({value}) @{}", metadata.edge_id)
        }
        InstructionOpcode::Br => format!("take_branch({})", metadata.edge_id),
        _ => format!(
            "effect({:?}, {})",
            metadata.opcode, metadata.instruction_text
        ),
    }
}

fn binary_effect(metadata: &LlvmEdgeMetadata, op: &str) -> String {
    let lhs = metadata
        .assignment
        .clone()
        .unwrap_or_else(|| "%tmp".to_string());
    let left = metadata
        .operands
        .first()
        .cloned()
        .unwrap_or_else(|| "%x".to_string());
    let right = metadata
        .operands
        .get(1)
        .cloned()
        .unwrap_or_else(|| "%y".to_string());
    format!("{lhs}' = {op}({left}, {right}) @{}", metadata.edge_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis2::cfg::{EdgeKind, EdgeTransition};
    use crate::analysis2::vocabulary::{EdgeId, NodeId};

    fn branch_edge(edge_id: EdgeId, kind: EdgeKind) -> PaperEdge {
        PaperEdge {
            id: edge_id,
            from: NodeId(0),
            to: NodeId(1),
            gamma: Predicate::atom("Gamma_e"),
            transition: EdgeTransition {
                kind,
                post_under_approx: None,
                pre_over_approx: None,
            },
        }
    }

    fn branch_metadata(edge_id: EdgeId, successor_index: usize) -> LlvmEdgeMetadata {
        LlvmEdgeMetadata {
            edge_id,
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Br,
            instruction_text: "br i1 %c, label %t, label %f".to_string(),
            assignment: None,
            called_function: None,
            operands: vec!["%c".to_string()],
            branch_condition: Some("%c".to_string()),
            successor_index: Some(successor_index),
        }
    }

    #[test]
    fn pre_over_approx_uses_true_branch_guard() {
        let edge = branch_edge(EdgeId(0), EdgeKind::BranchTrue);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(branch_metadata(edge.id, 0));
        let oracle = LlvmTransitionOracle::new(&registry);

        let beta = oracle
            .pre_over_approx(&edge, &Predicate::atom("phi2"))
            .unwrap();
        assert_eq!(beta, Predicate::atom("%c"));
    }

    #[test]
    fn pre_over_approx_uses_false_branch_guard() {
        let edge = branch_edge(EdgeId(1), EdgeKind::BranchFalse);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(branch_metadata(edge.id, 1));
        let oracle = LlvmTransitionOracle::new(&registry);

        let beta = oracle
            .pre_over_approx(&edge, &Predicate::atom("phi2"))
            .unwrap();
        assert_eq!(beta, Predicate::not(Predicate::atom("%c")));
    }

    #[test]
    fn post_under_approx_conjoins_source_guard_and_effect() {
        let edge = branch_edge(EdgeId(2), EdgeKind::BranchTrue);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(branch_metadata(edge.id, 0));
        let oracle = LlvmTransitionOracle::new(&registry);

        let source = Predicate::atom("Omega_n1_phi1");
        let theta = oracle.post_under_approx(&edge, &source).unwrap();

        let expected = Predicate::and([
            source,
            Predicate::atom("%c"),
            Predicate::atom(format!("take_branch({})", edge.id)),
        ]);
        assert_eq!(theta, expected);
    }

    #[test]
    fn missing_edge_metadata_returns_transition_error() {
        let edge = branch_edge(EdgeId(42), EdgeKind::BranchTrue);
        let registry = LlvmEdgeRegistry::new();
        let oracle = LlvmTransitionOracle::new(&registry);

        let err = oracle
            .post_under_approx(&edge, &Predicate::atom("src"))
            .unwrap_err();

        assert!(matches!(err, OracleError::UnknownTransition(_)));
    }
}
