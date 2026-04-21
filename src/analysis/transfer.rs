//! LLVM-backed transition layer for the active paper analysis (`Option A`).
//!
//! This module does not modify the paper rules.  It provides a bridge from
//! `EdgeId -> LlvmEdgeMetadata` into `TransitionOracle` operations:
//!
//! - under-approx post image (`theta`) for `MUST-POST`;
//! - over-approx pre image (`beta`) for `NOTMAY-PRE`.
//!
//! Paper correspondence:
//!
//! ```text
//! LlvmEdgeTransfer        -> LLVM-specific approximation of Gamma_e reasoning
//! LlvmTransitionOracle    -> TransitionOracle implementation
//! post_under_approx       -> choose theta for MUST-POST
//! pre_over_approx         -> choose beta for NOTMAY-PRE
//! ```
//!
//! This file may eventually use SMT-backed state encodings internally, but it
//! should not become the place that owns the global solver interface.

use crate::analysis::cfg::PaperEdge;
use crate::analysis::formula::Predicate;
use crate::analysis::llvm_adapter::{LlvmEdgeMetadata, LlvmEdgeRegistry};
use crate::analysis::oracle::{
    OracleError, OracleResult, PredicateOracle, SmtPredicateOracle, TransitionOracle,
};
use crate::analysis::vocabulary::EdgeId;
use crate::llvm_utils::llvm_wrap::InstructionOpcode;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssertionTargetMode {
    Violation,
    SiteReachability,
}

/// Transfer-function-like interface over adapted LLVM edge metadata.
///
/// `analysis::rules` calls `TransitionOracle`; this trait is the LLVM-backed
/// implementation detail that produces the guard/effect pieces consumed by that
/// oracle.
pub trait LlvmEdgeTransfer {
    fn edge_guard(&self, metadata: &LlvmEdgeMetadata) -> Predicate;
    fn edge_effect(
        &self,
        metadata: &LlvmEdgeMetadata,
        target_assertion: Option<EdgeId>,
        target_mode: AssertionTargetMode,
    ) -> Predicate;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct SyntacticLlvmTransfer;

impl LlvmEdgeTransfer for SyntacticLlvmTransfer {
    fn edge_guard(&self, metadata: &LlvmEdgeMetadata) -> Predicate {
        // APPROX_HEAVY: Branch guards are extracted syntactically from edge
        // metadata, without modeling full SSA/dataflow dependencies.
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

    fn edge_effect(
        &self,
        metadata: &LlvmEdgeMetadata,
        target_assertion: Option<EdgeId>,
        target_mode: AssertionTargetMode,
    ) -> Predicate {
        edge_effect_predicate(metadata, target_assertion, target_mode)
    }
}

#[derive(Clone, Debug)]
pub struct LlvmTransitionOracle<'a, T = SyntacticLlvmTransfer> {
    registry: &'a LlvmEdgeRegistry,
    transfer: T,
    target_assertion: Option<EdgeId>,
    target_assertion_mode: AssertionTargetMode,
}

impl<'a> LlvmTransitionOracle<'a, SyntacticLlvmTransfer> {
    pub fn new(registry: &'a LlvmEdgeRegistry) -> Self {
        Self {
            registry,
            transfer: SyntacticLlvmTransfer,
            target_assertion: None,
            target_assertion_mode: AssertionTargetMode::Violation,
        }
    }

    pub fn with_target_assertion(
        registry: &'a LlvmEdgeRegistry,
        target_assertion: Option<EdgeId>,
    ) -> Self {
        Self::with_target_assertion_mode(registry, target_assertion, AssertionTargetMode::Violation)
    }

    pub fn with_target_assertion_mode(
        registry: &'a LlvmEdgeRegistry,
        target_assertion: Option<EdgeId>,
        target_assertion_mode: AssertionTargetMode,
    ) -> Self {
        Self {
            registry,
            transfer: SyntacticLlvmTransfer,
            target_assertion,
            target_assertion_mode,
        }
    }
}

impl<'a, T> LlvmTransitionOracle<'a, T> {
    pub fn with_transfer(
        registry: &'a LlvmEdgeRegistry,
        transfer: T,
        target_assertion: Option<EdgeId>,
        target_assertion_mode: AssertionTargetMode,
    ) -> Self {
        Self {
            registry,
            transfer,
            target_assertion,
            target_assertion_mode,
        }
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
        // APPROX_HEAVY: Uses guard/effect conjunction as an under-approximate
        // post image instead of a full transition-relation image.
        let effect =
            self.transfer
                .edge_effect(metadata, self.target_assertion, self.target_assertion_mode);
        Ok(Predicate::and([source.clone(), guard, effect]))
    }

    fn pre_over_approx(&self, edge: &PaperEdge, _target: &Predicate) -> OracleResult<Predicate> {
        let metadata = self.metadata(edge)?;
        // APPROX_HEAVY: Ignores `target` and returns guard-only beta.
        // Deliberately conservative: for branches this is the branch guard;
        // for non-branches this falls back to `true`.
        Ok(self.transfer.edge_guard(metadata))
    }
}

/// SMT-backed LLVM transition oracle.
///
/// It uses the same metadata-driven guard/effect extraction as
/// `LlvmTransitionOracle`, but validates candidates with SMT:
///
/// - `theta` is returned as `false` when `source ∧ guard ∧ effect` is UNSAT;
/// - `beta` is returned as `false` when `guard` is UNSAT.
#[derive(Clone, Debug)]
pub struct SmtLlvmTransitionOracle<'a, T = SyntacticLlvmTransfer> {
    registry: &'a LlvmEdgeRegistry,
    transfer: T,
    target_assertion: Option<EdgeId>,
    target_assertion_mode: AssertionTargetMode,
    predicates: SmtPredicateOracle,
}

impl<'a> SmtLlvmTransitionOracle<'a, SyntacticLlvmTransfer> {
    pub fn new(registry: &'a LlvmEdgeRegistry) -> Self {
        Self {
            registry,
            transfer: SyntacticLlvmTransfer,
            target_assertion: None,
            target_assertion_mode: AssertionTargetMode::Violation,
            predicates: SmtPredicateOracle,
        }
    }

    pub fn with_target_assertion(
        registry: &'a LlvmEdgeRegistry,
        target_assertion: Option<EdgeId>,
    ) -> Self {
        Self::with_target_assertion_mode(registry, target_assertion, AssertionTargetMode::Violation)
    }

    pub fn with_target_assertion_mode(
        registry: &'a LlvmEdgeRegistry,
        target_assertion: Option<EdgeId>,
        target_assertion_mode: AssertionTargetMode,
    ) -> Self {
        Self {
            registry,
            transfer: SyntacticLlvmTransfer,
            target_assertion,
            target_assertion_mode,
            predicates: SmtPredicateOracle,
        }
    }
}

impl<'a, T> SmtLlvmTransitionOracle<'a, T> {
    pub fn with_transfer(
        registry: &'a LlvmEdgeRegistry,
        transfer: T,
        target_assertion: Option<EdgeId>,
        target_assertion_mode: AssertionTargetMode,
    ) -> Self {
        Self {
            registry,
            transfer,
            target_assertion,
            target_assertion_mode,
            predicates: SmtPredicateOracle,
        }
    }
}

impl<T> SmtLlvmTransitionOracle<'_, T>
where
    T: LlvmEdgeTransfer,
{
    fn metadata<'a>(&'a self, edge: &PaperEdge) -> OracleResult<&'a LlvmEdgeMetadata> {
        self.registry.metadata(edge.id).ok_or_else(|| {
            OracleError::UnknownTransition(format!("no LLVM metadata found for {}", edge.id))
        })
    }
}

impl<T> TransitionOracle for SmtLlvmTransitionOracle<'_, T>
where
    T: LlvmEdgeTransfer,
{
    fn post_under_approx(&self, edge: &PaperEdge, source: &Predicate) -> OracleResult<Predicate> {
        let metadata = self.metadata(edge)?;
        let guard = self.transfer.edge_guard(metadata);
        let effect =
            self.transfer
                .edge_effect(metadata, self.target_assertion, self.target_assertion_mode);
        // APPROX_HEAVY: Same guard/effect approximation as syntactic oracle,
        // with only an SMT SAT/UNSAT filter for pruning impossible theta.
        let theta = Predicate::and([source.clone(), guard, effect]);
        if self.predicates.is_empty(&theta)? {
            Ok(Predicate::False)
        } else {
            Ok(theta)
        }
    }

    fn pre_over_approx(&self, edge: &PaperEdge, _target: &Predicate) -> OracleResult<Predicate> {
        let metadata = self.metadata(edge)?;
        // APPROX_HEAVY: Same guard-only beta approximation; `_target` is
        // currently unused in the over-approximate predecessor calculation.
        let beta = self.transfer.edge_guard(metadata);
        if self.predicates.is_empty(&beta)? {
            Ok(Predicate::False)
        } else {
            Ok(beta)
        }
    }
}

pub fn edge_effect_predicate(
    metadata: &LlvmEdgeMetadata,
    target_assertion: Option<EdgeId>,
    target_mode: AssertionTargetMode,
) -> Predicate {
    if target_assertion == Some(metadata.edge_id) {
        match target_mode {
            AssertionTargetMode::Violation => {
                if let Some(violation) = assertion_violation_predicate(metadata) {
                    return violation;
                }
            }
            AssertionTargetMode::SiteReachability => {
                if let Some(site) = assertion_site_predicate(metadata) {
                    return site;
                }
            }
        }
    }
    // APPROX_HEAVY: Non-target edges fall back to opcode-derived symbolic
    // effect labels rather than a precise relational update.
    Predicate::atom(effect_label(metadata))
}

pub fn assertion_site_predicate(metadata: &LlvmEdgeMetadata) -> Option<Predicate> {
    if metadata.called_function.as_deref() != Some("may_assert") {
        return None;
    }
    Some(Predicate::atom(format!(
        "assert_violation({})",
        metadata.edge_id
    )))
}

pub fn assertion_violation_predicate(metadata: &LlvmEdgeMetadata) -> Option<Predicate> {
    if metadata.called_function.as_deref() != Some("may_assert") {
        return None;
    }

    let site = assertion_site_predicate(metadata)?;
    let arg = metadata
        .operands
        .first()
        .cloned()
        .unwrap_or_else(|| format!("assert_arg({})", metadata.edge_id));
    let asserted = boolean_argument_predicate(&arg);
    Some(Predicate::and([site, Predicate::not(asserted)]))
}

fn boolean_argument_predicate(argument: &str) -> Predicate {
    let normalized = argument.trim();
    if normalized.eq_ignore_ascii_case("true") {
        return Predicate::True;
    }
    if normalized.eq_ignore_ascii_case("false") {
        return Predicate::False;
    }
    if let Ok(value) = normalized.parse::<i64>() {
        return if value == 0 {
            Predicate::False
        } else {
            Predicate::True
        };
    }
    Predicate::atom(normalized.to_string())
}

fn effect_label(metadata: &LlvmEdgeMetadata) -> String {
    // APPROX_HEAVY: Encodes LLVM effects as lightweight string atoms; many
    // operations are summarized syntactically rather than semantically.
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
        // APPROX_HEAVY: Unsupported/other opcodes collapse into an opaque
        // uninterpreted effect token.
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
    use crate::analysis::cfg::{EdgeKind, EdgeTransition};
    use crate::analysis::vocabulary::{EdgeId, NodeId};

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

    fn may_assert_metadata(edge_id: EdgeId, arg: &str) -> LlvmEdgeMetadata {
        LlvmEdgeMetadata {
            edge_id,
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Call,
            instruction_text: format!("call void @may_assert(i1 {arg})"),
            assignment: None,
            called_function: Some("may_assert".to_string()),
            operands: vec![arg.to_string()],
            branch_condition: None,
            successor_index: None,
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
    fn smt_post_under_approx_returns_false_for_unsat_source_and_guard() {
        let edge = branch_edge(EdgeId(3), EdgeKind::BranchTrue);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(branch_metadata(edge.id, 0));
        let oracle = SmtLlvmTransitionOracle::new(&registry);

        let theta = oracle
            .post_under_approx(&edge, &Predicate::not(Predicate::atom("%c")))
            .unwrap();

        assert_eq!(theta, Predicate::False);
    }

    #[test]
    fn smt_pre_over_approx_returns_false_for_unsat_guard() {
        let edge = branch_edge(EdgeId(4), EdgeKind::BranchTrue);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(LlvmEdgeMetadata {
            edge_id: edge.id,
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Br,
            instruction_text: "br i1 false, label %t, label %f".to_string(),
            assignment: None,
            called_function: None,
            operands: vec!["false".to_string()],
            branch_condition: Some("false".to_string()),
            successor_index: Some(0),
        });
        let oracle = SmtLlvmTransitionOracle::new(&registry);

        let beta = oracle
            .pre_over_approx(&edge, &Predicate::atom("phi2"))
            .unwrap();

        assert_eq!(beta, Predicate::False);
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

    #[test]
    fn target_assert_edge_uses_violation_predicate() {
        let edge = branch_edge(EdgeId(4), EdgeKind::Local);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(may_assert_metadata(edge.id, "%cond"));
        let oracle = LlvmTransitionOracle::with_target_assertion(&registry, Some(edge.id));

        let theta = oracle
            .post_under_approx(&edge, &Predicate::atom("Omega_n1_phi1"))
            .unwrap();

        assert_eq!(
            theta,
            Predicate::and([
                Predicate::atom("Omega_n1_phi1"),
                Predicate::True,
                Predicate::and([
                    Predicate::atom("assert_violation(e4)"),
                    Predicate::not(Predicate::atom("%cond")),
                ]),
            ]),
        );
    }

    #[test]
    fn non_target_assert_edge_stays_as_regular_call_effect() {
        let edge = branch_edge(EdgeId(5), EdgeKind::Local);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(may_assert_metadata(edge.id, "%cond"));
        let oracle = LlvmTransitionOracle::with_target_assertion(&registry, Some(EdgeId(99)));

        let theta = oracle
            .post_under_approx(&edge, &Predicate::atom("Omega_n1_phi1"))
            .unwrap();

        assert_eq!(
            theta,
            Predicate::and([
                Predicate::atom("Omega_n1_phi1"),
                Predicate::True,
                Predicate::atom("call may_assert(%cond) @e5"),
            ]),
        );
    }

    #[test]
    fn may_assert_zero_becomes_site_violation() {
        let metadata = may_assert_metadata(EdgeId(4), "0");
        let violation = assertion_violation_predicate(&metadata).unwrap();
        assert_eq!(violation, Predicate::atom("assert_violation(e4)"));
    }

    #[test]
    fn may_assert_one_becomes_false() {
        let metadata = may_assert_metadata(EdgeId(5), "1");
        let violation = assertion_violation_predicate(&metadata).unwrap();
        assert_eq!(violation, Predicate::False);
    }

    #[test]
    fn may_assert_symbolic_arg_negates_the_argument() {
        let metadata = may_assert_metadata(EdgeId(6), "%cond");
        let violation = assertion_violation_predicate(&metadata).unwrap();
        assert_eq!(
            violation,
            Predicate::and([
                Predicate::atom("assert_violation(e6)"),
                Predicate::not(Predicate::atom("%cond")),
            ]),
        );
    }

    #[test]
    fn target_assert_edge_uses_site_marker_in_site_reachability_mode() {
        let edge = branch_edge(EdgeId(7), EdgeKind::Local);
        let mut registry = LlvmEdgeRegistry::new();
        registry.insert(may_assert_metadata(edge.id, "1"));
        let oracle = LlvmTransitionOracle::with_target_assertion_mode(
            &registry,
            Some(edge.id),
            AssertionTargetMode::SiteReachability,
        );

        let theta = oracle
            .post_under_approx(&edge, &Predicate::atom("Omega_n1_phi1"))
            .unwrap();

        assert_eq!(
            theta,
            Predicate::and([
                Predicate::atom("Omega_n1_phi1"),
                Predicate::True,
                Predicate::atom("assert_violation(e7)"),
            ]),
        );
    }
}
