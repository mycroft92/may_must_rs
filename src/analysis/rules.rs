//! Named declarative rules from Figures 5-10 of the SMASH paper.
//!
//! The goal here is to keep the public interface close to the paper. Each
//! figure gets its own namespace so rules with the same paper name but
//! different premises can coexist without being blurred into one ad hoc API.
//! Premises involving `Pre`, `Post`, or `∃V^L` are passed in explicitly as
//! `β`, `θ`, or a projection closure instead of being hidden inside the rules.
//!
//! The current module is intentionally declarative rather than executable.
//! It stores and updates the paper carriers:
//!
//! - `Π_n` as a partition-like list of regions per node
//! - `Ω_n` as one accumulated must-region per node
//! - `N_e` as blocked abstract `(ϕ_1, ϕ_2)` pairs per edge
//! - `⟨ϕ_1 ?⇒_P ϕ_2⟩` as [`ReachabilityQuery`]
//!
//! A future `driver.rs` is expected to choose candidate `β` / `θ` formulas and
//! schedule these rules over lowered LLVM procedures.

use crate::analysis::cfg::{Cfg, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::Formula;
use crate::analysis::oracle::{Feasibility, Oracle, OracleError, Validity};
use crate::analysis::summaries::{MustSummary, NotMaySummary, ProcedureName, SummaryTables};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use thiserror::Error;

pub type Region = Formula;

/// The paper query `⟨ϕ_1 ?⇒_P ϕ_2⟩` for one procedure `P`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReachabilityQuery {
    pub procedure: ProcedureName,
    pub precondition: Formula,
    pub postcondition: Formula,
}

impl ReachabilityQuery {
    /// Builds a query in the same shape as the paper notation.
    pub fn new(
        procedure: impl Into<ProcedureName>,
        precondition: Formula,
        postcondition: Formula,
    ) -> Self {
        Self {
            procedure: procedure.into(),
            precondition,
            postcondition,
        }
    }
}

/// Final judgements for one reachability query.
///
/// `Yes` corresponds to a found bug / witness, `No` corresponds to a verified
/// not-may result, and `Unknown` means the currently available rules do not
/// settle the query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryJudgement {
    Yes,
    No,
    Unknown,
}

/// One abstract blocked pair in `N_e`.
///
/// The pair means that abstract execution from `pre_region` at the source of
/// `e` to `post_region` at the target of `e` has been ruled out.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NotMayPair {
    pub pre_region: Formula,
    pub post_region: Formula,
}

/// All paper carriers for one procedure/query instance.
///
/// This is the mutable frame over which the named rules operate. It does not
/// choose which rule to apply; it only stores the state those rules read and
/// update.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProcedureFrame {
    cfg: Cfg,
    query: ReachabilityQuery,
    pi: BTreeMap<CfgNodeId, Vec<Formula>>,
    omega: BTreeMap<CfgNodeId, Formula>,
    ne: BTreeMap<CfgEdgeId, Vec<NotMayPair>>,
}

impl ProcedureFrame {
    /// Creates an empty rule frame for one normalized procedure CFG and one
    /// paper query.
    pub fn new(cfg: Cfg, query: ReachabilityQuery) -> Self {
        Self {
            cfg,
            query,
            pi: BTreeMap::new(),
            omega: BTreeMap::new(),
            ne: BTreeMap::new(),
        }
    }

    /// Returns the normalized paper CFG `P`.
    pub fn cfg(&self) -> &Cfg {
        &self.cfg
    }

    /// Returns the query `⟨ϕ_1 ?⇒_P ϕ_2⟩`.
    pub fn query(&self) -> &ReachabilityQuery {
        &self.query
    }

    /// Returns the current region list used as `Π_n`.
    pub fn partition(&self, node: CfgNodeId) -> Option<&[Formula]> {
        self.pi.get(&node).map(Vec::as_slice)
    }

    /// Returns the current accumulated `Ω_n`.
    pub fn omega(&self, node: CfgNodeId) -> Option<&Formula> {
        self.omega.get(&node)
    }

    /// Returns the blocked abstract pairs currently stored in `N_e`.
    pub fn notmay_pairs(&self, edge: CfgEdgeId) -> Option<&[NotMayPair]> {
        self.ne.get(&edge).map(Vec::as_slice)
    }

    fn exit(&self) -> Result<CfgNodeId, RuleError> {
        self.cfg.exit().ok_or(RuleError::MissingExit)
    }

    fn require_partition_membership(
        &self,
        rule: &'static str,
        node: CfgNodeId,
        region: &Formula,
    ) -> Result<(), RuleError> {
        let partition = self
            .pi
            .get(&node)
            .ok_or(RuleError::MissingPartition { node })?;
        if partition.contains(region) {
            Ok(())
        } else {
            Err(RuleError::RegionNotInPartition {
                rule,
                node,
                region: region.clone(),
            })
        }
    }

    fn replace_partition_region(
        &mut self,
        node: CfgNodeId,
        original: &Formula,
        replacements: [Formula; 2],
    ) -> Result<(), RuleError> {
        let partition = self
            .pi
            .get_mut(&node)
            .ok_or(RuleError::MissingPartition { node })?;
        let Some(index) = partition.iter().position(|region| region == original) else {
            return Err(RuleError::RegionNotInPartition {
                rule: "partition-update",
                node,
                region: original.clone(),
            });
        };
        partition.remove(index);
        for replacement in replacements {
            if !partition.contains(&replacement) {
                partition.push(replacement);
            }
        }
        Ok(())
    }

    fn add_notmay_pair(&mut self, edge: CfgEdgeId, pair: NotMayPair) -> Result<(), RuleError> {
        if self.cfg.edge(edge).is_none() {
            return Err(RuleError::UnknownEdge { edge });
        }
        let pairs = self.ne.entry(edge).or_default();
        if !pairs.contains(&pair) {
            pairs.push(pair);
        }
        Ok(())
    }

    fn require_notmay_pair(
        &self,
        rule: &'static str,
        edge: CfgEdgeId,
        pair: &NotMayPair,
    ) -> Result<(), RuleError> {
        let pairs = self.ne.get(&edge).ok_or(RuleError::UnknownEdge { edge })?;
        if pairs.contains(pair) {
            Ok(())
        } else {
            Err(RuleError::MissingNotMayPair {
                rule,
                edge,
                pair: pair.clone(),
            })
        }
    }

    fn set_omega(&mut self, node: CfgNodeId, region: Formula) -> Result<(), RuleError> {
        if self.cfg.node(node).is_none() {
            return Err(RuleError::UnknownNode { node });
        }
        self.omega.insert(node, region);
        Ok(())
    }

    fn add_to_omega(&mut self, node: CfgNodeId, region: Formula) -> Result<(), RuleError> {
        if self.cfg.node(node).is_none() {
            return Err(RuleError::UnknownNode { node });
        }
        self.omega
            .entry(node)
            .and_modify(|current| *current = Formula::or(current.clone(), region.clone()))
            .or_insert(region);
        Ok(())
    }

    fn omega_or_empty(&self, node: CfgNodeId) -> Formula {
        self.omega.get(&node).cloned().unwrap_or(Formula::False)
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum RuleError {
    #[error("missing normalized exit node")]
    MissingExit,
    #[error("unknown CFG node {node:?}")]
    UnknownNode { node: CfgNodeId },
    #[error("unknown CFG edge {edge:?}")]
    UnknownEdge { edge: CfgEdgeId },
    #[error("missing partition for node {node:?}")]
    MissingPartition { node: CfgNodeId },
    #[error("rule {rule} requires region {region} in Π_{node:?}")]
    RegionNotInPartition {
        rule: &'static str,
        node: CfgNodeId,
        region: Formula,
    },
    #[error("rule {rule} requires pair {pair:?} in N_{edge:?}")]
    MissingNotMayPair {
        rule: &'static str,
        edge: CfgEdgeId,
        pair: NotMayPair,
    },
    #[error("rule {rule} premise not satisfied: {premise}")]
    PremiseNotSatisfied { rule: &'static str, premise: String },
    #[error("rule {rule} premise unknown: {premise}")]
    PremiseUnknown { rule: &'static str, premise: String },
    #[error(transparent)]
    Oracle(#[from] OracleError),
}

#[allow(non_snake_case)]
pub mod figure5 {
    use super::*;

    /// Figure 5 `INIT-PI-NE`.
    ///
    /// Initializes every non-exit partition to `[true]`, initializes the exit
    /// partition to `[ϕ_2, ¬ϕ_2]`, and clears all `N_e`.
    pub fn INIT_PI_NE(frame: &mut ProcedureFrame) -> Result<(), RuleError> {
        frame.pi.clear();
        frame.ne.clear();

        let exit = frame.exit()?;
        let nodes = frame.cfg.nodes().keys().copied().collect::<Vec<_>>();
        for node in nodes {
            let regions = if node == exit {
                vec![
                    frame.query.postcondition.clone(),
                    Formula::not(frame.query.postcondition.clone()),
                ]
            } else {
                vec![Formula::True]
            };
            frame.pi.insert(node, regions);
        }

        let edges = frame.cfg.edges().keys().copied().collect::<Vec<_>>();
        for edge in edges {
            frame.ne.insert(edge, Vec::new());
        }

        Ok(())
    }

    /// Figure 5 `NOTMAY-PRE`.
    ///
    /// This is the backward partition-splitting rule. The caller supplies `θ`
    /// as the paper-side `Pre` candidate. The rule:
    ///
    /// - checks that `ϕ_1 ∈ Π_n1` and `ϕ_2 ∈ Π_n2`
    /// - replaces `ϕ_1` by `ϕ_1 ∧ θ` and `ϕ_1 ∧ ¬θ`
    /// - adds `(ϕ_1 ∧ ¬θ, ϕ_2)` to `N_e`
    pub fn NOTMAY_PRE(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        theta: Formula,
    ) -> Result<(), RuleError> {
        let (source, target) = {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            (cfg_edge.source, cfg_edge.target)
        };
        frame.require_partition_membership("NOTMAY-PRE", source, phi_1)?;
        frame.require_partition_membership("NOTMAY-PRE", target, phi_2)?;
        let blocked_pre = Formula::and(phi_1.clone(), Formula::not(theta.clone()));

        frame.replace_partition_region(
            source,
            phi_1,
            [
                Formula::and(phi_1.clone(), theta.clone()),
                blocked_pre.clone(),
            ],
        )?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: blocked_pre,
                post_region: phi_2.clone(),
            },
        )?;

        Ok(())
    }

    /// Figure 5 `IMPL-LEFT`.
    ///
    /// If `(ϕ_1, ϕ_2) ∈ N_e` and `ϕ'_1 ⊆ ϕ_1`, then `(ϕ'_1, ϕ_2)` may also be
    /// recorded in `N_e`.
    pub fn IMPL_LEFT(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        phi_prime_1: &Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        frame.require_notmay_pair(
            "IMPL-LEFT",
            edge,
            &NotMayPair {
                pre_region: phi_1.clone(),
                post_region: phi_2.clone(),
            },
        )?;
        require_subset("IMPL-LEFT", "ϕ'_1 ⊆ ϕ1", oracle, phi_prime_1, phi_1)?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: phi_prime_1.clone(),
                post_region: phi_2.clone(),
            },
        )
    }

    /// Figure 5 `IMPL-RIGHT`.
    ///
    /// If `(ϕ_1, ϕ_2) ∈ N_e` and `ϕ'_2 ⊆ ϕ_2`, then `(ϕ_1, ϕ'_2)` may also be
    /// recorded in `N_e`.
    pub fn IMPL_RIGHT(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        phi_prime_2: &Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        frame.require_notmay_pair(
            "IMPL-RIGHT",
            edge,
            &NotMayPair {
                pre_region: phi_1.clone(),
                post_region: phi_2.clone(),
            },
        )?;
        require_subset("IMPL-RIGHT", "ϕ'_2 ⊆ ϕ2", oracle, phi_prime_2, phi_2)?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: phi_1.clone(),
                post_region: phi_prime_2.clone(),
            },
        )
    }

    /// Figure 5 `VERIFIED`.
    ///
    /// The current implementation checks whether any abstract path remains from
    /// an entry partition region overlapping `ϕ_1` to an exit partition region
    /// overlapping `ϕ_2`. If none remain, the query is verified as `No`.
    ///
    /// If at least one path still exists, the rule reports `Unknown` rather
    /// than making a stronger claim.
    pub fn VERIFIED(frame: &ProcedureFrame, oracle: &Oracle) -> Result<QueryJudgement, RuleError> {
        if abstract_path_exists(frame, oracle)? {
            Ok(QueryJudgement::Unknown)
        } else {
            Ok(QueryJudgement::No)
        }
    }
}

#[allow(non_snake_case)]
pub mod figure6 {
    use super::*;

    /// Figure 6 `INIT-OMEGA`.
    ///
    /// Initializes `Ω_entry = ϕ_1` and every other `Ω_n = false`.
    pub fn INIT_OMEGA(frame: &mut ProcedureFrame) -> Result<(), RuleError> {
        frame.omega.clear();
        let entry = frame.cfg.entry();
        let nodes = frame.cfg.nodes().keys().copied().collect::<Vec<_>>();
        for node in nodes {
            let region = if node == entry {
                frame.query.precondition.clone()
            } else {
                Formula::False
            };
            frame.set_omega(node, region)?;
        }
        Ok(())
    }

    /// Figure 6 `MUST-POST`.
    ///
    /// The caller provides `θ` as a forward `Post` candidate. The rule adds
    /// `θ` into `Ω_n2`.
    pub fn MUST_POST(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        theta: Formula,
    ) -> Result<(), RuleError> {
        let target = frame
            .cfg
            .edge(edge)
            .ok_or(RuleError::UnknownEdge { edge })?
            .target;
        frame.add_to_omega(target, theta)
    }

    /// Figure 6 `BUGFOUND`.
    ///
    /// Checks feasibility of `Ω_exit ∧ ϕ_2`. If feasible, a witness to the
    /// query exists and the judgement is `Yes`. Otherwise the figure only
    /// supports `Unknown`.
    pub fn BUGFOUND(frame: &ProcedureFrame, oracle: &Oracle) -> Result<QueryJudgement, RuleError> {
        let exit = frame.exit()?;
        match oracle.feasibility(&Formula::and(
            frame.omega_or_empty(exit),
            frame.query.postcondition.clone(),
        ))? {
            Feasibility::Feasible => Ok(QueryJudgement::Yes),
            Feasibility::Infeasible | Feasibility::Unknown => Ok(QueryJudgement::Unknown),
        }
    }
}

#[allow(non_snake_case)]
pub mod figure7 {
    use super::*;

    /// Figure 7 combined `MUST-POST`.
    ///
    /// This is the refined must-side rule that uses both `Π_n` and `Ω_n`.
    /// Membership, overlap, and disjointness premises are checked exactly as
    /// solver queries through [`Oracle`].
    pub fn MUST_POST(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        theta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let (source, target) = {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            (cfg_edge.source, cfg_edge.target)
        };
        frame.require_partition_membership("MUST-POST", source, phi_1)?;
        frame.require_partition_membership("MUST-POST", target, phi_2)?;

        require_overlap(
            "MUST-POST",
            "Ω_n1 ∩ ϕ1 ≠ {}",
            oracle,
            &frame.omega_or_empty(source),
            phi_1,
        )?;
        require_disjoint(
            "MUST-POST",
            "Ω_n2 ∩ ϕ2 = {}",
            oracle,
            &frame.omega_or_empty(target),
            phi_2,
        )?;
        require_overlap("MUST-POST", "ϕ2 ∩ θ ≠ {}", oracle, phi_2, &theta)?;

        frame.add_to_omega(target, theta)
    }

    /// Figure 7 combined `NOTMAY-PRE`.
    ///
    /// This is the refined not-may rule that uses both `Π_n` and `Ω_n`. The
    /// caller supplies `β` directly. If the premises hold, the source region is
    /// split into `ϕ_1 ∧ β` and `ϕ_1 ∧ ¬β`, and `(ϕ_1 ∧ ¬β, ϕ_2)` is inserted
    /// into `N_e`.
    pub fn NOTMAY_PRE(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        beta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let (source, target) = {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            (cfg_edge.source, cfg_edge.target)
        };
        frame.require_partition_membership("NOTMAY-PRE", source, phi_1)?;
        frame.require_partition_membership("NOTMAY-PRE", target, phi_2)?;

        require_overlap(
            "NOTMAY-PRE",
            "Ω_n1 ∩ ϕ1 ≠ {}",
            oracle,
            &frame.omega_or_empty(source),
            phi_1,
        )?;
        require_disjoint(
            "NOTMAY-PRE",
            "Ω_n2 ∩ ϕ2 = {}",
            oracle,
            &frame.omega_or_empty(target),
            phi_2,
        )?;
        require_disjoint(
            "NOTMAY-PRE",
            "β ∩ Ω_n1 = {}",
            oracle,
            &beta,
            &frame.omega_or_empty(source),
        )?;

        let blocked_pre = Formula::and(phi_1.clone(), Formula::not(beta.clone()));
        frame.replace_partition_region(
            source,
            phi_1,
            [Formula::and(phi_1.clone(), beta), blocked_pre.clone()],
        )?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: blocked_pre,
                post_region: phi_2.clone(),
            },
        )
    }
}

#[allow(non_snake_case)]
pub mod figure8 {
    use super::*;

    /// Figure 8 `INIT-NOTMAYSUM`.
    pub fn INIT_NOTMAYSUM(summaries: &mut SummaryTables, procedure: impl Into<ProcedureName>) {
        summaries.init_notmay(procedure);
    }

    /// Figure 8 `NOTMAY-PRE-USESUMMARY`.
    ///
    /// Reuses one not-may summary by checking the paper subset premises and
    /// then applying the same split-and-block shape as the local backward rule.
    pub fn NOTMAY_PRE_USESUMMARY(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        summary: &NotMaySummary,
        theta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let source = frame
            .cfg
            .edge(edge)
            .ok_or(RuleError::UnknownEdge { edge })?
            .source;
        let target = frame
            .cfg
            .edge(edge)
            .ok_or(RuleError::UnknownEdge { edge })?
            .target;
        frame.require_partition_membership("NOTMAY-PRE-USESUMMARY", source, phi_1)?;
        frame.require_partition_membership("NOTMAY-PRE-USESUMMARY", target, phi_2)?;

        require_subset(
            "NOTMAY-PRE-USESUMMARY",
            "ϕ2 ⊆ ϕ̂2",
            oracle,
            phi_2,
            &summary.postcondition,
        )?;
        require_subset(
            "NOTMAY-PRE-USESUMMARY",
            "θ ⊆ ϕ̂1",
            oracle,
            &theta,
            &summary.precondition,
        )?;

        let blocked_pre = Formula::and(phi_1.clone(), theta.clone());
        frame.replace_partition_region(
            source,
            phi_1,
            [
                blocked_pre.clone(),
                Formula::and(phi_1.clone(), Formula::not(theta)),
            ],
        )?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: blocked_pre,
                post_region: phi_2.clone(),
            },
        )
    }

    /// Figure 8 `MAY-CALL`.
    ///
    /// Produces the callee subquery directly in paper form.
    pub fn MAY_CALL(
        callee: impl Into<ProcedureName>,
        phi_1: Formula,
        phi_2: Formula,
    ) -> ReachabilityQuery {
        ReachabilityQuery::new(callee, phi_1, phi_2)
    }

    /// Figure 8 `CREATE-NOTMAYSUMMARY`.
    ///
    /// The summary is created only when all entry-to-exit abstract paths are
    /// already blocked. Entry and exit summary regions are formed by collecting
    /// partition members that overlap the query pre/post and then disjoining
    /// them. `project_locals` stands in for the paper's local-variable
    /// projection `∃V^L`.
    pub fn CREATE_NOTMAYSUMMARY<P>(
        frame: &ProcedureFrame,
        summaries: &mut SummaryTables,
        project_locals: P,
        oracle: &Oracle,
    ) -> Result<(), RuleError>
    where
        P: Fn(&Formula) -> Formula,
    {
        if abstract_path_exists(frame, oracle)? {
            return Err(RuleError::PremiseNotSatisfied {
                rule: "CREATE-NOTMAYSUMMARY",
                premise: "all entry-to-exit abstract paths are blocked".to_string(),
            });
        }

        let entry_regions = overlapping_partition_regions(
            frame,
            frame.cfg.entry(),
            &frame.query.precondition,
            oracle,
        )?;
        let exit_regions = overlapping_partition_regions(
            frame,
            frame.exit()?,
            &frame.query.postcondition,
            oracle,
        )?;

        let psi_1 = Formula::or_all(entry_regions);
        let psi_2 = Formula::or_all(exit_regions);
        summaries.add_notmay(
            frame.query.procedure.clone(),
            NotMaySummary {
                precondition: project_locals(&psi_1),
                postcondition: project_locals(&psi_2),
            },
        );
        Ok(())
    }

    /// Figure 8 `MERGE-MAYSUMMARY`.
    ///
    /// Merges two not-may summaries with the same postcondition by disjoining
    /// their preconditions.
    pub fn MERGE_MAYSUMMARY(
        summaries: &mut SummaryTables,
        procedure: &str,
        left: &NotMaySummary,
        right: &NotMaySummary,
    ) -> Result<(), RuleError> {
        if left.postcondition != right.postcondition {
            return Err(RuleError::PremiseNotSatisfied {
                rule: "MERGE-MAYSUMMARY",
                premise: "(ϕ1, ϕ) and (ϕ2, ϕ) must share the same postcondition".to_string(),
            });
        }
        summaries.add_notmay(
            procedure.to_string(),
            NotMaySummary {
                precondition: Formula::or(left.precondition.clone(), right.precondition.clone()),
                postcondition: left.postcondition.clone(),
            },
        );
        Ok(())
    }
}

#[allow(non_snake_case)]
pub mod figure9 {
    use super::*;

    /// Figure 9 `INIT-MUSTSUMMARY`.
    pub fn INIT_MUSTSUMMARY(summaries: &mut SummaryTables, procedure: impl Into<ProcedureName>) {
        summaries.init_must(procedure);
    }

    /// Figure 9 `MUST-POST-USESUMMARY`.
    ///
    /// Reuses one must summary by checking the paper subset premises and then
    /// adding `θ` into `Ω_n2`.
    pub fn MUST_POST_USESUMMARY(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        summary: &MustSummary,
        theta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let (source, target) = {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            (cfg_edge.source, cfg_edge.target)
        };
        require_subset(
            "MUST-POST-USESUMMARY",
            "ϕ1 ⊆ Ω_n1",
            oracle,
            &summary.precondition,
            &frame.omega_or_empty(source),
        )?;
        require_subset(
            "MUST-POST-USESUMMARY",
            "θ ⊆ ϕ2",
            oracle,
            &theta,
            &summary.postcondition,
        )?;
        frame.add_to_omega(target, theta)
    }

    /// Figure 9 `MUST-CALL`.
    ///
    /// Produces the callee subquery directly from `Ω_n1` and `σ_Π`.
    pub fn MUST_CALL(
        callee: impl Into<ProcedureName>,
        omega_n1: Formula,
        sigma_pi: Formula,
    ) -> ReachabilityQuery {
        ReachabilityQuery::new(callee, omega_n1, sigma_pi)
    }

    /// Figure 9 `CREATE-MUSTSUMMARY`.
    ///
    /// Projects the current exit must-region and stores a summary when it still
    /// overlaps the query postcondition.
    pub fn CREATE_MUSTSUMMARY<P>(
        frame: &ProcedureFrame,
        summaries: &mut SummaryTables,
        project_locals: P,
        oracle: &Oracle,
    ) -> Result<(), RuleError>
    where
        P: Fn(&Formula) -> Formula,
    {
        let theta = project_locals(&frame.omega_or_empty(frame.exit()?));
        require_overlap(
            "CREATE-MUSTSUMMARY",
            "θ ∩ ϕ̂2 ≠ {}",
            oracle,
            &theta,
            &frame.query.postcondition,
        )?;
        summaries.add_must(
            frame.query.procedure.clone(),
            MustSummary {
                precondition: frame.query.precondition.clone(),
                postcondition: theta,
            },
        );
        Ok(())
    }

    /// Figure 9 `MERGE-MUSTSUMMARY`.
    ///
    /// Merges two must summaries with the same precondition by disjoining
    /// their postconditions.
    pub fn MERGE_MUSTSUMMARY(
        summaries: &mut SummaryTables,
        procedure: &str,
        left: &MustSummary,
        right: &MustSummary,
    ) -> Result<(), RuleError> {
        if left.precondition != right.precondition {
            return Err(RuleError::PremiseNotSatisfied {
                rule: "MERGE-MUSTSUMMARY",
                premise: "(ϕ, ϕ1) and (ϕ, ϕ2) must share the same precondition".to_string(),
            });
        }
        summaries.add_must(
            procedure.to_string(),
            MustSummary {
                precondition: left.precondition.clone(),
                postcondition: Formula::or(left.postcondition.clone(), right.postcondition.clone()),
            },
        );
        Ok(())
    }
}

#[allow(non_snake_case)]
pub mod figure10 {
    use super::*;

    /// Figure 10 `MUST-POST-USESUMMARY`.
    ///
    /// This is the combined must-side summary rule. It checks partition
    /// membership, must-overlap/disjointness, summary subset premises, and
    /// overlap of the target region with `θ`.
    pub fn MUST_POST_USESUMMARY(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        summary: &MustSummary,
        theta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let (source, target) = {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            (cfg_edge.source, cfg_edge.target)
        };
        frame.require_partition_membership("MUST-POST-USESUMMARY", source, phi_1)?;
        frame.require_partition_membership("MUST-POST-USESUMMARY", target, phi_2)?;
        require_overlap(
            "MUST-POST-USESUMMARY",
            "ϕ1 ∩ Ω_n1 ≠ {}",
            oracle,
            phi_1,
            &frame.omega_or_empty(source),
        )?;
        require_disjoint(
            "MUST-POST-USESUMMARY",
            "ϕ2 ∩ Ω_n2 = {}",
            oracle,
            phi_2,
            &frame.omega_or_empty(target),
        )?;
        require_subset(
            "MUST-POST-USESUMMARY",
            "ϕ1 ∩ Ω_n1 ⊆ ϕ̂1",
            oracle,
            &Formula::and(phi_1.clone(), frame.omega_or_empty(source)),
            &summary.precondition,
        )?;
        require_subset(
            "MUST-POST-USESUMMARY",
            "θ ⊆ ϕ̂2",
            oracle,
            &theta,
            &summary.postcondition,
        )?;
        require_overlap("MUST-POST-USESUMMARY", "ϕ2 ∩ θ ≠ {}", oracle, phi_2, &theta)?;
        frame.add_to_omega(target, theta)
    }

    /// Figure 10 `NOTMAY-PRE-USESUMMARY`.
    ///
    /// This is the combined not-may summary rule. It checks summary premises
    /// plus the must-side exclusion premise `¬θ ∩ Ω_n1 = {}`, then performs the
    /// same partition split and `N_e` update shape as the local not-may rules.
    pub fn NOTMAY_PRE_USESUMMARY(
        frame: &mut ProcedureFrame,
        edge: CfgEdgeId,
        phi_1: &Formula,
        phi_2: &Formula,
        summary: &NotMaySummary,
        theta: Formula,
        oracle: &Oracle,
    ) -> Result<(), RuleError> {
        let source = frame
            .cfg
            .edge(edge)
            .ok_or(RuleError::UnknownEdge { edge })?
            .source;
        let target = frame
            .cfg
            .edge(edge)
            .ok_or(RuleError::UnknownEdge { edge })?
            .target;
        frame.require_partition_membership("NOTMAY-PRE-USESUMMARY", source, phi_1)?;
        frame.require_partition_membership("NOTMAY-PRE-USESUMMARY", target, phi_2)?;
        require_subset(
            "NOTMAY-PRE-USESUMMARY",
            "ϕ2 ⊆ ϕ̂2",
            oracle,
            phi_2,
            &summary.postcondition,
        )?;
        require_subset(
            "NOTMAY-PRE-USESUMMARY",
            "θ ⊆ ϕ̂1",
            oracle,
            &theta,
            &summary.precondition,
        )?;
        require_disjoint(
            "NOTMAY-PRE-USESUMMARY",
            "¬θ ∩ Ω_n1 = {}",
            oracle,
            &Formula::not(theta.clone()),
            &frame.omega_or_empty(source),
        )?;

        let blocked_pre = Formula::and(phi_1.clone(), theta.clone());
        frame.replace_partition_region(
            source,
            phi_1,
            [
                blocked_pre.clone(),
                Formula::and(phi_1.clone(), Formula::not(theta)),
            ],
        )?;
        frame.add_notmay_pair(
            edge,
            NotMayPair {
                pre_region: blocked_pre,
                post_region: phi_2.clone(),
            },
        )
    }

    /// Figure 10 `MAY-MUST-CALL`.
    ///
    /// Builds the mixed query for a call edge after confirming the caller-side
    /// may/must premises.
    pub fn MAY_MUST_CALL(
        callee: impl Into<ProcedureName>,
        phi_1: &Formula,
        phi_2: &Formula,
        omega_n1: &Formula,
        omega_n2: &Formula,
        oracle: &Oracle,
    ) -> Result<ReachabilityQuery, RuleError> {
        require_overlap("MAY-MUST-CALL", "ϕ1 ∩ Ω_n1 ≠ {}", oracle, phi_1, omega_n1)?;
        require_disjoint("MAY-MUST-CALL", "ϕ2 ∩ Ω_n2 = {}", oracle, phi_2, omega_n2)?;

        Ok(ReachabilityQuery::new(
            callee,
            Formula::and(phi_1.clone(), omega_n1.clone()),
            phi_2.clone(),
        ))
    }
}

/// Checks a paper premise of the form `lhs ⊆ rhs`.
fn require_subset(
    rule: &'static str,
    premise: &str,
    oracle: &Oracle,
    lhs: &Formula,
    rhs: &Formula,
) -> Result<(), RuleError> {
    match oracle.implies(lhs, rhs)? {
        Validity::Valid => Ok(()),
        Validity::Invalid => Err(RuleError::PremiseNotSatisfied {
            rule,
            premise: premise.to_string(),
        }),
        Validity::Unknown => Err(RuleError::PremiseUnknown {
            rule,
            premise: premise.to_string(),
        }),
    }
}

/// Checks a paper premise of the form `lhs ∩ rhs ≠ {}`.
fn require_overlap(
    rule: &'static str,
    premise: &str,
    oracle: &Oracle,
    lhs: &Formula,
    rhs: &Formula,
) -> Result<(), RuleError> {
    match oracle.feasibility(&Formula::and(lhs.clone(), rhs.clone()))? {
        Feasibility::Feasible => Ok(()),
        Feasibility::Infeasible => Err(RuleError::PremiseNotSatisfied {
            rule,
            premise: premise.to_string(),
        }),
        Feasibility::Unknown => Err(RuleError::PremiseUnknown {
            rule,
            premise: premise.to_string(),
        }),
    }
}

/// Checks a paper premise of the form `lhs ∩ rhs = {}`.
fn require_disjoint(
    rule: &'static str,
    premise: &str,
    oracle: &Oracle,
    lhs: &Formula,
    rhs: &Formula,
) -> Result<(), RuleError> {
    match oracle.feasibility(&Formula::and(lhs.clone(), rhs.clone()))? {
        Feasibility::Infeasible => Ok(()),
        Feasibility::Feasible => Err(RuleError::PremiseNotSatisfied {
            rule,
            premise: premise.to_string(),
        }),
        Feasibility::Unknown => Err(RuleError::PremiseUnknown {
            rule,
            premise: premise.to_string(),
        }),
    }
}

fn may_overlap(oracle: &Oracle, lhs: &Formula, rhs: &Formula) -> Result<bool, RuleError> {
    // APPROX_HEAVY: if SMT returns Unknown, this helper treats the regions as
    // possibly overlapping so that path-blocking checks stay conservative.
    Ok(
        match oracle.feasibility(&Formula::and(lhs.clone(), rhs.clone()))? {
            Feasibility::Infeasible => false,
            Feasibility::Feasible | Feasibility::Unknown => true,
        },
    )
}

/// Returns all members of `Π_n` that may overlap a target region.
fn overlapping_partition_regions(
    frame: &ProcedureFrame,
    node: CfgNodeId,
    target: &Formula,
    oracle: &Oracle,
) -> Result<Vec<Formula>, RuleError> {
    let partition = frame
        .partition(node)
        .ok_or(RuleError::MissingPartition { node })?;
    let mut regions = Vec::new();
    for region in partition {
        if may_overlap(oracle, region, target)? {
            regions.push(region.clone());
        }
    }
    Ok(regions)
}

/// Conservative abstract-path search used by `VERIFIED` and
/// `CREATE_NOTMAYSUMMARY`.
///
/// Nodes in the search graph are `(node, region-index)` pairs. An abstract edge
/// is blocked only when the exact `(ϕ_1, ϕ_2)` pair has been stored in `N_e`.
/// Any solver `Unknown` in overlap checks is treated as "path may exist".
fn abstract_path_exists(frame: &ProcedureFrame, oracle: &Oracle) -> Result<bool, RuleError> {
    let entry = frame.cfg.entry();
    let exit = frame.exit()?;
    let start_partition = frame
        .partition(entry)
        .ok_or(RuleError::MissingPartition { node: entry })?;
    let exit_partition = frame
        .partition(exit)
        .ok_or(RuleError::MissingPartition { node: exit })?;

    let mut starts = Vec::new();
    for (index, region) in start_partition.iter().enumerate() {
        if may_overlap(oracle, region, &frame.query.precondition)? {
            starts.push((entry, index));
        }
    }

    let mut goals = BTreeSet::new();
    for (index, region) in exit_partition.iter().enumerate() {
        if may_overlap(oracle, region, &frame.query.postcondition)? {
            goals.insert((exit, index));
        }
    }

    if starts.is_empty() || goals.is_empty() {
        return Ok(false);
    }

    let mut queue = VecDeque::from(starts.clone());
    let mut visited = BTreeSet::new();
    while let Some((node, region_index)) = queue.pop_front() {
        if !visited.insert((node, region_index)) {
            continue;
        }
        if goals.contains(&(node, region_index)) {
            return Ok(true);
        }

        let source_region = frame
            .partition(node)
            .ok_or(RuleError::MissingPartition { node })?
            .get(region_index)
            .ok_or(RuleError::PremiseNotSatisfied {
                rule: "abstract-path",
                premise: "partition index out of bounds".to_string(),
            })?
            .clone();

        for edge in frame
            .cfg
            .outgoing_edges(node)
            .map_err(|_| RuleError::UnknownNode { node })?
        {
            let cfg_edge = frame
                .cfg
                .edge(edge)
                .ok_or(RuleError::UnknownEdge { edge })?;
            let target_partition =
                frame
                    .partition(cfg_edge.target)
                    .ok_or(RuleError::MissingPartition {
                        node: cfg_edge.target,
                    })?;
            for (target_index, target_region) in target_partition.iter().enumerate() {
                let blocked = frame.notmay_pairs(edge).unwrap_or(&[]).iter().any(|pair| {
                    pair.pre_region == source_region && pair.post_region == *target_region
                });
                if !blocked {
                    queue.push_back((cfg_edge.target, target_index));
                }
            }
        }
    }

    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cfg() -> ProcedureFrame {
        let mut cfg = Cfg::new("entry");
        let mid = cfg.add_node("mid");
        let exit = cfg.add_node("exit");
        cfg.add_edge(cfg.entry(), mid, Formula::True).unwrap();
        cfg.add_edge(mid, exit, Formula::True).unwrap();
        cfg.mark_exit(exit).unwrap();
        cfg.ensure_single_exit().unwrap();
        ProcedureFrame::new(
            cfg,
            ReachabilityQuery::new("P", Formula::bool_var("pre"), Formula::bool_var("post")),
        )
    }

    #[test]
    fn init_pi_ne_matches_figure_5_shape() {
        let mut frame = test_cfg();
        figure5::INIT_PI_NE(&mut frame).unwrap();
        let exit = frame.cfg().exit().unwrap();
        assert_eq!(
            frame.partition(frame.cfg().entry()).unwrap(),
            &[Formula::True]
        );
        assert_eq!(
            frame.partition(exit).unwrap(),
            &[
                Formula::bool_var("post"),
                Formula::not(Formula::bool_var("post"))
            ]
        );
        assert!(frame
            .notmay_pairs(frame.cfg().edges().keys().next().copied().unwrap())
            .unwrap()
            .is_empty());
    }

    #[test]
    fn figure_5_notmay_pre_splits_and_blocks_an_edge_pair() {
        let oracle = Oracle::new();
        let mut frame = test_cfg();
        figure5::INIT_PI_NE(&mut frame).unwrap();
        let edge = CfgEdgeId(0);
        figure5::NOTMAY_PRE(
            &mut frame,
            edge,
            &Formula::True,
            &Formula::True,
            Formula::bool_var("beta"),
        )
        .unwrap();
        assert_eq!(frame.partition(frame.cfg().entry()).unwrap().len(), 2);
        figure5::IMPL_LEFT(
            &mut frame,
            edge,
            &Formula::and(Formula::True, Formula::not(Formula::bool_var("beta"))),
            &Formula::True,
            &Formula::False,
            &oracle,
        )
        .unwrap();
    }

    #[test]
    fn verified_returns_no_when_all_abstract_paths_are_blocked() {
        let oracle = Oracle::new();
        let mut frame = test_cfg();
        figure5::INIT_PI_NE(&mut frame).unwrap();
        let first = CfgEdgeId(0);
        let second = CfgEdgeId(1);
        frame
            .add_notmay_pair(
                first,
                NotMayPair {
                    pre_region: Formula::True,
                    post_region: Formula::True,
                },
            )
            .unwrap();
        frame
            .add_notmay_pair(
                second,
                NotMayPair {
                    pre_region: Formula::True,
                    post_region: Formula::bool_var("post"),
                },
            )
            .unwrap();
        assert_eq!(
            figure5::VERIFIED(&frame, &oracle).unwrap(),
            QueryJudgement::No
        );
    }

    #[test]
    fn init_omega_and_bugfound_follow_figure_6() {
        let oracle = Oracle::new();
        let mut frame = test_cfg();
        figure6::INIT_OMEGA(&mut frame).unwrap();
        let edge0 = CfgEdgeId(0);
        let edge1 = CfgEdgeId(1);
        figure6::MUST_POST(&mut frame, edge0, Formula::bool_var("pre")).unwrap();
        figure6::MUST_POST(&mut frame, edge1, Formula::bool_var("post")).unwrap();
        assert_eq!(
            figure6::BUGFOUND(&frame, &oracle).unwrap(),
            QueryJudgement::Yes
        );
    }

    #[test]
    fn figure_7_rules_use_partitions_and_omega_together() {
        let oracle = Oracle::new();
        let mut must_frame = test_cfg();
        figure5::INIT_PI_NE(&mut must_frame).unwrap();
        figure6::INIT_OMEGA(&mut must_frame).unwrap();
        let edge = CfgEdgeId(0);
        figure7::MUST_POST(
            &mut must_frame,
            edge,
            &Formula::True,
            &Formula::True,
            Formula::bool_var("witness"),
            &oracle,
        )
        .unwrap();

        let mut notmay_frame = test_cfg();
        figure5::INIT_PI_NE(&mut notmay_frame).unwrap();
        figure6::INIT_OMEGA(&mut notmay_frame).unwrap();
        figure7::NOTMAY_PRE(
            &mut notmay_frame,
            edge,
            &Formula::True,
            &Formula::True,
            Formula::not(Formula::bool_var("pre")),
            &oracle,
        )
        .unwrap();
        assert!(notmay_frame.notmay_pairs(edge).unwrap().len() >= 1);
    }

    #[test]
    fn figure_8_summary_rules_create_and_merge_notmay_summaries() {
        let oracle = Oracle::new();
        let mut frame = test_cfg();
        let mut summaries = SummaryTables::new();
        figure5::INIT_PI_NE(&mut frame).unwrap();
        figure8::INIT_NOTMAYSUM(&mut summaries, "P");
        frame
            .add_notmay_pair(
                CfgEdgeId(0),
                NotMayPair {
                    pre_region: Formula::True,
                    post_region: Formula::True,
                },
            )
            .unwrap();
        frame
            .add_notmay_pair(
                CfgEdgeId(1),
                NotMayPair {
                    pre_region: Formula::True,
                    post_region: Formula::bool_var("post"),
                },
            )
            .unwrap();
        figure8::CREATE_NOTMAYSUMMARY(&frame, &mut summaries, |formula| formula.clone(), &oracle)
            .unwrap();
        let first = summaries.notmay("P")[0].clone();
        figure8::MERGE_MAYSUMMARY(&mut summaries, "P", &first, &first).unwrap();
        assert!(!summaries.notmay("P").is_empty());
    }

    #[test]
    fn figure_9_summary_rules_create_and_merge_must_summaries() {
        let oracle = Oracle::new();
        let mut frame = test_cfg();
        let mut summaries = SummaryTables::new();
        figure6::INIT_OMEGA(&mut frame).unwrap();
        figure9::INIT_MUSTSUMMARY(&mut summaries, "P");
        figure6::MUST_POST(&mut frame, CfgEdgeId(0), Formula::bool_var("pre")).unwrap();
        figure6::MUST_POST(&mut frame, CfgEdgeId(1), Formula::bool_var("post")).unwrap();
        figure9::CREATE_MUSTSUMMARY(&frame, &mut summaries, |formula| formula.clone(), &oracle)
            .unwrap();
        let first = summaries.must("P")[0].clone();
        figure9::MERGE_MUSTSUMMARY(&mut summaries, "P", &first, &first).unwrap();
        assert!(!summaries.must("P").is_empty());
    }

    #[test]
    fn figure_10_may_must_call_shapes_the_subquery_like_the_paper() {
        let oracle = Oracle::new();
        let query = figure10::MAY_MUST_CALL(
            "callee",
            &Formula::True,
            &Formula::bool_var("goal"),
            &Formula::bool_var("reachable"),
            &Formula::False,
            &oracle,
        )
        .unwrap();
        assert_eq!(query.procedure, "callee");
        assert_eq!(
            query.precondition,
            Formula::and(Formula::True, Formula::bool_var("reachable"))
        );
        assert_eq!(query.postcondition, Formula::bool_var("goal"));
    }

    #[test]
    fn may_and_must_call_rules_return_paper_shaped_queries() {
        let may = figure8::MAY_CALL("callee", Formula::bool_var("a"), Formula::bool_var("b"));
        let must = figure9::MUST_CALL("callee", Formula::bool_var("omega"), Formula::True);

        assert_eq!(may.procedure, "callee");
        assert_eq!(may.precondition, Formula::bool_var("a"));
        assert_eq!(may.postcondition, Formula::bool_var("b"));
        assert_eq!(must.precondition, Formula::bool_var("omega"));
        assert_eq!(must.postcondition, Formula::True);
    }
}
