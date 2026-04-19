//! Intraprocedural orchestration for the paper-shaped rules.
//!
//! This module now has two layers:
//!
//! - top-level summary reuse through `PaperDriver`;
//! - a local worklist over `(edge, source region, destination region)`
//!   obligations for the intraprocedural paper rules.
//!
//! Paper correspondence:
//!
//! ```text
//! PaperDriver::answer_from_summaries -> summary applicability stage
//! run_intraprocedural                -> local rule engine over P
//! worklist item                      -> (e, phi1, phi2)
//! MUST-POST step                     -> update Omega_n
//! NOTMAY-PRE step                    -> refine Pi_n and add may edges
//! ```

use crate::analysis::cfg::{PaperEdge, PaperProcedure};
use crate::analysis::formula::Predicate;
use crate::analysis::oracle::{OracleResult, PredicateOracle, TransitionOracle};
use crate::analysis::rules::{
    applicable_must_summary, applicable_not_may_summary, must_post_edge, not_may_pre_edge,
    RuleApplication, RuleConclusion,
};
use crate::analysis::state::{MayEdge, PaperAnalysisState, Partition, Region};
use crate::analysis::summaries::{ReachabilityQuery, SummaryTable};
use crate::analysis::vocabulary::{EdgeId, NodeId, RegionId};
use std::collections::{BTreeSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PaperAnswer {
    Must(RuleApplication),
    NotMay(RuleApplication),
    NeedsIntraproceduralAnalysis,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntraproceduralConfig {
    pub max_obligations: usize,
}

impl Default for IntraproceduralConfig {
    fn default() -> Self {
        Self {
            max_obligations: 10_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EdgeRegionObligation {
    pub edge: EdgeId,
    pub from: NodeId,
    pub to: NodeId,
    pub source_region: RegionId,
    pub dest_region: RegionId,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct IntraproceduralStats {
    pub obligations_processed: usize,
    pub must_steps: usize,
    pub refinement_steps: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntraproceduralResult {
    pub state: PaperAnalysisState,
    pub stats: IntraproceduralStats,
    pub reached_target: bool,
    pub stopped_by_limit: bool,
}

#[derive(Clone, Debug, Default)]
pub struct PaperDriver {
    summaries: SummaryTable,
}

impl PaperDriver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn summaries(&self) -> &SummaryTable {
        &self.summaries
    }

    pub fn summaries_mut(&mut self) -> &mut SummaryTable {
        &mut self.summaries
    }

    /// Deterministic top-level order from the paper discussion:
    ///
    /// 1. reuse an applicable must summary;
    /// 2. reuse an applicable not-may summary;
    /// 3. otherwise run intraprocedural may/must analysis.
    pub fn answer_from_summaries<P>(
        &self,
        predicates: &P,
        query: &ReachabilityQuery,
    ) -> OracleResult<PaperAnswer>
    where
        P: PredicateOracle,
    {
        for summary in self.summaries.for_procedure(&query.procedure) {
            let application = applicable_must_summary(predicates, summary, query)?;
            if application.is_applied() {
                return Ok(PaperAnswer::Must(application));
            }
        }

        for summary in self.summaries.for_procedure(&query.procedure) {
            let application = applicable_not_may_summary(predicates, summary, query)?;
            if application.is_applied() {
                return Ok(PaperAnswer::NotMay(application));
            }
        }

        Ok(PaperAnswer::NeedsIntraproceduralAnalysis)
    }

    /// Executes the first explicit intraprocedural paper loop.
    ///
    /// The worklist unit is an `(edge, source region, destination region)`
    /// obligation. `Omega` growth re-enqueues outgoing obligations from the
    /// destination node. Partition refinement re-enqueues all obligations that
    /// touch the split node because the source or destination region ids may
    /// have changed.
    pub fn run_intraprocedural<P, T>(
        &self,
        predicates: &P,
        transitions: &T,
        procedure: &PaperProcedure,
        query: &ReachabilityQuery,
        config: IntraproceduralConfig,
    ) -> OracleResult<IntraproceduralResult>
    where
        P: PredicateOracle,
        T: TransitionOracle,
    {
        let mut state = initial_state_for_query(procedure, query);
        let mut stats = IntraproceduralStats::default();
        let mut queue = VecDeque::new();
        let mut pending = BTreeSet::new();
        enqueue_all_obligations(procedure, &state, &mut queue, &mut pending);

        while let Some(obligation) = pop_obligation(&mut queue, &mut pending) {
            if stats.obligations_processed >= config.max_obligations {
                return Ok(IntraproceduralResult {
                    reached_target: target_reached(predicates, &state, procedure, query)?,
                    state,
                    stats,
                    stopped_by_limit: true,
                });
            }
            stats.obligations_processed += 1;

            let Some(edge) = procedure.edge(obligation.edge) else {
                continue;
            };
            let Some(source_region) =
                region_predicate(&state, obligation.from, obligation.source_region)
            else {
                continue;
            };
            let Some(dest_region) = region_predicate(&state, obligation.to, obligation.dest_region)
            else {
                continue;
            };

            let omega_n1 = state.omega(obligation.from);
            let omega_n2 = state.omega(obligation.to);

            let must = must_post_edge(
                predicates,
                transitions,
                edge,
                &source_region,
                &dest_region,
                &omega_n1,
                &omega_n2,
            )?;
            if let RuleApplication::Applied {
                conclusion: RuleConclusion::AddOmega { theta },
                ..
            } = must
            {
                state.add_omega(obligation.to, theta);
                stats.must_steps += 1;
                enqueue_outgoing_obligations(
                    procedure,
                    &state,
                    obligation.to,
                    &mut queue,
                    &mut pending,
                );
                if target_reached(predicates, &state, procedure, query)? {
                    return Ok(IntraproceduralResult {
                        reached_target: true,
                        state,
                        stats,
                        stopped_by_limit: false,
                    });
                }
                continue;
            }

            let not_may = not_may_pre_edge(
                predicates,
                transitions,
                edge,
                obligation.source_region,
                obligation.dest_region,
                &source_region,
                &dest_region,
                &omega_n1,
                &omega_n2,
            )?;
            if let RuleApplication::Applied {
                conclusion:
                    RuleConclusion::RefineAndAddMayEdge {
                        keep_region,
                        reject_region,
                        ..
                    },
                ..
            } = not_may
            {
                if apply_refinement(
                    predicates,
                    &mut state,
                    obligation,
                    keep_region,
                    reject_region,
                )? {
                    stats.refinement_steps += 1;
                    enqueue_touching_obligations(
                        procedure,
                        &state,
                        obligation.from,
                        &mut queue,
                        &mut pending,
                    );
                }
            }
        }

        Ok(IntraproceduralResult {
            reached_target: target_reached(predicates, &state, procedure, query)?,
            state,
            stats,
            stopped_by_limit: false,
        })
    }
}

fn initial_state_for_query(
    procedure: &PaperProcedure,
    query: &ReachabilityQuery,
) -> PaperAnalysisState {
    let mut state = PaperAnalysisState::new();
    for &node in &procedure.nodes {
        state.set_partition(node, Partition::top());
        state.set_omega(node, Predicate::False);
    }

    state.set_omega(procedure.entry, query.pre.clone());
    state.set_partition(procedure.exit, target_partition(query.post.clone()));
    state
}

fn target_partition(target: Predicate) -> Partition {
    if target == Predicate::True {
        Partition::top()
    } else {
        Partition::new([
            Region::new(RegionId(0), target.clone()),
            Region::new(RegionId(1), Predicate::not(target)),
        ])
    }
}

fn region_predicate(
    state: &PaperAnalysisState,
    node: NodeId,
    region: RegionId,
) -> Option<Predicate> {
    state
        .partition(node)?
        .region(region)
        .map(|region| region.predicate.clone())
}

fn target_reached<P>(
    predicates: &P,
    state: &PaperAnalysisState,
    procedure: &PaperProcedure,
    query: &ReachabilityQuery,
) -> OracleResult<bool>
where
    P: PredicateOracle,
{
    predicates.intersects(&state.omega(procedure.exit), &query.post)
}

fn apply_refinement<P>(
    predicates: &P,
    state: &mut PaperAnalysisState,
    obligation: EdgeRegionObligation,
    keep_region: Predicate,
    reject_region: Predicate,
) -> OracleResult<bool>
where
    P: PredicateOracle,
{
    if predicates.is_empty(&keep_region)? || predicates.is_empty(&reject_region)? {
        return Ok(false);
    }

    let Some(partition) = state.partition_mut(obligation.from) else {
        return Ok(false);
    };
    let Some((keep_region_id, _reject_region_id)) =
        partition.replace_with_split(obligation.source_region, keep_region, reject_region)
    else {
        return Ok(false);
    };

    state.add_may_edge(MayEdge::new(
        obligation.edge,
        keep_region_id,
        obligation.dest_region,
    ));
    Ok(true)
}

fn pop_obligation(
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
) -> Option<EdgeRegionObligation> {
    let obligation = queue.pop_front()?;
    pending.remove(&obligation);
    Some(obligation)
}

fn enqueue_all_obligations(
    procedure: &PaperProcedure,
    state: &PaperAnalysisState,
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
) {
    for edge in &procedure.edges {
        enqueue_edge_obligations(edge, state, queue, pending);
    }
}

fn enqueue_outgoing_obligations(
    procedure: &PaperProcedure,
    state: &PaperAnalysisState,
    node: NodeId,
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
) {
    for edge in procedure.outgoing_edges(node) {
        enqueue_edge_obligations(edge, state, queue, pending);
    }
}

fn enqueue_touching_obligations(
    procedure: &PaperProcedure,
    state: &PaperAnalysisState,
    node: NodeId,
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
) {
    for edge in procedure.incoming_edges(node) {
        enqueue_edge_obligations(edge, state, queue, pending);
    }
    for edge in procedure.outgoing_edges(node) {
        enqueue_edge_obligations(edge, state, queue, pending);
    }
}

fn enqueue_edge_obligations(
    edge: &PaperEdge,
    state: &PaperAnalysisState,
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
) {
    let Some(source_partition) = state.partition(edge.from) else {
        return;
    };
    let Some(dest_partition) = state.partition(edge.to) else {
        return;
    };

    let source_regions: Vec<_> = source_partition.regions().map(|region| region.id).collect();
    let dest_regions: Vec<_> = dest_partition.regions().map(|region| region.id).collect();

    for source_region in source_regions {
        for dest_region in &dest_regions {
            let obligation = EdgeRegionObligation {
                edge: edge.id,
                from: edge.from,
                to: edge.to,
                source_region,
                dest_region: *dest_region,
            };
            if pending.insert(obligation) {
                queue.push_back(obligation);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::cfg::PaperEdge;
    use crate::analysis::oracle::SyntacticOracle;
    use crate::analysis::vocabulary::{EdgeId, NodeId};

    fn straight_line_procedure(theta: Predicate, beta: Predicate) -> PaperProcedure {
        let mut procedure = PaperProcedure::new("P", NodeId(0), NodeId(1));
        procedure.add_edge(PaperEdge::local(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            Predicate::atom("Gamma_e"),
            Some(theta),
            Some(beta),
        ));
        procedure
    }

    #[test]
    fn intraprocedural_driver_propagates_omega_to_exit() {
        let driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let procedure = straight_line_procedure(Predicate::atom("goal"), Predicate::True);
        let query = ReachabilityQuery::new("P", Predicate::atom("start"), Predicate::atom("goal"));

        let result = driver
            .run_intraprocedural(
                &oracle,
                &oracle,
                &procedure,
                &query,
                IntraproceduralConfig::default(),
            )
            .unwrap();

        assert!(result.reached_target);
        assert_eq!(result.stats.must_steps, 1);
        assert_eq!(result.state.omega(procedure.exit), Predicate::atom("goal"));
    }

    #[test]
    fn intraprocedural_driver_refines_source_partition_and_records_may_edge() {
        let driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let procedure = straight_line_procedure(
            Predicate::not(Predicate::atom("bug")),
            Predicate::not(Predicate::atom("p")),
        );
        let query = ReachabilityQuery::new("P", Predicate::atom("p"), Predicate::atom("bug"));

        let result = driver
            .run_intraprocedural(
                &oracle,
                &oracle,
                &procedure,
                &query,
                IntraproceduralConfig::default(),
            )
            .unwrap();

        assert!(!result.reached_target);
        assert_eq!(result.stats.refinement_steps, 1);
        assert_eq!(
            result
                .state
                .partition(procedure.entry)
                .unwrap()
                .regions()
                .count(),
            2
        );
        assert_eq!(result.state.may_edges().count(), 1);
    }

    #[test]
    fn intraprocedural_driver_reports_limit_stop() {
        let driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let procedure = straight_line_procedure(Predicate::atom("goal"), Predicate::True);
        let query = ReachabilityQuery::new("P", Predicate::atom("start"), Predicate::atom("goal"));

        let result = driver
            .run_intraprocedural(
                &oracle,
                &oracle,
                &procedure,
                &query,
                IntraproceduralConfig { max_obligations: 0 },
            )
            .unwrap();

        assert!(result.stopped_by_limit);
        assert_eq!(result.stats.obligations_processed, 0);
    }
}
