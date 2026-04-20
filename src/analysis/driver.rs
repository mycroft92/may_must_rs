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

use crate::analysis::cfg::{EdgeKind, PaperEdge, PaperProcedure};
use crate::analysis::formula::Predicate;
use crate::analysis::oracle::{OracleResult, PredicateOracle, TransitionOracle};
use crate::analysis::rules::{
    applicable_must_summary, applicable_not_may_summary, create_must_summary,
    create_not_may_summary, must_post_edge, must_post_use_summary, not_may_pre_edge,
    not_may_pre_use_summary, RuleApplication, RuleConclusion,
};
use crate::analysis::state::{MayEdge, PaperAnalysisState, Partition, Region};
use crate::analysis::summaries::{ProcedureSummary, ReachabilityQuery, SummaryTable};
use crate::analysis::vocabulary::{EdgeId, NodeId, ProcedureName, RegionId};
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InterproceduralConfig {
    pub intraprocedural: IntraproceduralConfig,
    pub max_call_depth: usize,
}

impl Default for InterproceduralConfig {
    fn default() -> Self {
        Self {
            intraprocedural: IntraproceduralConfig::default(),
            max_call_depth: 6,
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

pub trait InterproceduralOracleProvider {
    fn procedure(&self, procedure: &ProcedureName) -> Option<&PaperProcedure>;

    fn transitions(
        &self,
        procedure: &ProcedureName,
        target_assertion: Option<EdgeId>,
    ) -> Option<Box<dyn TransitionOracle + '_>>;

    fn project_call_query(
        &self,
        caller_query: &ReachabilityQuery,
        call_edge: &PaperEdge,
        omega_n1: &Predicate,
        source_region: &Predicate,
        dest_region: &Predicate,
    ) -> Option<ReachabilityQuery>;
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

            if let Some(conclusion) = self.call_edge_summary_conclusion(
                predicates,
                edge,
                obligation,
                &source_region,
                &dest_region,
                &omega_n1,
                &omega_n2,
            )? {
                match conclusion {
                    RuleConclusion::AddOmega { theta } => {
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
                    }
                    RuleConclusion::RefineAndAddMayEdge {
                        keep_region,
                        reject_region,
                        ..
                    } => {
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
                    RuleConclusion::ReuseSummary { .. } | RuleConclusion::CreateSummary { .. } => {}
                }
                // If a summary rule applies on a call edge, do not fall back
                // to local-transition rules for the same obligation.
                continue;
            }

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

    pub fn run_interprocedural<P, I>(
        &mut self,
        predicates: &P,
        provider: &I,
        query: &ReachabilityQuery,
        config: InterproceduralConfig,
    ) -> OracleResult<IntraproceduralResult>
    where
        P: PredicateOracle,
        I: InterproceduralOracleProvider,
    {
        let mut call_stack = Vec::new();
        self.run_interprocedural_inner(predicates, provider, query, config, &mut call_stack)
    }

    fn run_interprocedural_inner<P, I>(
        &mut self,
        predicates: &P,
        provider: &I,
        query: &ReachabilityQuery,
        config: InterproceduralConfig,
        call_stack: &mut Vec<ProcedureName>,
    ) -> OracleResult<IntraproceduralResult>
    where
        P: PredicateOracle,
        I: InterproceduralOracleProvider,
    {
        if call_stack.len() >= config.max_call_depth {
            return Ok(unknown_result_for_query(provider, query));
        }
        if call_stack.contains(&query.procedure) {
            return Ok(unknown_result_for_query(provider, query));
        }

        match self.answer_from_summaries(predicates, query)? {
            PaperAnswer::Must(_) => {
                return Ok(reachable_result_for_query(provider, query));
            }
            PaperAnswer::NotMay(_) => {
                return Ok(not_reached_result_for_query(provider, query));
            }
            PaperAnswer::NeedsIntraproceduralAnalysis => {}
        }

        let Some(procedure) = provider.procedure(&query.procedure) else {
            return Ok(unknown_result_for_query(provider, query));
        };
        let Some(transitions) = provider.transitions(&query.procedure, query.target_assertion)
        else {
            return Ok(unknown_result_for_query(provider, query));
        };

        call_stack.push(query.procedure.clone());
        let mut state = initial_state_for_query(procedure, query);
        let mut stats = IntraproceduralStats::default();
        let mut queue = VecDeque::new();
        let mut pending = BTreeSet::new();
        let mut unresolved_internal_call = false;
        enqueue_all_obligations(procedure, &state, &mut queue, &mut pending);

        while let Some(obligation) = pop_obligation(&mut queue, &mut pending) {
            if stats.obligations_processed >= config.intraprocedural.max_obligations {
                let reached = target_reached(predicates, &state, procedure, query)?;
                call_stack.pop();
                return Ok(IntraproceduralResult {
                    reached_target: reached,
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

            if let Some(conclusion) = self.call_edge_summary_conclusion(
                predicates,
                edge,
                obligation,
                &source_region,
                &dest_region,
                &omega_n1,
                &omega_n2,
            )? {
                apply_summary_conclusion(
                    predicates,
                    procedure,
                    query,
                    &mut state,
                    &mut stats,
                    &mut queue,
                    &mut pending,
                    obligation,
                    conclusion,
                )?;
                if target_reached(predicates, &state, procedure, query)? {
                    call_stack.pop();
                    return Ok(IntraproceduralResult {
                        reached_target: true,
                        state,
                        stats,
                        stopped_by_limit: false,
                    });
                }
                continue;
            }
            if let EdgeKind::Call { callee } = &edge.transition.kind {
                // Internal calls are handled compositionally via summaries and
                // may-call recursion. External/unresolved calls still use the
                // transition layer (e.g. direct may_assert effects).
                if provider.procedure(callee).is_some() {
                    if let Some(summary) = self.may_call_summary(
                        predicates,
                        provider,
                        query,
                        edge,
                        &omega_n1,
                        &source_region,
                        &dest_region,
                        config,
                        call_stack,
                    )? {
                        self.summaries.add(summary);
                    }

                    if let Some(conclusion) = self.call_edge_summary_conclusion(
                        predicates,
                        edge,
                        obligation,
                        &source_region,
                        &dest_region,
                        &omega_n1,
                        &omega_n2,
                    )? {
                        apply_summary_conclusion(
                            predicates,
                            procedure,
                            query,
                            &mut state,
                            &mut stats,
                            &mut queue,
                            &mut pending,
                            obligation,
                            conclusion,
                        )?;
                        if target_reached(predicates, &state, procedure, query)? {
                            call_stack.pop();
                            return Ok(IntraproceduralResult {
                                reached_target: true,
                                state,
                                stats,
                                stopped_by_limit: false,
                            });
                        }
                        continue;
                    }

                    unresolved_internal_call = true;
                    continue;
                }
            }

            let must = must_post_edge(
                predicates,
                transitions.as_ref(),
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
                    call_stack.pop();
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
                transitions.as_ref(),
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

        let reached_target = target_reached(predicates, &state, procedure, query)?;
        call_stack.pop();
        Ok(IntraproceduralResult {
            reached_target,
            state,
            stats,
            stopped_by_limit: unresolved_internal_call && !reached_target,
        })
    }

    fn may_call_summary<P, I>(
        &mut self,
        predicates: &P,
        provider: &I,
        caller_query: &ReachabilityQuery,
        edge: &PaperEdge,
        omega_n1: &Predicate,
        source_region: &Predicate,
        dest_region: &Predicate,
        config: InterproceduralConfig,
        call_stack: &mut Vec<ProcedureName>,
    ) -> OracleResult<Option<ProcedureSummary>>
    where
        P: PredicateOracle,
        I: InterproceduralOracleProvider,
    {
        let EdgeKind::Call { callee: _ } = &edge.transition.kind else {
            return Ok(None);
        };

        let Some(callee_query) =
            provider.project_call_query(caller_query, edge, omega_n1, source_region, dest_region)
        else {
            return Ok(None);
        };

        let result = self.run_interprocedural_inner(
            predicates,
            provider,
            &callee_query,
            config,
            call_stack,
        )?;
        if result.reached_target {
            let created = create_must_summary(
                callee_query.procedure.clone(),
                callee_query.pre.clone(),
                callee_query.post.clone(),
                format!("may-call witness via {}", edge.id),
            );
            if let RuleApplication::Applied {
                conclusion: RuleConclusion::CreateSummary { summary },
                ..
            } = created
            {
                return Ok(Some(summary));
            }
        } else if !result.stopped_by_limit {
            let created = create_not_may_summary(
                callee_query.procedure.clone(),
                callee_query.pre.clone(),
                callee_query.post.clone(),
                format!("may-call proof via {}", edge.id),
            );
            if let RuleApplication::Applied {
                conclusion: RuleConclusion::CreateSummary { summary },
                ..
            } = created
            {
                return Ok(Some(summary));
            }
        }

        Ok(None)
    }

    fn call_edge_summary_conclusion<P>(
        &self,
        predicates: &P,
        edge: &PaperEdge,
        obligation: EdgeRegionObligation,
        source_region: &Predicate,
        dest_region: &Predicate,
        omega_n1: &Predicate,
        omega_n2: &Predicate,
    ) -> OracleResult<Option<RuleConclusion>>
    where
        P: PredicateOracle,
    {
        let EdgeKind::Call { callee } = &edge.transition.kind else {
            return Ok(None);
        };

        for summary in self.summaries.for_procedure(callee) {
            let application =
                must_post_use_summary(predicates, summary, dest_region, omega_n1, omega_n2)?;
            if let RuleApplication::Applied { conclusion, .. } = application {
                return Ok(Some(conclusion));
            }
        }

        for summary in self.summaries.for_procedure(callee) {
            let application = not_may_pre_use_summary(
                predicates,
                summary,
                edge.id,
                obligation.source_region,
                obligation.dest_region,
                source_region,
                dest_region,
                omega_n1,
            )?;
            if let RuleApplication::Applied { conclusion, .. } = application {
                return Ok(Some(conclusion));
            }
        }

        Ok(None)
    }
}

fn apply_summary_conclusion<P>(
    predicates: &P,
    procedure: &PaperProcedure,
    query: &ReachabilityQuery,
    state: &mut PaperAnalysisState,
    stats: &mut IntraproceduralStats,
    queue: &mut VecDeque<EdgeRegionObligation>,
    pending: &mut BTreeSet<EdgeRegionObligation>,
    obligation: EdgeRegionObligation,
    conclusion: RuleConclusion,
) -> OracleResult<()>
where
    P: PredicateOracle,
{
    match conclusion {
        RuleConclusion::AddOmega { theta } => {
            state.add_omega(obligation.to, theta);
            stats.must_steps += 1;
            enqueue_outgoing_obligations(procedure, state, obligation.to, queue, pending);
        }
        RuleConclusion::RefineAndAddMayEdge {
            keep_region,
            reject_region,
            ..
        } => {
            if apply_refinement(predicates, state, obligation, keep_region, reject_region)? {
                stats.refinement_steps += 1;
                enqueue_touching_obligations(procedure, state, obligation.from, queue, pending);
            }
        }
        RuleConclusion::ReuseSummary { .. } | RuleConclusion::CreateSummary { .. } => {}
    }

    if target_reached(predicates, state, procedure, query)? {
        return Ok(());
    }
    Ok(())
}

fn unknown_result_for_query<I>(provider: &I, query: &ReachabilityQuery) -> IntraproceduralResult
where
    I: InterproceduralOracleProvider,
{
    let state = provider
        .procedure(&query.procedure)
        .map(|procedure| initial_state_for_query(procedure, query))
        .unwrap_or_default();
    IntraproceduralResult {
        state,
        stats: IntraproceduralStats::default(),
        reached_target: false,
        stopped_by_limit: true,
    }
}

fn reachable_result_for_query<I>(provider: &I, query: &ReachabilityQuery) -> IntraproceduralResult
where
    I: InterproceduralOracleProvider,
{
    let mut state = provider
        .procedure(&query.procedure)
        .map(|procedure| initial_state_for_query(procedure, query))
        .unwrap_or_default();
    if let Some(procedure) = provider.procedure(&query.procedure) {
        state.add_omega(procedure.exit, query.post.clone());
    }
    IntraproceduralResult {
        state,
        stats: IntraproceduralStats::default(),
        reached_target: true,
        stopped_by_limit: false,
    }
}

fn not_reached_result_for_query<I>(provider: &I, query: &ReachabilityQuery) -> IntraproceduralResult
where
    I: InterproceduralOracleProvider,
{
    let state = provider
        .procedure(&query.procedure)
        .map(|procedure| initial_state_for_query(procedure, query))
        .unwrap_or_default();
    IntraproceduralResult {
        state,
        stats: IntraproceduralStats::default(),
        reached_target: false,
        stopped_by_limit: false,
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
    use crate::analysis::summaries::ProcedureSummary;
    use crate::analysis::vocabulary::{EdgeId, NodeId, ProcedureName};
    use std::collections::BTreeMap;

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

    fn call_only_procedure() -> PaperProcedure {
        let mut procedure = PaperProcedure::new("P", NodeId(0), NodeId(1));
        procedure.add_edge(PaperEdge::call(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            "callee",
            Predicate::atom("Gamma_call"),
        ));
        procedure
    }

    #[derive(Clone)]
    struct StaticInterproceduralProvider {
        procedures: BTreeMap<ProcedureName, PaperProcedure>,
    }

    impl InterproceduralOracleProvider for StaticInterproceduralProvider {
        fn procedure(&self, procedure: &ProcedureName) -> Option<&PaperProcedure> {
            self.procedures.get(procedure)
        }

        fn transitions(
            &self,
            _procedure: &ProcedureName,
            _target_assertion: Option<EdgeId>,
        ) -> Option<Box<dyn TransitionOracle + '_>> {
            Some(Box::new(SyntacticOracle))
        }

        fn project_call_query(
            &self,
            _caller_query: &ReachabilityQuery,
            call_edge: &PaperEdge,
            omega_n1: &Predicate,
            source_region: &Predicate,
            dest_region: &Predicate,
        ) -> Option<ReachabilityQuery> {
            let EdgeKind::Call { callee } = &call_edge.transition.kind else {
                return None;
            };
            Some(ReachabilityQuery::new(
                callee.clone(),
                Predicate::and([omega_n1.clone(), source_region.clone()]),
                dest_region.clone(),
            ))
        }
    }

    fn interprocedural_must_pair() -> StaticInterproceduralProvider {
        let mut caller = PaperProcedure::new("caller", NodeId(0), NodeId(1));
        caller.add_edge(PaperEdge::call(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            "callee",
            Predicate::atom("Gamma_call"),
        ));

        let mut callee = PaperProcedure::new("callee", NodeId(0), NodeId(1));
        callee.add_edge(PaperEdge::local(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            Predicate::atom("Gamma_local"),
            Some(Predicate::atom("goal")),
            Some(Predicate::True),
        ));

        StaticInterproceduralProvider {
            procedures: BTreeMap::from([
                (ProcedureName::new("caller"), caller),
                (ProcedureName::new("callee"), callee),
            ]),
        }
    }

    fn interprocedural_not_may_pair() -> StaticInterproceduralProvider {
        let mut caller = PaperProcedure::new("caller", NodeId(0), NodeId(1));
        caller.add_edge(PaperEdge::call(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            "callee",
            Predicate::atom("Gamma_call"),
        ));

        let mut callee = PaperProcedure::new("callee", NodeId(0), NodeId(1));
        callee.add_edge(PaperEdge::local(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            Predicate::atom("Gamma_local"),
            Some(Predicate::not(Predicate::atom("bug"))),
            Some(Predicate::not(Predicate::atom("p"))),
        ));

        StaticInterproceduralProvider {
            procedures: BTreeMap::from([
                (ProcedureName::new("caller"), caller),
                (ProcedureName::new("callee"), callee),
            ]),
        }
    }

    #[derive(Clone)]
    struct NoProjectionProvider {
        procedures: BTreeMap<ProcedureName, PaperProcedure>,
    }

    impl InterproceduralOracleProvider for NoProjectionProvider {
        fn procedure(&self, procedure: &ProcedureName) -> Option<&PaperProcedure> {
            self.procedures.get(procedure)
        }

        fn transitions(
            &self,
            _procedure: &ProcedureName,
            _target_assertion: Option<EdgeId>,
        ) -> Option<Box<dyn TransitionOracle + '_>> {
            Some(Box::new(SyntacticOracle))
        }

        fn project_call_query(
            &self,
            _caller_query: &ReachabilityQuery,
            _call_edge: &PaperEdge,
            _omega_n1: &Predicate,
            _source_region: &Predicate,
            _dest_region: &Predicate,
        ) -> Option<ReachabilityQuery> {
            None
        }
    }

    fn unresolved_internal_call_pair() -> NoProjectionProvider {
        let mut caller = PaperProcedure::new("caller", NodeId(0), NodeId(1));
        caller.add_edge(PaperEdge::call(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            "callee",
            Predicate::atom("Gamma_call"),
        ));

        let callee = PaperProcedure::new("callee", NodeId(0), NodeId(1));
        NoProjectionProvider {
            procedures: BTreeMap::from([
                (ProcedureName::new("caller"), caller),
                (ProcedureName::new("callee"), callee),
            ]),
        }
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

    #[test]
    fn call_edge_uses_must_summary_without_transition_stub() {
        let mut driver = PaperDriver::new();
        driver.summaries_mut().add(ProcedureSummary::must(
            "callee",
            Predicate::atom("start"),
            Predicate::atom("goal"),
            "witness",
        ));

        let oracle = SyntacticOracle;
        let procedure = call_only_procedure();
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
    }

    #[test]
    fn call_edge_uses_not_may_summary_without_transition_stub() {
        let mut driver = PaperDriver::new();
        driver.summaries_mut().add(ProcedureSummary::not_may(
            "callee",
            Predicate::atom("p"),
            Predicate::True,
            "proof",
        ));

        let oracle = SyntacticOracle;
        let procedure = call_only_procedure();
        let query = ReachabilityQuery::new("P", Predicate::atom("p"), Predicate::True);

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
    }

    #[test]
    fn interprocedural_run_creates_and_reuses_must_summary() {
        let mut driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let provider = interprocedural_must_pair();
        let query =
            ReachabilityQuery::new("caller", Predicate::atom("start"), Predicate::atom("goal"));

        let result = driver
            .run_interprocedural(&oracle, &provider, &query, InterproceduralConfig::default())
            .unwrap();

        assert!(result.reached_target);
        assert!(driver
            .summaries()
            .for_procedure(&ProcedureName::new("callee"))
            .iter()
            .any(|summary| summary.kind == crate::analysis::summaries::SummaryKind::Must));
    }

    #[test]
    fn interprocedural_run_creates_and_reuses_not_may_summary() {
        let mut driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let provider = interprocedural_not_may_pair();
        let query = ReachabilityQuery::new("caller", Predicate::atom("p"), Predicate::atom("bug"));

        let result = driver
            .run_interprocedural(&oracle, &provider, &query, InterproceduralConfig::default())
            .unwrap();

        assert!(!result.reached_target);
        assert!(driver
            .summaries()
            .for_procedure(&ProcedureName::new("callee"))
            .iter()
            .any(|summary| summary.kind == crate::analysis::summaries::SummaryKind::NotMay));
    }

    #[test]
    fn interprocedural_may_call_runs_with_existing_non_applicable_summary() {
        let mut driver = PaperDriver::new();
        driver.summaries_mut().add(ProcedureSummary::must(
            "callee",
            Predicate::atom("other_pre"),
            Predicate::atom("other_post"),
            "unrelated witness",
        ));

        let oracle = SyntacticOracle;
        let provider = interprocedural_must_pair();
        let query =
            ReachabilityQuery::new("caller", Predicate::atom("start"), Predicate::atom("goal"));

        let result = driver
            .run_interprocedural(&oracle, &provider, &query, InterproceduralConfig::default())
            .unwrap();

        assert!(result.reached_target);
        assert!(driver
            .summaries()
            .for_procedure(&ProcedureName::new("callee"))
            .iter()
            .any(
                |summary| summary.kind == crate::analysis::summaries::SummaryKind::Must
                    && summary.post == Predicate::atom("goal")
            ));
    }

    #[test]
    fn unresolved_internal_call_returns_unknown() {
        let mut driver = PaperDriver::new();
        let oracle = SyntacticOracle;
        let provider = unresolved_internal_call_pair();
        let query =
            ReachabilityQuery::new("caller", Predicate::atom("start"), Predicate::atom("goal"));

        let result = driver
            .run_interprocedural(&oracle, &provider, &query, InterproceduralConfig::default())
            .unwrap();

        assert!(!result.reached_target);
        assert!(result.stopped_by_limit);
    }
}
