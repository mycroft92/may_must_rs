//! Executable driver slices for the current milestone.
//!
//! This module currently exposes two CLI-usable paths:
//!
//! - a temporary bounded path explorer for the wider single-procedure subset
//! - a first rule-driven scheduler over the paper's local Figure 5/6/7 rules
//!
//! The bounded explorer handles one lowered procedure at a time, explores
//! branch paths under a temporary `max_step` loop budget, applies normalized
//! transfer effects, and uses the SMT oracle to decide whether embedded
//! `may_assert` obligations are feasible.
//!
//! The rule-driven slice is deliberately narrower but closer to the paper. It
//! constructs one paper query per lowered assertion, derives scalar `β` / `θ`
//! candidates from normalized edge/node effects, and schedules
//! `INIT_PI_NE`, `INIT_OMEGA`, `MUST_POST`, `NOTMAY_PRE`, `BUGFOUND`, and
//! `VERIFIED`.
//! When requested, that slice can also replay one feasible must-side witness
//! path through the query CFG and attach the resulting SMT model to the final
//! violating state.
//!
//! It is still not the full paper scheduler:
//!
//! - the path explorer still owns the temporary `max_step` loop policy
//! - the rule scheduler is currently limited to acyclic scalar/SSA procedures
//! - interprocedural summary rules are implemented but not yet scheduled here
//!
//! The purpose is to keep one honest executable slice for the current broader
//! subset while also making the local paper rules runnable end to end.
//!
//! The active CLI-visible result is a per-procedure report with explicit
//! per-assertion truth values:
//!
//! - `true` means every explored reachable check of that assertion is safe
//! - `false` means a feasible negated obligation was found
//! - `unknown` means the temporary bounded explorer could not decide
//!
//! When an assertion is `false`, the driver also records a symbolic evidence
//! trace showing the explored state formulas that led to the failing
//! obligation.

use crate::analysis::cfg::{Cfg, CfgEdge, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, Memory, Term, Var};
use crate::analysis::llvm_adapter::{
    adapt_function_graph, adapt_function_graph_with_purity, AdaptedAssertionSite, AdaptedProcedure,
    AdapterError,
};
use crate::analysis::oracle::{Feasibility, Oracle, OracleError};
use crate::analysis::rules::{self, ProcedureFrame, QueryJudgement, ReachabilityQuery, RuleError};
use crate::analysis::state::NodeState;
use crate::analysis::transfer::{apply_effects, AssignValue, TransferEffect, TransferError};
use crate::llvm_utils::program_graph::FunctionGraph;
use log::{debug, log_enabled, Level};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;
use thiserror::Error;

pub const TRACE_TARGET: &str = "analysis_trace";
pub const DEFAULT_MAX_STEP: usize = 3;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimpleDriverOptions {
    pub max_step: usize,
    pub trace_predicates: bool,
}

impl Default for SimpleDriverOptions {
    fn default() -> Self {
        Self {
            max_step: DEFAULT_MAX_STEP,
            trace_predicates: false,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RuleDriverOptions {
    /// Generate one witness trace and final solver model for `Yes` results.
    pub generate_witnesses: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimpleProcedureReport {
    pub procedure: String,
    pub judgement: QueryJudgement,
    pub max_step: usize,
    pub explored_paths: usize,
    pub pruned_paths: usize,
    pub bounded_paths: usize,
    pub checked_obligations: usize,
    pub feasible_obligations: usize,
    pub assertions: Vec<AssertionReport>,
}

impl fmt::Display for SimpleProcedureReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut lines = vec![
            format!("procedure {}", self.procedure),
            format!("  judgement: {:?}", self.judgement),
            format!("  max step: {}", self.max_step),
            format!("  explored paths: {}", self.explored_paths),
            format!("  pruned paths: {}", self.pruned_paths),
            format!("  bounded paths: {}", self.bounded_paths),
            format!("  obligations checked: {}", self.checked_obligations),
            format!("  feasible obligations: {}", self.feasible_obligations),
        ];
        for assertion in &self.assertions {
            lines.push(format!("  assertion {}", assertion.id));
            lines.push(format!("    location: {}", assertion.location));
            if assertion.result == AssertionResult::True && assertion.checked_count == 0 {
                lines.push("    result: true (unreachable)".to_string());
            } else {
                lines.push(format!("    result: {}", assertion.result));
            }
            if let Some(evidence) = &assertion.evidence {
                lines.push("    evidence trace:".to_string());
                for step in &evidence.steps {
                    lines.push(format!("      {}", step.heading()));
                    match step {
                        EvidenceTraceStep::State {
                            generated,
                            path_summary,
                            facts,
                            memory,
                            obligations,
                            feasibility,
                            ..
                        } => {
                            lines.push(format!(
                                "        generated: {}",
                                format_generated(generated)
                            ));
                            lines.push(format!("        path summary: {path_summary}"));
                            lines.push(format!("        facts: {facts}"));
                            lines.push(format!("        memory: {memory}"));
                            lines.push(format!("        obligations: {obligations}"));
                            lines.push(format!("        feasibility: {:?}", feasibility));
                        }
                        EvidenceTraceStep::Obligation {
                            obligation,
                            query,
                            result,
                            ..
                        } => {
                            lines.push(format!("        obligation: {obligation}"));
                            lines.push(format!("        check: {query}"));
                            lines.push(format!("        result: {:?}", result));
                        }
                    }
                }
            }
        }
        write!(f, "{}", lines.join("\n"))
    }
}

impl SimpleProcedureReport {
    pub fn summary_only(
        procedure: impl Into<String>,
        judgement: QueryJudgement,
        max_step: usize,
        explored_paths: usize,
        pruned_paths: usize,
        bounded_paths: usize,
        checked_obligations: usize,
        feasible_obligations: usize,
    ) -> Self {
        Self {
            procedure: procedure.into(),
            judgement,
            max_step,
            explored_paths,
            pruned_paths,
            bounded_paths,
            checked_obligations,
            feasible_obligations,
            assertions: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssertionReport {
    /// Stable 1-based identifier in the adapted procedure report.
    pub id: usize,
    /// Human-readable source position derived from the surrounding LLVM graph.
    pub location: String,
    /// Final truth value for this assertion within the current bounded run.
    pub result: AssertionResult,
    /// Number of explored reachable checks performed for this assertion.
    pub checked_count: usize,
    /// Symbolic counterexample trace when the assertion is false.
    pub evidence: Option<EvidenceTrace>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssertionResult {
    True,
    False,
    Unknown,
}

impl fmt::Display for AssertionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AssertionResult::True => write!(f, "true"),
            AssertionResult::False => write!(f, "false"),
            AssertionResult::Unknown => write!(f, "unknown"),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EvidenceTrace {
    /// Ordered symbolic steps ending at a failing obligation check.
    steps: Vec<EvidenceTraceStep>,
}

impl EvidenceTrace {
    fn push_state(
        &mut self,
        location: impl Into<String>,
        generated: Vec<Formula>,
        state: &NodeState,
        feasibility: Feasibility,
    ) {
        self.steps.push(EvidenceTraceStep::State {
            location: location.into(),
            generated,
            path_summary: state.path_summary().as_formula(),
            facts: state.facts().collapse(),
            memory: state.memory_summary(),
            obligations: state.obligations().collapse(),
            feasibility,
        });
    }

    fn push_obligation(
        &mut self,
        location: impl Into<String>,
        obligation: Formula,
        query: Formula,
        result: Feasibility,
    ) {
        self.steps.push(EvidenceTraceStep::Obligation {
            location: location.into(),
            obligation,
            query,
            result,
        });
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvidenceTraceStep {
    State {
        location: String,
        generated: Vec<Formula>,
        path_summary: Formula,
        facts: Formula,
        memory: String,
        obligations: Formula,
        feasibility: Feasibility,
    },
    Obligation {
        location: String,
        obligation: Formula,
        query: Formula,
        result: Feasibility,
    },
}

impl EvidenceTraceStep {
    fn heading(&self) -> &str {
        match self {
            EvidenceTraceStep::State { location, .. }
            | EvidenceTraceStep::Obligation { location, .. } => location,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AssertionAccumulator {
    id: usize,
    location: String,
    checked_count: usize,
    false_seen: bool,
    unknown_seen: bool,
    evidence: Option<EvidenceTrace>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct PathContext {
    active_nodes: BTreeMap<CfgNodeId, usize>,
    edge_visits: BTreeMap<CfgEdgeId, usize>,
}

impl PathContext {
    fn enter_node(&self, node: CfgNodeId) -> Self {
        let mut next = self.clone();
        *next.active_nodes.entry(node).or_default() += 1;
        next
    }

    fn active_node_count(&self, node: CfgNodeId) -> usize {
        self.active_nodes.get(&node).copied().unwrap_or(0)
    }

    fn increment_edge_visit(&self, edge: CfgEdgeId) -> Self {
        let mut next = self.clone();
        *next.edge_visits.entry(edge).or_default() += 1;
        next
    }

    fn edge_visit_count(&self, edge: CfgEdgeId) -> usize {
        self.edge_visits.get(&edge).copied().unwrap_or(0)
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum DriverError {
    #[error(transparent)]
    Adapter(#[from] AdapterError),
    #[error(transparent)]
    Oracle(#[from] OracleError),
    #[error(transparent)]
    Transfer(#[from] TransferError),
    #[error(transparent)]
    Rule(#[from] RuleError),
    #[error("max_step must be at least 1 but found {max_step}")]
    InvalidMaxStep { max_step: usize },
    #[error("unknown CFG node {node:?}")]
    UnknownNode { node: CfgNodeId },
    #[error("missing CFG edge {edge}")]
    MissingEdge { edge: usize },
    #[error(
        "rule driver currently supports only acyclic scalar assign/assume procedures; unsupported effect: {effect}"
    )]
    UnsupportedRuleEffect { effect: String },
    #[error(
        "rule driver currently requires an acyclic CFG until loop summaries/invariants are implemented"
    )]
    CyclicRuleProcedure,
    #[error(
        "rule driver returned Yes for assertion {assertion_id} but could not replay a witness"
    )]
    MissingRuleWitness { assertion_id: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleProcedureReport {
    pub procedure: String,
    pub judgement: QueryJudgement,
    pub assertions: Vec<RuleAssertionReport>,
}

impl fmt::Display for RuleProcedureReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut lines = vec![
            format!("procedure {}", self.procedure),
            format!("  judgement: {:?}", self.judgement),
            format!("  assertions: {}", self.assertions.len()),
        ];
        for assertion in &self.assertions {
            lines.push(format!("  assertion {}", assertion.id));
            lines.push(format!("    location: {}", assertion.location));
            lines.push(format!("    result: {}", assertion.result));
            lines.push(format!("    judgement: {:?}", assertion.judgement));
            lines.push(format!("    rule rounds: {}", assertion.rule_rounds));
            lines.push(format!(
                "    rule applications: {}",
                assertion.rule_applications
            ));
            lines.push(format!(
                "    unknown premises: {}",
                assertion.unknown_premises
            ));
            if let Some(witness) = &assertion.witness {
                lines.push("    witness trace:".to_string());
                for step in &witness.steps {
                    lines.push(format!("      {}", step.heading()));
                    match step {
                        RuleWitnessStep::State {
                            generated,
                            path_summary,
                            facts,
                            feasibility,
                            ..
                        } => {
                            lines.push(format!(
                                "        generated: {}",
                                format_generated(generated)
                            ));
                            lines.push(format!("        path summary: {path_summary}"));
                            lines.push(format!("        facts: {facts}"));
                            lines.push(format!("        feasibility: {:?}", feasibility));
                        }
                        RuleWitnessStep::Outcome {
                            query,
                            result,
                            model,
                            ..
                        } => {
                            lines.push(format!("        check: {query}"));
                            lines.push(format!("        result: {:?}", result));
                            if let Some(model) = model {
                                lines.push("        model:".to_string());
                                append_indented_block(&mut lines, model, 10);
                            }
                        }
                    }
                }
            }
        }
        write!(f, "{}", lines.join("\n"))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleAssertionReport {
    pub id: usize,
    pub location: String,
    pub result: AssertionResult,
    pub judgement: QueryJudgement,
    pub rule_rounds: usize,
    pub rule_applications: usize,
    pub unknown_premises: usize,
    /// Optional on-demand witness for `Yes` results in the current local rule slice.
    pub witness: Option<RuleWitnessTrace>,
}

#[derive(Clone, Debug)]
struct AssertionQueryProcedure {
    cfg: Cfg,
    node_effects: BTreeMap<CfgNodeId, Vec<TransferEffect>>,
    edge_effects: BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct RuleSearchStats {
    rounds: usize,
    applications: usize,
    unknown_premises: usize,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RuleWitnessTrace {
    /// Ordered symbolic states ending at the final violating query check.
    steps: Vec<RuleWitnessStep>,
}

impl RuleWitnessTrace {
    fn push_state(
        &mut self,
        location: impl Into<String>,
        generated: Vec<Formula>,
        state: &NodeState,
        feasibility: Feasibility,
    ) {
        self.steps.push(RuleWitnessStep::State {
            location: location.into(),
            generated,
            path_summary: state.path_summary().as_formula(),
            facts: state.facts().collapse(),
            feasibility,
        });
    }

    fn push_outcome(
        &mut self,
        location: impl Into<String>,
        query: Formula,
        result: Feasibility,
        model: Option<String>,
    ) {
        self.steps.push(RuleWitnessStep::Outcome {
            location: location.into(),
            query,
            result,
            model,
        });
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleWitnessStep {
    State {
        location: String,
        generated: Vec<Formula>,
        path_summary: Formula,
        facts: Formula,
        feasibility: Feasibility,
    },
    Outcome {
        location: String,
        query: Formula,
        result: Feasibility,
        model: Option<String>,
    },
}

impl RuleWitnessStep {
    fn heading(&self) -> &str {
        match self {
            RuleWitnessStep::State { location, .. } | RuleWitnessStep::Outcome { location, .. } => {
                location
            }
        }
    }
}

pub fn analyze_function_graph_simple(
    graph: &FunctionGraph,
) -> Result<SimpleProcedureReport, DriverError> {
    analyze_function_graph_simple_with_options(graph, SimpleDriverOptions::default())
}

pub fn analyze_function_graph_simple_with_options(
    graph: &FunctionGraph,
    options: SimpleDriverOptions,
) -> Result<SimpleProcedureReport, DriverError> {
    let adapted = adapt_function_graph(graph)?;
    analyze_adapted_procedure_simple_with_options(&graph.name, &adapted, options)
}

pub fn analyze_function_graph_simple_with_purity(
    graph: &FunctionGraph,
    memory_pure_functions: &BTreeSet<String>,
    options: SimpleDriverOptions,
) -> Result<SimpleProcedureReport, DriverError> {
    let adapted = adapt_function_graph_with_purity(graph, memory_pure_functions)?;
    analyze_adapted_procedure_simple_with_options(&graph.name, &adapted, options)
}

pub fn analyze_adapted_procedure_simple(
    procedure: &str,
    adapted: &AdaptedProcedure,
) -> Result<SimpleProcedureReport, DriverError> {
    analyze_adapted_procedure_simple_with_options(
        procedure,
        adapted,
        SimpleDriverOptions::default(),
    )
}

pub fn analyze_adapted_procedure_simple_with_options(
    procedure: &str,
    adapted: &AdaptedProcedure,
    options: SimpleDriverOptions,
) -> Result<SimpleProcedureReport, DriverError> {
    if options.max_step == 0 {
        return Err(DriverError::InvalidMaxStep {
            max_step: options.max_step,
        });
    }
    let oracle = Oracle::new();
    let mut explorer = SimpleExplorer::new(procedure, adapted, &oracle, options);
    explorer.explore_entry()?;
    Ok(explorer.finish())
}

struct SimpleExplorer<'a> {
    procedure: &'a str,
    adapted: &'a AdaptedProcedure,
    oracle: &'a Oracle,
    options: SimpleDriverOptions,
    explored_paths: usize,
    pruned_paths: usize,
    bounded_paths: usize,
    checked_obligations: usize,
    feasible_obligations: usize,
    unknown_seen: bool,
    next_path_id: usize,
    assertion_accumulators: BTreeMap<usize, AssertionAccumulator>,
}

impl<'a> SimpleExplorer<'a> {
    fn new(
        procedure: &'a str,
        adapted: &'a AdaptedProcedure,
        oracle: &'a Oracle,
        options: SimpleDriverOptions,
    ) -> Self {
        let mut assertion_accumulators = BTreeMap::new();
        for site in adapted.assertions_by_node.values().flatten() {
            assertion_accumulators.insert(
                site.id,
                AssertionAccumulator {
                    id: site.id,
                    location: site.location.clone(),
                    checked_count: 0,
                    false_seen: false,
                    unknown_seen: false,
                    evidence: None,
                },
            );
        }
        Self {
            procedure,
            adapted,
            oracle,
            options,
            explored_paths: 0,
            pruned_paths: 0,
            bounded_paths: 0,
            checked_obligations: 0,
            feasible_obligations: 0,
            unknown_seen: false,
            next_path_id: 1,
            assertion_accumulators,
        }
    }

    fn finish(self) -> SimpleProcedureReport {
        let judgement = if self.feasible_obligations > 0 {
            QueryJudgement::Yes
        } else if self.unknown_seen {
            QueryJudgement::Unknown
        } else {
            QueryJudgement::No
        };
        let procedure_unknown = self.unknown_seen;
        let assertions = self
            .assertion_accumulators
            .into_values()
            .map(|accumulator| {
                let result = if accumulator.false_seen {
                    AssertionResult::False
                } else if procedure_unknown || accumulator.unknown_seen {
                    AssertionResult::Unknown
                } else {
                    AssertionResult::True
                };
                AssertionReport {
                    id: accumulator.id,
                    location: accumulator.location,
                    result,
                    checked_count: accumulator.checked_count,
                    evidence: accumulator.evidence,
                }
            })
            .collect();
        SimpleProcedureReport {
            procedure: self.procedure.to_string(),
            judgement,
            max_step: self.options.max_step,
            explored_paths: self.explored_paths,
            pruned_paths: self.pruned_paths,
            bounded_paths: self.bounded_paths,
            checked_obligations: self.checked_obligations,
            feasible_obligations: self.feasible_obligations,
            assertions,
        }
    }

    fn explore_entry(&mut self) -> Result<(), DriverError> {
        let entry = self.adapted.cfg.entry();
        let path_id = self.allocate_path_id();
        self.explore_node(
            entry,
            NodeState::entry(),
            PathContext::default(),
            path_id,
            EvidenceTrace::default(),
        )
    }

    fn explore_node(
        &mut self,
        node: CfgNodeId,
        mut state: NodeState,
        context: PathContext,
        path_id: usize,
        mut trace: EvidenceTrace,
    ) -> Result<(), DriverError> {
        let context = context.enter_node(node);
        let node_label = self.node_label(node)?;
        let repeated_node = context.active_node_count(node) > 1;

        if let Some(effects) = self.adapted.node_effects.get(&node) {
            apply_effects(&mut state, effects)?;
        }

        let node_generated = self
            .adapted
            .node_effects
            .get(&node)
            .map(|effects| effect_predicates(effects))
            .unwrap_or_default();
        let node_feasibility = self.oracle.state_feasibility(&state)?;
        trace.push_state(
            format!("step {}: node {node_label}", trace.steps.len() + 1),
            node_generated.clone(),
            &state,
            node_feasibility,
        );
        if !repeated_node {
            self.debug_state_step(
                path_id,
                &format!("node {node_label}"),
                &node_generated,
                &state,
                node_feasibility,
            );
        }

        match node_feasibility {
            Feasibility::Feasible => {}
            Feasibility::Infeasible => {
                self.pruned_paths += 1;
                return Ok(());
            }
            Feasibility::Unknown => {
                self.unknown_seen = true;
                return Ok(());
            }
        }

        self.check_obligations(node, &mut state, path_id, &trace)?;

        let outgoing = self
            .adapted
            .cfg
            .outgoing_edges(node)
            .map_err(|_| DriverError::UnknownNode { node })?;
        if outgoing.is_empty() {
            self.explored_paths += 1;
            self.debug_path_completion(path_id, &state);
            return Ok(());
        }

        let edge_count = outgoing.len();
        for (edge_index, edge_id) in outgoing.into_iter().enumerate() {
            let edge = self
                .adapted
                .cfg
                .edge(edge_id)
                .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
            let branch_path_id = if edge_count > 1 && edge_index > 0 {
                self.allocate_path_id()
            } else {
                path_id
            };

            if context.edge_visit_count(edge_id) >= self.options.max_step {
                // APPROX_HEAVY: bounded loop handling cuts off any path whose
                // next step would exceed the temporary edge-visit budget.
                self.bounded_paths += 1;
                self.unknown_seen = true;
                self.debug_bound_cutoff(branch_path_id, edge, &state)?;
                continue;
            }

            let mut next_state = state.clone();
            next_state.path_summary_mut().refine(edge.relation.clone());
            if let Some(effects) = self.adapted.edge_effects.get(&edge_id) {
                apply_effects(&mut next_state, effects)?;
            }

            let next_context = context.increment_edge_visit(edge_id);
            let visit_count = next_context.edge_visit_count(edge_id);
            let edge_feasibility = self.oracle.state_feasibility(&next_state)?;
            let target_label = self.node_label(edge.target)?;
            let generated = edge_predicates(
                edge.relation.clone(),
                self.adapted.edge_effects.get(&edge_id),
            );
            let mut next_trace = trace.clone();
            next_trace.push_state(
                format!(
                    "step {}: edge {} -> {}",
                    next_trace.steps.len() + 1,
                    node_label,
                    target_label
                ),
                generated.clone(),
                &next_state,
                edge_feasibility,
            );

            if context.active_node_count(edge.target) > 0 || visit_count > 1 {
                self.debug_loop_iteration(
                    branch_path_id,
                    edge,
                    &node_label,
                    &target_label,
                    visit_count,
                    &generated,
                    &next_state,
                    edge_feasibility,
                );
            } else {
                self.debug_state_step(
                    branch_path_id,
                    &format!("edge {} -> {}", node_label, target_label),
                    &generated,
                    &next_state,
                    edge_feasibility,
                );
            }

            match edge_feasibility {
                Feasibility::Feasible => {
                    self.explore_node(
                        edge.target,
                        next_state,
                        next_context,
                        branch_path_id,
                        next_trace,
                    )?;
                }
                Feasibility::Infeasible => {
                    self.pruned_paths += 1;
                }
                Feasibility::Unknown => {
                    self.unknown_seen = true;
                }
            }
        }

        Ok(())
    }

    fn check_obligations(
        &mut self,
        node: CfgNodeId,
        state: &mut NodeState,
        path_id: usize,
        trace: &EvidenceTrace,
    ) -> Result<(), DriverError> {
        let obligations = state.obligations().formulas().to_vec();
        if obligations.is_empty() {
            return Ok(());
        }

        let path_formula = state.feasibility_formula();
        let node_label = self.node_label(node)?;
        let assertion_sites = self
            .adapted
            .assertions_by_node
            .get(&node)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        for (index, obligation) in obligations.into_iter().enumerate() {
            self.checked_obligations += 1;
            let query = Formula::and(path_formula.clone(), obligation.clone());
            let result = self.oracle.feasibility(&query)?;
            let assertion_site = assertion_sites
                .get(index)
                .filter(|site| site.obligation == obligation)
                .cloned();
            let evidence_location = assertion_site
                .as_ref()
                .map(|site| {
                    format!(
                        "step {}: assertion {} at {}",
                        trace.steps.len() + 1,
                        site.id,
                        site.location
                    )
                })
                .unwrap_or_else(|| {
                    format!("step {}: obligation at {node_label}", trace.steps.len() + 1)
                });
            self.debug_obligation_step(path_id, &node_label, &obligation, &query, result);
            if let Some(site) = &assertion_site {
                let accumulator = self
                    .assertion_accumulators
                    .get_mut(&site.id)
                    .expect("assertion accumulator should exist");
                accumulator.checked_count += 1;
            }
            match result {
                Feasibility::Feasible => {
                    self.feasible_obligations += 1;
                    if let Some(site) = assertion_site {
                        let accumulator = self
                            .assertion_accumulators
                            .get_mut(&site.id)
                            .expect("assertion accumulator should exist");
                        accumulator.false_seen = true;
                        if accumulator.evidence.is_none() {
                            let mut evidence = trace.clone();
                            evidence.push_obligation(evidence_location, obligation, query, result);
                            accumulator.evidence = Some(evidence);
                        }
                    }
                }
                Feasibility::Infeasible => {}
                Feasibility::Unknown => {
                    self.unknown_seen = true;
                    if let Some(site) = assertion_site {
                        let accumulator = self
                            .assertion_accumulators
                            .get_mut(&site.id)
                            .expect("assertion accumulator should exist");
                        accumulator.unknown_seen = true;
                    }
                }
            }
        }
        state.clear_obligations();
        Ok(())
    }

    fn allocate_path_id(&mut self) -> usize {
        let path_id = self.next_path_id;
        self.next_path_id += 1;
        path_id
    }

    fn node_label(&self, node: CfgNodeId) -> Result<String, DriverError> {
        self.adapted
            .cfg
            .node(node)
            .map(|node| normalize_label(&node.label))
            .ok_or(DriverError::UnknownNode { node })
    }

    fn trace_enabled(&self) -> bool {
        self.options.trace_predicates && log_enabled!(target: TRACE_TARGET, Level::Debug)
    }

    fn debug_state_step(
        &self,
        path_id: usize,
        location: &str,
        generated: &[Formula],
        state: &NodeState,
        feasibility: Feasibility,
    ) {
        if !self.trace_enabled() {
            return;
        }
        debug!(
            target: TRACE_TARGET,
            "path {path_id} {location}: generated={}; path_summary={}; facts={}; memory={}; obligations={}; feasibility={:?}",
            format_generated(generated),
            state.path_summary().as_formula(),
            state.facts().collapse(),
            state.memory_summary(),
            state.obligations().collapse(),
            feasibility
        );
    }

    fn debug_loop_iteration(
        &self,
        path_id: usize,
        edge: &CfgEdge,
        source_label: &str,
        target_label: &str,
        visit_count: usize,
        generated: &[Formula],
        state: &NodeState,
        feasibility: Feasibility,
    ) {
        if !self.trace_enabled() {
            return;
        }
        debug!(
            target: TRACE_TARGET,
            "path {path_id} loop edge {} ({} -> {}) iteration {}: generated={}; formula={}; memory={}; obligations={}; feasibility={:?}",
            edge.id.0,
            source_label,
            target_label,
            visit_count,
            format_generated(generated),
            state.feasibility_formula(),
            state.memory_summary(),
            state.obligations().collapse(),
            feasibility
        );
    }

    fn debug_obligation_step(
        &self,
        path_id: usize,
        node_label: &str,
        obligation: &Formula,
        query: &Formula,
        result: Feasibility,
    ) {
        if !self.trace_enabled() {
            return;
        }
        debug!(
            target: TRACE_TARGET,
            "path {path_id} obligation at {node_label}: obligation={obligation}; check={query}; result={:?}",
            result
        );
    }

    fn debug_bound_cutoff(
        &self,
        path_id: usize,
        edge: &CfgEdge,
        state: &NodeState,
    ) -> Result<(), DriverError> {
        if !self.trace_enabled() {
            return Ok(());
        }
        debug!(
            target: TRACE_TARGET,
            "path {path_id} max_step cutoff on edge {} ({} -> {}): max_step={}; formula={}; memory={}; obligations={}",
            edge.id.0,
            self.node_label(edge.source)?,
            self.node_label(edge.target)?,
            self.options.max_step,
            state.feasibility_formula(),
            state.memory_summary(),
            state.obligations().collapse()
        );
        Ok(())
    }

    fn debug_path_completion(&self, path_id: usize, state: &NodeState) {
        if !self.trace_enabled() {
            return;
        }
        debug!(
            target: TRACE_TARGET,
            "path {path_id} complete: formula={}; memory={}; obligations={}",
            state.feasibility_formula(),
            state.memory_summary(),
            state.obligations().collapse()
        );
    }
}

pub fn analyze_function_graph_rules(
    graph: &FunctionGraph,
) -> Result<RuleProcedureReport, DriverError> {
    let adapted = adapt_function_graph(graph)?;
    analyze_adapted_procedure_rules_with_options(
        &graph.name,
        &adapted,
        RuleDriverOptions::default(),
    )
}

pub fn analyze_function_graph_rules_with_purity(
    graph: &FunctionGraph,
    memory_pure_functions: &BTreeSet<String>,
) -> Result<RuleProcedureReport, DriverError> {
    let adapted = adapt_function_graph_with_purity(graph, memory_pure_functions)?;
    analyze_adapted_procedure_rules_with_options(
        &graph.name,
        &adapted,
        RuleDriverOptions::default(),
    )
}

pub fn analyze_function_graph_rules_with_options(
    graph: &FunctionGraph,
    options: RuleDriverOptions,
) -> Result<RuleProcedureReport, DriverError> {
    let adapted = adapt_function_graph(graph)?;
    analyze_adapted_procedure_rules_with_options(&graph.name, &adapted, options)
}

pub fn analyze_function_graph_rules_with_purity_and_options(
    graph: &FunctionGraph,
    memory_pure_functions: &BTreeSet<String>,
    options: RuleDriverOptions,
) -> Result<RuleProcedureReport, DriverError> {
    let adapted = adapt_function_graph_with_purity(graph, memory_pure_functions)?;
    analyze_adapted_procedure_rules_with_options(&graph.name, &adapted, options)
}

pub fn analyze_adapted_procedure_rules(
    procedure: &str,
    adapted: &AdaptedProcedure,
) -> Result<RuleProcedureReport, DriverError> {
    analyze_adapted_procedure_rules_with_options(procedure, adapted, RuleDriverOptions::default())
}

pub fn analyze_adapted_procedure_rules_with_options(
    procedure: &str,
    adapted: &AdaptedProcedure,
    options: RuleDriverOptions,
) -> Result<RuleProcedureReport, DriverError> {
    let assertion_sites = collect_assertion_sites(adapted);
    let mut assertions = Vec::new();
    for (node, site) in assertion_sites {
        let query_procedure = build_assertion_query_procedure(adapted, node, &site)?;
        ensure_rule_query_supported(&query_procedure)?;
        assertions.push(analyze_assertion_query(
            procedure,
            &site,
            &query_procedure,
            &options,
        )?);
    }
    Ok(RuleProcedureReport {
        procedure: procedure.to_string(),
        judgement: aggregate_assertion_judgement(&assertions),
        assertions,
    })
}

fn analyze_assertion_query(
    procedure: &str,
    site: &AdaptedAssertionSite,
    query_procedure: &AssertionQueryProcedure,
    options: &RuleDriverOptions,
) -> Result<RuleAssertionReport, DriverError> {
    let oracle = Oracle::new();
    let query = ReachabilityQuery::new(procedure, Formula::True, Formula::True);
    let mut frame = ProcedureFrame::new(query_procedure.cfg.clone(), query);
    rules::figure5::INIT_PI_NE(&mut frame)?;
    rules::figure6::INIT_OMEGA(&mut frame)?;

    let mut stats = RuleSearchStats::default();
    loop {
        match rules::figure6::BUGFOUND(&frame, &oracle)? {
            QueryJudgement::Yes => {
                return rule_assertion_report(
                    site,
                    QueryJudgement::Yes,
                    stats,
                    query_procedure,
                    &oracle,
                    options,
                );
            }
            QueryJudgement::No | QueryJudgement::Unknown => {}
        }
        match rules::figure5::VERIFIED(&frame, &oracle)? {
            QueryJudgement::No => {
                return rule_assertion_report(
                    site,
                    QueryJudgement::No,
                    stats,
                    query_procedure,
                    &oracle,
                    options,
                );
            }
            QueryJudgement::Yes | QueryJudgement::Unknown => {}
        }

        stats.rounds += 1;
        let mut changed = false;
        changed |= apply_must_post_round(&mut frame, query_procedure, &oracle, &mut stats)?;
        changed |= apply_notmay_pre_round(&mut frame, query_procedure, &oracle, &mut stats)?;
        changed |= apply_notmay_closure_round(&mut frame, &oracle, &mut stats)?;

        if !changed {
            break;
        }
    }

    let final_judgement = match rules::figure6::BUGFOUND(&frame, &oracle)? {
        QueryJudgement::Yes => QueryJudgement::Yes,
        QueryJudgement::No | QueryJudgement::Unknown => {
            match rules::figure5::VERIFIED(&frame, &oracle)? {
                QueryJudgement::No => QueryJudgement::No,
                QueryJudgement::Yes | QueryJudgement::Unknown => QueryJudgement::Unknown,
            }
        }
    };
    rule_assertion_report(
        site,
        final_judgement,
        stats,
        query_procedure,
        &oracle,
        options,
    )
}

fn rule_assertion_report(
    site: &AdaptedAssertionSite,
    judgement: QueryJudgement,
    stats: RuleSearchStats,
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
    options: &RuleDriverOptions,
) -> Result<RuleAssertionReport, DriverError> {
    let result = match judgement {
        QueryJudgement::No => AssertionResult::True,
        QueryJudgement::Yes => AssertionResult::False,
        QueryJudgement::Unknown => AssertionResult::Unknown,
    };
    let witness = if options.generate_witnesses && judgement == QueryJudgement::Yes {
        Some(generate_rule_witness(query_procedure, oracle)?.ok_or(
            DriverError::MissingRuleWitness {
                assertion_id: site.id,
            },
        )?)
    } else {
        None
    };
    Ok(RuleAssertionReport {
        id: site.id,
        location: site.location.clone(),
        result,
        judgement,
        rule_rounds: stats.rounds,
        rule_applications: stats.applications,
        unknown_premises: stats.unknown_premises,
        witness,
    })
}

fn aggregate_assertion_judgement(assertions: &[RuleAssertionReport]) -> QueryJudgement {
    if assertions
        .iter()
        .any(|assertion| assertion.judgement == QueryJudgement::Yes)
    {
        QueryJudgement::Yes
    } else if assertions
        .iter()
        .any(|assertion| assertion.judgement == QueryJudgement::Unknown)
    {
        QueryJudgement::Unknown
    } else {
        QueryJudgement::No
    }
}

fn collect_assertion_sites(adapted: &AdaptedProcedure) -> Vec<(CfgNodeId, AdaptedAssertionSite)> {
    let mut assertions = adapted
        .assertions_by_node
        .iter()
        .flat_map(|(node, sites)| sites.iter().cloned().map(move |site| (*node, site)))
        .collect::<Vec<_>>();
    assertions.sort_by_key(|(_, site)| site.id);
    assertions
}

fn build_assertion_query_procedure(
    adapted: &AdaptedProcedure,
    assertion_node: CfgNodeId,
    site: &AdaptedAssertionSite,
) -> Result<AssertionQueryProcedure, DriverError> {
    let original_entry = adapted.cfg.entry();
    let mut cfg = Cfg::new("__query_entry");
    let mut node_map = BTreeMap::<CfgNodeId, CfgNodeId>::new();

    for original_node in adapted.cfg.nodes().keys().copied() {
        let label = adapted
            .cfg
            .node(original_node)
            .ok_or(DriverError::UnknownNode {
                node: original_node,
            })?
            .label
            .clone();
        node_map.insert(original_node, cfg.add_node(label));
    }

    cfg.add_edge(cfg.entry(), node_map[&original_entry], Formula::True)
        .expect("synthetic query entry should connect to the original entry");

    let mut edge_map = BTreeMap::<CfgEdgeId, CfgEdgeId>::new();
    for (edge_id, edge) in adapted.cfg.edges() {
        let copied_edge = cfg
            .add_edge(
                node_map[&edge.source],
                node_map[&edge.target],
                edge.relation.clone(),
            )
            .expect("copied edge endpoints should exist");
        edge_map.insert(*edge_id, copied_edge);
    }

    let mut node_effects = BTreeMap::<CfgNodeId, Vec<TransferEffect>>::new();
    for (node, effects) in &adapted.node_effects {
        let filtered = effects
            .iter()
            .filter(|effect| !matches!(effect, TransferEffect::Obligation(_)))
            .cloned()
            .collect::<Vec<_>>();
        if !filtered.is_empty() {
            node_effects.insert(node_map[node], filtered);
        }
    }

    let mut edge_effects = BTreeMap::<CfgEdgeId, Vec<TransferEffect>>::new();
    for (edge, effects) in &adapted.edge_effects {
        edge_effects.insert(edge_map[edge], effects.clone());
    }

    let violation_exit = cfg.add_node(format!("__assert{}_violation", site.id));
    cfg.mark_exit(violation_exit)
        .expect("fresh violation exit should be markable");
    cfg.add_edge(
        node_map[&assertion_node],
        violation_exit,
        site.obligation.clone(),
    )
    .expect("violation edge should connect existing nodes");
    cfg.ensure_single_exit()
        .expect("assertion query CFG should have one violation exit");

    Ok(AssertionQueryProcedure {
        cfg,
        node_effects,
        edge_effects,
    })
}

fn ensure_rule_query_supported(
    query_procedure: &AssertionQueryProcedure,
) -> Result<(), DriverError> {
    // APPROX_HEAVY: until loop summaries/invariants exist, the rule-driven
    // slice rejects cyclic CFGs and leaves loop handling to the temporary
    // bounded explorer.
    if !cfg_is_acyclic(&query_procedure.cfg) {
        return Err(DriverError::CyclicRuleProcedure);
    }
    for effects in query_procedure
        .node_effects
        .values()
        .chain(query_procedure.edge_effects.values())
    {
        for effect in effects {
            match effect {
                TransferEffect::Assign { .. } | TransferEffect::Assume(_) | TransferEffect::Nop => {
                }
                other => {
                    return Err(DriverError::UnsupportedRuleEffect {
                        effect: format!("{other:?}"),
                    });
                }
            }
        }
    }
    Ok(())
}

fn generate_rule_witness(
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
) -> Result<Option<RuleWitnessTrace>, DriverError> {
    // APPROX_HEAVY: the current rule-driven witness is reconstructed by
    // replaying the lowered query CFG after a `BUGFOUND` result rather than
    // by storing first-class must-rule provenance during scheduling.
    let entry = query_procedure.cfg.entry();
    search_rule_witness_path(
        query_procedure,
        oracle,
        entry,
        NodeState::entry(),
        RuleWitnessTrace::default(),
    )
}

fn search_rule_witness_path(
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
    node: CfgNodeId,
    mut state: NodeState,
    mut trace: RuleWitnessTrace,
) -> Result<Option<RuleWitnessTrace>, DriverError> {
    let node_label = cfg_node_label(&query_procedure.cfg, node)?;
    if let Some(effects) = query_procedure.node_effects.get(&node) {
        apply_effects(&mut state, effects)?;
    }

    let node_generated = query_procedure
        .node_effects
        .get(&node)
        .map(|effects| effect_predicates(effects))
        .unwrap_or_default();
    let node_feasibility = oracle.state_feasibility(&state)?;
    trace.push_state(
        format!("step {}: node {node_label}", trace.steps.len() + 1),
        node_generated,
        &state,
        node_feasibility,
    );
    if node_feasibility != Feasibility::Feasible {
        return Ok(None);
    }

    if query_procedure.cfg.exit() == Some(node) {
        let query = state.feasibility_formula();
        let report = oracle.state_feasibility_with_model(&state)?;
        trace.push_outcome(
            format!("step {}: violation query", trace.steps.len() + 1),
            query,
            report.feasibility,
            report.model,
        );
        return Ok((report.feasibility == Feasibility::Feasible).then_some(trace));
    }

    let outgoing = query_procedure
        .cfg
        .outgoing_edges(node)
        .map_err(|_| DriverError::UnknownNode { node })?;
    for edge_id in outgoing {
        let edge = query_procedure
            .cfg
            .edge(edge_id)
            .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
        let mut next_state = state.clone();
        next_state.path_summary_mut().refine(edge.relation.clone());
        if let Some(effects) = query_procedure.edge_effects.get(&edge_id) {
            apply_effects(&mut next_state, effects)?;
        }

        let target_label = cfg_node_label(&query_procedure.cfg, edge.target)?;
        let generated = edge_predicates(
            edge.relation.clone(),
            query_procedure.edge_effects.get(&edge_id),
        );
        let edge_feasibility = oracle.state_feasibility(&next_state)?;
        let mut next_trace = trace.clone();
        next_trace.push_state(
            format!(
                "step {}: edge {} -> {}",
                next_trace.steps.len() + 1,
                node_label,
                target_label
            ),
            generated,
            &next_state,
            edge_feasibility,
        );
        if edge_feasibility != Feasibility::Feasible {
            continue;
        }

        if let Some(witness) =
            search_rule_witness_path(query_procedure, oracle, edge.target, next_state, next_trace)?
        {
            return Ok(Some(witness));
        }
    }

    Ok(None)
}

fn cfg_is_acyclic(cfg: &Cfg) -> bool {
    let mut indegree = cfg
        .nodes()
        .keys()
        .copied()
        .map(|node| (node, 0usize))
        .collect::<BTreeMap<_, _>>();
    for edge in cfg.edges().values() {
        *indegree.entry(edge.target).or_default() += 1;
    }
    let mut queue = indegree
        .iter()
        .filter_map(|(node, degree)| (*degree == 0).then_some(*node))
        .collect::<VecDeque<_>>();
    let mut visited = 0usize;
    let mut remaining = indegree;
    while let Some(node) = queue.pop_front() {
        visited += 1;
        for edge in cfg
            .outgoing_edges(node)
            .expect("acyclicity check only visits known nodes")
        {
            let target = cfg
                .edge(edge)
                .expect("known edge id should exist during acyclicity check")
                .target;
            let degree = remaining
                .get_mut(&target)
                .expect("target node should exist during acyclicity check");
            *degree -= 1;
            if *degree == 0 {
                queue.push_back(target);
            }
        }
    }
    visited == cfg.nodes().len()
}

fn apply_must_post_round(
    frame: &mut ProcedureFrame,
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
    stats: &mut RuleSearchStats,
) -> Result<bool, DriverError> {
    let mut changed = false;
    let edges = frame.cfg().edges().keys().copied().collect::<Vec<_>>();
    for edge_id in edges {
        let edge = frame
            .cfg()
            .edge(edge_id)
            .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
        let source_regions = frame
            .partition(edge.source)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.source,
            }))?
            .to_vec();
        let target_regions = frame
            .partition(edge.target)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.target,
            }))?
            .to_vec();
        let omega_source = frame.omega(edge.source).cloned().unwrap_or(Formula::False);
        let theta = Formula::and(
            omega_source,
            forward_step_formula(query_procedure, edge_id)?,
        );
        for phi_1 in &source_regions {
            for phi_2 in &target_regions {
                changed |= attempt_mutating_rule(frame, stats, |frame| {
                    rules::figure7::MUST_POST(frame, edge_id, phi_1, phi_2, theta.clone(), oracle)
                })?;
            }
        }
    }
    Ok(changed)
}

fn apply_notmay_pre_round(
    frame: &mut ProcedureFrame,
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
    stats: &mut RuleSearchStats,
) -> Result<bool, DriverError> {
    let mut changed = false;
    let edges = frame.cfg().edges().keys().copied().collect::<Vec<_>>();
    for edge_id in edges {
        let edge = frame
            .cfg()
            .edge(edge_id)
            .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
        let source_regions = frame
            .partition(edge.source)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.source,
            }))?
            .to_vec();
        let target_regions = frame
            .partition(edge.target)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.target,
            }))?
            .to_vec();
        for phi_1 in &source_regions {
            for phi_2 in &target_regions {
                let beta = backward_pre_candidate(query_procedure, edge_id, phi_2)?;
                changed |= attempt_mutating_rule(frame, stats, |frame| {
                    rules::figure7::NOTMAY_PRE(frame, edge_id, phi_1, phi_2, beta.clone(), oracle)
                })?;
            }
        }
    }
    Ok(changed)
}

fn apply_notmay_closure_round(
    frame: &mut ProcedureFrame,
    oracle: &Oracle,
    stats: &mut RuleSearchStats,
) -> Result<bool, DriverError> {
    let mut changed = false;
    let edges = frame.cfg().edges().keys().copied().collect::<Vec<_>>();
    for edge_id in edges {
        let edge = frame
            .cfg()
            .edge(edge_id)
            .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
        let source_regions = frame
            .partition(edge.source)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.source,
            }))?
            .to_vec();
        let target_regions = frame
            .partition(edge.target)
            .ok_or(DriverError::Rule(RuleError::MissingPartition {
                node: edge.target,
            }))?
            .to_vec();
        let blocked_pairs = frame.notmay_pairs(edge_id).unwrap_or(&[]).to_vec();
        for pair in &blocked_pairs {
            for phi_prime_1 in &source_regions {
                changed |= attempt_mutating_rule(frame, stats, |frame| {
                    rules::figure5::IMPL_LEFT(
                        frame,
                        edge_id,
                        &pair.pre_region,
                        &pair.post_region,
                        phi_prime_1,
                        oracle,
                    )
                })?;
            }
            for phi_prime_2 in &target_regions {
                changed |= attempt_mutating_rule(frame, stats, |frame| {
                    rules::figure5::IMPL_RIGHT(
                        frame,
                        edge_id,
                        &pair.pre_region,
                        &pair.post_region,
                        phi_prime_2,
                        oracle,
                    )
                })?;
            }
        }
    }
    Ok(changed)
}

fn attempt_mutating_rule<F>(
    frame: &mut ProcedureFrame,
    stats: &mut RuleSearchStats,
    apply_rule: F,
) -> Result<bool, DriverError>
where
    F: FnOnce(&mut ProcedureFrame) -> Result<(), RuleError>,
{
    let before = frame.clone();
    match apply_rule(frame) {
        Ok(()) => {
            let changed = *frame != before;
            if changed {
                stats.applications += 1;
            }
            Ok(changed)
        }
        Err(RuleError::PremiseUnknown { .. }) => {
            stats.unknown_premises += 1;
            Ok(false)
        }
        Err(RuleError::PremiseNotSatisfied { .. })
        | Err(RuleError::RegionNotInPartition { .. })
        | Err(RuleError::MissingNotMayPair { .. }) => Ok(false),
        Err(error) => Err(DriverError::Rule(error)),
    }
}

fn forward_step_formula(
    query_procedure: &AssertionQueryProcedure,
    edge_id: CfgEdgeId,
) -> Result<Formula, DriverError> {
    let edge = query_procedure
        .cfg
        .edge(edge_id)
        .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
    let mut formulas = Vec::new();
    if edge.relation != Formula::True {
        formulas.push(edge.relation.clone());
    }
    if let Some(effects) = query_procedure.edge_effects.get(&edge_id) {
        formulas.extend(effect_formulas_for_rules(effects)?);
    }
    if let Some(effects) = query_procedure.node_effects.get(&edge.target) {
        formulas.extend(effect_formulas_for_rules(effects)?);
    }
    Ok(Formula::and_all(formulas))
}

fn backward_pre_candidate(
    query_procedure: &AssertionQueryProcedure,
    edge_id: CfgEdgeId,
    phi_2: &Formula,
) -> Result<Formula, DriverError> {
    let edge = query_procedure
        .cfg
        .edge(edge_id)
        .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
    let mut current = phi_2.clone();
    if let Some(effects) = query_procedure.node_effects.get(&edge.target) {
        for effect in effects.iter().rev() {
            current = backward_pre_through_effect(current, effect)?;
        }
    }
    if let Some(effects) = query_procedure.edge_effects.get(&edge_id) {
        for effect in effects.iter().rev() {
            current = backward_pre_through_effect(current, effect)?;
        }
    }
    if edge.relation != Formula::True {
        current = Formula::and(edge.relation.clone(), current);
    }
    Ok(current)
}

fn effect_formulas_for_rules(effects: &[TransferEffect]) -> Result<Vec<Formula>, DriverError> {
    let mut formulas = Vec::new();
    for effect in effects {
        match effect {
            TransferEffect::Assign { target, value } => match value {
                AssignValue::Term(term) => {
                    formulas.push(Formula::eq(Term::Var(target.clone()), term.clone()));
                }
                AssignValue::Predicate(formula) => {
                    formulas.push(Formula::iff(Formula::Var(target.clone()), formula.clone()));
                }
            },
            TransferEffect::Assume(formula) => formulas.push(formula.clone()),
            TransferEffect::Nop => {}
            other => {
                return Err(DriverError::UnsupportedRuleEffect {
                    effect: format!("{other:?}"),
                });
            }
        }
    }
    Ok(formulas)
}

fn backward_pre_through_effect(
    formula: Formula,
    effect: &TransferEffect,
) -> Result<Formula, DriverError> {
    match effect {
        TransferEffect::Assign { target, value } => match value {
            AssignValue::Term(term) => Ok(substitute_term_assignment(&formula, target, term)),
            AssignValue::Predicate(predicate) => {
                Ok(substitute_bool_assignment(&formula, target, predicate))
            }
        },
        TransferEffect::Assume(guard) => Ok(Formula::and(guard.clone(), formula)),
        TransferEffect::Nop => Ok(formula),
        other => Err(DriverError::UnsupportedRuleEffect {
            effect: format!("{other:?}"),
        }),
    }
}

fn substitute_term_assignment(formula: &Formula, target: &Var, replacement: &Term) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => Formula::not(substitute_term_assignment(inner, target, replacement)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| substitute_term_assignment(item, target, replacement))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| substitute_term_assignment(item, target, replacement))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_term_assignment(lhs, target, replacement),
            substitute_term_assignment(rhs, target, replacement),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
    }
}

fn substitute_bool_assignment(formula: &Formula, target: &Var, replacement: &Formula) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => {
            if var == target {
                replacement.clone()
            } else {
                Formula::Var(var.clone())
            }
        }
        Formula::Not(inner) => Formula::not(substitute_bool_assignment(inner, target, replacement)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| substitute_bool_assignment(item, target, replacement))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| substitute_bool_assignment(item, target, replacement))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_bool_assignment(lhs, target, replacement),
            substitute_bool_assignment(rhs, target, replacement),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(lhs.clone(), rhs.clone()),
        Formula::Lt(lhs, rhs) => Formula::lt(lhs.clone(), rhs.clone()),
        Formula::Le(lhs, rhs) => Formula::le(lhs.clone(), rhs.clone()),
        Formula::Gt(lhs, rhs) => Formula::gt(lhs.clone(), rhs.clone()),
        Formula::Ge(lhs, rhs) => Formula::ge(lhs.clone(), rhs.clone()),
    }
}

fn substitute_term(term: &Term, target: &Var, replacement: &Term) -> Term {
    match term {
        Term::Var(var) => {
            if var == target {
                replacement.clone()
            } else {
                Term::Var(var.clone())
            }
        }
        Term::Int(value) => Term::int(*value),
        Term::Real(value) => Term::Real(value.clone()),
        Term::Select(memory, index) => Term::select(
            substitute_memory(memory, target, replacement),
            substitute_term(index, target, replacement),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_term(lhs, target, replacement),
            substitute_term(rhs, target, replacement),
        ),
        Term::Neg(inner) => Term::neg(substitute_term(inner, target, replacement)),
    }
}

fn substitute_memory(memory: &Memory, target: &Var, replacement: &Term) -> Memory {
    match memory {
        Memory::Var(name) => Memory::var(name.clone()),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_memory(inner, target, replacement),
            substitute_term(index, target, replacement),
            substitute_term(value, target, replacement),
        ),
    }
}

fn effect_predicates(effects: &[TransferEffect]) -> Vec<Formula> {
    let mut predicates = Vec::new();
    for effect in effects {
        match effect {
            TransferEffect::Assign { target, value } => match value {
                crate::analysis::transfer::AssignValue::Term(term) => {
                    predicates.push(Formula::eq(
                        crate::analysis::formula::Term::Var(target.clone()),
                        term.clone(),
                    ));
                }
                crate::analysis::transfer::AssignValue::Predicate(formula) => {
                    predicates.push(Formula::iff(Formula::Var(target.clone()), formula.clone()));
                }
            },
            TransferEffect::Assume(formula) | TransferEffect::Obligation(formula) => {
                predicates.push(formula.clone());
            }
            TransferEffect::Alloca { .. }
            | TransferEffect::GetElementPtr { .. }
            | TransferEffect::Load { .. }
            | TransferEffect::Store { .. }
            | TransferEffect::Nop
            | TransferEffect::Call { .. } => {}
        }
    }
    predicates
}

fn edge_predicates(relation: Formula, edge_effects: Option<&Vec<TransferEffect>>) -> Vec<Formula> {
    let mut predicates = Vec::new();
    if relation != Formula::True {
        predicates.push(relation);
    }
    if let Some(effects) = edge_effects {
        predicates.extend(effect_predicates(effects));
    }
    predicates
}

fn format_generated(formulas: &[Formula]) -> String {
    if formulas.is_empty() {
        "<none>".to_string()
    } else {
        join_formulas(formulas)
    }
}

fn join_formulas(formulas: &[Formula]) -> String {
    formulas
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn append_indented_block(lines: &mut Vec<String>, block: &str, indent: usize) {
    let prefix = " ".repeat(indent);
    for line in block.lines() {
        lines.push(format!("{prefix}{line}"));
    }
}

fn cfg_node_label(cfg: &Cfg, node: CfgNodeId) -> Result<String, DriverError> {
    cfg.node(node)
        .map(|node| normalize_label(&node.label))
        .ok_or(DriverError::UnknownNode { node })
}

fn normalize_label(label: &str) -> String {
    label.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::llvm_utils::program_graph::generate_program_graph;

    fn analyze_first_with_options(ir: &str, options: SimpleDriverOptions) -> SimpleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        analyze_function_graph_simple_with_options(&graphs[0], options).unwrap()
    }

    fn analyze_first(ir: &str) -> SimpleProcedureReport {
        analyze_first_with_options(ir, SimpleDriverOptions::default())
    }

    fn analyze_named_with_options(
        ir: &str,
        name: &str,
        options: SimpleDriverOptions,
    ) -> SimpleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let pure = crate::analysis::llvm_adapter::infer_memory_pure_functions(&graphs);
        let graph = graphs.iter().find(|graph| graph.name == name).unwrap();
        analyze_function_graph_simple_with_purity(graph, &pure, options).unwrap()
    }

    fn analyze_first_rules_with_options(
        ir: &str,
        options: RuleDriverOptions,
    ) -> RuleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_rule_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        analyze_function_graph_rules_with_options(&graphs[0], options).unwrap()
    }

    fn analyze_first_rules(ir: &str) -> RuleProcedureReport {
        analyze_first_rules_with_options(ir, RuleDriverOptions::default())
    }

    fn analyze_first_rules_err(ir: &str) -> DriverError {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_rule_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        analyze_function_graph_rules(&graphs[0]).unwrap_err()
    }

    #[test]
    fn straight_line_assert_is_reported_safe() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %x = add i32 2, 3
                    %ok = icmp eq i32 %x, 5
                    call void @may_assert(i1 %ok)
                    ret i32 %x
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
        assert_eq!(report.checked_obligations, 1);
        assert_eq!(report.bounded_paths, 0);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::True);
    }

    #[test]
    fn branch_pruned_assertions_are_reported_safe() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %then_ok = icmp sgt i32 %x, 0
                    call void @may_assert(i1 %then_ok)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
        assert_eq!(report.checked_obligations, 2);
        assert_eq!(report.explored_paths, 2);
        assert_eq!(report.bounded_paths, 0);
    }

    #[test]
    fn branch_can_report_an_unsafe_obligation() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.feasible_obligations, 1);
        assert_eq!(report.assertions.len(), 2);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        assert!(report.assertions[0].evidence.is_some());
    }

    #[test]
    fn memory_load_store_assertion_is_reported_safe() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %ptr = alloca i32
                    store i32 7, ptr %ptr
                    %value = load i32, ptr %ptr
                    %ok = icmp eq i32 %value, 7
                    call void @may_assert(i1 %ok)
                    ret i32 %value
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
    }

    #[test]
    fn impure_call_havoc_can_make_memory_assertion_fail() {
        let report = analyze_named_with_options(
            r#"
                declare void @may_assert(i1)

                define void @touch(ptr %p) {
                entry:
                    store i32 1, ptr %p
                    ret void
                }

                define void @main() {
                entry:
                    %ptr = alloca i32
                    store i32 7, ptr %ptr
                    call void @touch(ptr %ptr)
                    %value = load i32, ptr %ptr
                    %ok = icmp eq i32 %value, 7
                    call void @may_assert(i1 %ok)
                    ret void
                }
            "#,
            "main",
            SimpleDriverOptions::default(),
        );
        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.feasible_obligations, 1);
    }

    #[test]
    fn memory_pure_call_does_not_havoc_caller_memory() {
        let report = analyze_named_with_options(
            r#"
                declare void @may_assert(i1)

                define void @helper() {
                entry:
                    %ptr = alloca i32
                    store i32 1, ptr %ptr
                    %tmp = load i32, ptr %ptr
                    ret void
                }

                define void @main() {
                entry:
                    %ptr = alloca i32
                    store i32 7, ptr %ptr
                    call void @helper()
                    %value = load i32, ptr %ptr
                    %ok = icmp eq i32 %value, 7
                    call void @may_assert(i1 %ok)
                    ret void
                }
            "#,
            "main",
            SimpleDriverOptions::default(),
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
    }

    #[test]
    fn loop_budget_exhaustion_is_reported_unknown() {
        let report = analyze_first_with_options(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %keep_looping) {
                entry:
                    br label %loop
                loop:
                    call void @may_assert(i1 true)
                    br i1 %keep_looping, label %loop, label %exit
                exit:
                    ret void
                }
            "#,
            SimpleDriverOptions {
                max_step: 2,
                trace_predicates: false,
            },
        );
        assert_eq!(report.judgement, QueryJudgement::Unknown);
        assert_eq!(report.bounded_paths, 1);
        assert_eq!(report.feasible_obligations, 0);
    }

    #[test]
    fn loop_body_violation_is_still_found_before_cutoff() {
        let report = analyze_first_with_options(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %keep_looping, i1 %bad) {
                entry:
                    br label %loop
                loop:
                    call void @may_assert(i1 %bad)
                    br i1 %keep_looping, label %loop, label %exit
                exit:
                    ret void
                }
            "#,
            SimpleDriverOptions {
                max_step: 2,
                trace_predicates: false,
            },
        );
        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        assert!(report.assertions[0].evidence.is_some());
        assert!(report.feasible_obligations >= 1);
    }

    #[test]
    fn zero_max_step_is_rejected() {
        initialize_target();
        let context = Context::new();
        let module = context
            .parse_ir_str(
                r#"
                declare void @may_assert(i1)

                define void @main() {
                entry:
                    ret void
                }
            "#,
                "driver_test",
            )
            .unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let error = analyze_function_graph_simple_with_options(
            &graphs[0],
            SimpleDriverOptions {
                max_step: 0,
                trace_predicates: false,
            },
        )
        .unwrap_err();

        assert_eq!(error, DriverError::InvalidMaxStep { max_step: 0 });
    }

    #[test]
    fn report_display_is_stable_and_readable() {
        let report = SimpleProcedureReport::summary_only(
            "subject",
            QueryJudgement::Unknown,
            3,
            2,
            1,
            1,
            3,
            0,
        );

        assert_eq!(
            report.to_string(),
            "procedure subject\n  judgement: Unknown\n  max step: 3\n  explored paths: 2\n  pruned paths: 1\n  bounded paths: 1\n  obligations checked: 3\n  feasible obligations: 0"
        );
    }

    #[test]
    fn false_assertions_render_with_evidence() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    ret void
                }
            "#,
        );

        let rendered = report.to_string();
        assert!(rendered.contains("result: false"));
        assert!(rendered.contains("evidence trace:"));
        assert!(rendered.contains("assertion 1"));
    }

    #[test]
    fn rule_driver_proves_a_straight_line_assertion_safe() {
        let report = analyze_first_rules(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %x = add i32 2, 3
                    %ok = icmp eq i32 %x, 5
                    call void @may_assert(i1 %ok)
                    ret i32 %x
                }
            "#,
        );

        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::True);
    }

    #[test]
    fn rule_driver_finds_an_unsafe_branch_assertion() {
        let report = analyze_first_rules(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
        );

        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.assertions.len(), 2);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        assert!(report.assertions[0].rule_applications > 0);
    }

    #[test]
    fn rule_driver_can_generate_a_witness_on_demand() {
        let report = analyze_first_rules_with_options(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
            RuleDriverOptions {
                generate_witnesses: true,
            },
        );

        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        let witness = report.assertions[0]
            .witness
            .as_ref()
            .expect("false rule result should carry a witness when requested");
        assert!(witness.steps.len() >= 2);
        match witness.steps.last().unwrap() {
            RuleWitnessStep::Outcome { model, result, .. } => {
                assert_eq!(*result, Feasibility::Feasible);
                assert!(model.is_some());
            }
            other => panic!("expected witness outcome step, found {other:?}"),
        }
    }

    #[test]
    fn rule_driver_does_not_attach_witnesses_by_default() {
        let report = analyze_first_rules(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    ret void
                }
            "#,
        );

        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert!(report.assertions[0].witness.is_none());
    }

    #[test]
    fn safe_rule_results_do_not_attach_witnesses() {
        let report = analyze_first_rules_with_options(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %x = add i32 2, 3
                    %ok = icmp eq i32 %x, 5
                    call void @may_assert(i1 %ok)
                    ret i32 %x
                }
            "#,
            RuleDriverOptions {
                generate_witnesses: true,
            },
        );

        assert_eq!(report.judgement, QueryJudgement::No);
        assert!(report.assertions[0].witness.is_none());
    }

    #[test]
    fn rule_report_display_renders_witness_trace() {
        let report = analyze_first_rules_with_options(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    ret void
                }
            "#,
            RuleDriverOptions {
                generate_witnesses: true,
            },
        );

        let rendered = report.to_string();
        assert!(rendered.contains("witness trace:"));
        assert!(rendered.contains("model:"));
    }

    #[test]
    fn rule_driver_rejects_loops_before_invariants_exist() {
        let error = analyze_first_rules_err(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %keep_looping) {
                entry:
                    br label %loop
                loop:
                    call void @may_assert(i1 true)
                    br i1 %keep_looping, label %loop, label %exit
                exit:
                    ret void
                }
            "#,
        );

        assert_eq!(error, DriverError::CyclicRuleProcedure);
    }
}
