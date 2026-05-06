//! Executable driver slices for the current milestone.
//!
//! This module currently exposes two CLI-usable paths:
//!
//! - a temporary bounded path explorer for the wider single-procedure subset
//! - a rule-driven scheduler over the paper rules with module-level summary
//!   reuse for the supported interprocedural slice
//!
//! The bounded explorer handles one lowered procedure at a time, explores
//! branch paths under a temporary `max_step` loop budget, applies normalized
//! transfer effects, and uses the SMT oracle to decide whether embedded
//! `may_assert` obligations are feasible.
//!
//! The rule-driven slice is deliberately narrower but closer to the paper. For
//! each assertion query it:
//!
//! - builds a synthetic violation-exit query CFG;
//! - derives scalar `β` / `θ` candidates from normalized edge/node effects;
//! - rewrites the supported local memory slice (`alloca` / `load` / `store` /
//!   `gep` plus conservative impure-call memory havoc) into scalar formulas;
//! - schedules the currently supported Figure 5-10 rules;
//! - uses Figures 8/9/10 to create, cache, instantiate, and reuse summaries
//!   across supported calls with scalar returns plus visible memory ports;
//! - alpha-renames summary variables before instantiating them at a call site;
//! - replays one feasible must-side witness path plus the final SMT model for
//!   false results.
//!
//! It is still not the full paper scheduler:
//!
//! - the path explorer still owns the temporary `max_step` loop policy
//! - the rule scheduler still rejects procedures whose summary structure
//!   contains loop regions
//! - interprocedural summaries currently cover the scalar-return plus visible
//!   integer-array memory interface slice, not full heap summaries
//! - pointer phis, loop invariants, and richer projection/elimination remain
//!   future work
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

use crate::analysis::cfg::{Cfg, CfgEdge, CfgEdgeId, CfgNodeId, LoopRegion, SummaryStructure};
use crate::analysis::formula::{Formula, FreshNameGenerator, Memory, Sort, Term, Var};
use crate::analysis::llvm_adapter::{
    adapt_function_graph, adapt_function_graph_with_purity, AdaptedAssertionSite, AdaptedProcedure,
    AdapterError, ProcedureInterface,
};
use crate::analysis::oracle::{Feasibility, Oracle, OracleError};
use crate::analysis::rules::{self, ProcedureFrame, QueryJudgement, ReachabilityQuery, RuleError};
use crate::analysis::state::{NodeState, PointerValue};
use crate::analysis::summaries::{MustSummary, NotMaySummary, SummaryProvider, SummaryRepository};
use crate::analysis::transfer::{
    apply_effects, AssignValue, CallArgument, CallMemoryEffect, PointerArgument, TransferEffect,
    TransferError,
};
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
    #[error("CFG rewrite failed: {0}")]
    Cfg(String),
    #[error(
        "rule driver currently supports only acyclic scalarized procedures; unsupported effect after rewrite: {effect}"
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
    /// Witness for `Yes` results in the current local rule slice.
    pub witness: Option<RuleWitnessTrace>,
}

#[derive(Clone, Debug)]
struct AssertionQueryProcedure {
    procedure: String,
    interface: ProcedureInterface,
    summary_capable: bool,
    /// Concrete loop SCCs present in this lowered query procedure.
    loops: Vec<LoopRegion>,
    /// Acyclic condensation view that future invariant scheduling will use.
    summary_structure: SummaryStructure,
    cfg: Cfg,
    node_effects: BTreeMap<CfgNodeId, Vec<TransferEffect>>,
    edge_effects: BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RuleRewriteState {
    visible_memory_roots: BTreeSet<String>,
    pointers: BTreeMap<String, PointerValue>,
    memory_regions: BTreeMap<String, Memory>,
    memory_epoch: usize,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct RuleSearchStats {
    rounds: usize,
    applications: usize,
    unknown_premises: usize,
}

impl RuleRewriteState {
    fn from_interface(interface: &ProcedureInterface) -> Self {
        let visible_memory_roots = interface
            .visible_memory_roots
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut state = Self {
            visible_memory_roots,
            pointers: BTreeMap::new(),
            memory_regions: BTreeMap::new(),
            memory_epoch: 0,
        };
        for root in &interface.visible_memory_roots {
            state.memory_regions.insert(
                root.clone(),
                Memory::var(ProcedureInterface::input_memory_port(root)),
            );
            state.pointers.insert(
                root.clone(),
                PointerValue::new(
                    root.clone(),
                    Term::Var(ProcedureInterface::offset_var(root)),
                ),
            );
        }
        state
    }

    fn lower_effects(
        &mut self,
        effects: &[TransferEffect],
    ) -> Result<Vec<TransferEffect>, DriverError> {
        let mut lowered = Vec::new();
        for effect in effects {
            match effect {
                TransferEffect::Assign { .. } | TransferEffect::Assume(_) | TransferEffect::Nop => {
                    lowered.push(effect.clone())
                }
                TransferEffect::Alloca { target, region } => {
                    self.bind_alloca_pointer(target.clone(), region.clone());
                }
                TransferEffect::GetElementPtr {
                    target,
                    base,
                    offset,
                } => {
                    self.bind_pointer_offset(target.clone(), base, offset.clone());
                }
                TransferEffect::Load { target, source } => {
                    lowered.push(TransferEffect::Assign {
                        target: target.clone(),
                        value: AssignValue::Term(self.load_term(source)),
                    });
                }
                TransferEffect::Store { target, value } => {
                    self.store_to_pointer(target, value.clone());
                }
                TransferEffect::Call {
                    callee,
                    arguments,
                    return_target,
                    memory_effect,
                } => {
                    let rewritten_arguments = arguments
                        .iter()
                        .map(|argument| self.rewrite_call_argument(argument, *memory_effect))
                        .collect::<Vec<_>>();
                    if *memory_effect == CallMemoryEffect::HavocMemory {
                        // APPROX_HEAVY: until interprocedural memory summaries
                        // exist, impure calls still havoc the tracked
                        // integer-array regions before later loads are lowered.
                        self.havoc_memory();
                    }
                    let finalized_arguments = rewritten_arguments
                        .into_iter()
                        .map(|argument| self.finalize_call_argument(argument))
                        .collect::<Vec<_>>();
                    lowered.push(TransferEffect::Call {
                        callee: callee.clone(),
                        arguments: finalized_arguments,
                        return_target: return_target.clone(),
                        memory_effect: *memory_effect,
                    });
                }
                TransferEffect::Obligation(_) => {
                    return Err(DriverError::UnsupportedRuleEffect {
                        effect: format!("{effect:?}"),
                    });
                }
            }
        }
        Ok(lowered)
    }

    fn bind_alloca_pointer(&mut self, target: String, region: String) {
        self.ensure_region(&region);
        self.pointers
            .insert(target, PointerValue::new(region, Term::int(0)));
    }

    fn bind_pointer_offset(&mut self, target: String, base: &str, offset: Term) {
        let base_pointer = self.resolve_pointer(base);
        let offset = if base_pointer.offset() == &Term::int(0) {
            offset
        } else {
            Term::add(base_pointer.offset().clone(), offset)
        };
        self.pointers.insert(
            target,
            PointerValue::new(base_pointer.region().to_string(), offset),
        );
    }

    fn load_term(&mut self, source: &str) -> Term {
        let pointer = self.resolve_pointer(source);
        let memory = self.current_memory(pointer.region()).clone();
        Term::select(memory, pointer.offset().clone())
    }

    fn store_to_pointer(&mut self, target: &str, value: Term) {
        let pointer = self.resolve_pointer(target);
        let next_memory = Memory::store(
            self.current_memory(pointer.region()).clone(),
            pointer.offset().clone(),
            value,
        );
        self.memory_regions
            .insert(pointer.region().to_string(), next_memory);
    }

    fn havoc_memory(&mut self) {
        self.memory_epoch += 1;
        let regions = self.memory_regions.keys().cloned().collect::<Vec<_>>();
        for region in regions {
            let symbol = if self.visible_memory_roots.contains(&region) {
                ProcedureInterface::output_memory_port(&region)
            } else {
                self.memory_symbol(&region)
            };
            self.memory_regions
                .insert(region.clone(), Memory::var(symbol));
        }
    }

    fn resolve_pointer(&mut self, name: &str) -> PointerValue {
        if let Some(pointer) = self.pointers.get(name) {
            return pointer.clone();
        }
        if self.visible_memory_roots.contains(name) {
            let pointer = PointerValue::new(
                name.to_string(),
                Term::Var(ProcedureInterface::offset_var(name)),
            );
            self.pointers.insert(name.to_string(), pointer.clone());
            return pointer;
        }
        let region = format!("{name}$region");
        self.ensure_region(&region);
        let pointer = PointerValue::new(region, Term::int(0));
        self.pointers.insert(name.to_string(), pointer.clone());
        pointer
    }

    fn ensure_region(&mut self, region: &str) {
        if self.memory_regions.contains_key(region) {
            return;
        }
        if self.visible_memory_roots.contains(region) {
            self.memory_regions.insert(
                region.to_string(),
                Memory::var(ProcedureInterface::input_memory_port(region)),
            );
            return;
        }
        self.memory_regions
            .insert(region.to_string(), Memory::var(self.memory_symbol(region)));
    }

    fn current_memory(&self, region: &str) -> &Memory {
        self.memory_regions
            .get(region)
            .expect("memory region should exist before use")
    }

    fn memory_symbol(&self, region: &str) -> String {
        format!("{region}$mem{}", self.memory_epoch)
    }

    fn rewrite_call_argument(
        &mut self,
        argument: &CallArgument,
        memory_effect: CallMemoryEffect,
    ) -> CallArgument {
        match argument {
            CallArgument::Term(term) => CallArgument::Term(term.clone()),
            CallArgument::Predicate(predicate) => CallArgument::Predicate(predicate.clone()),
            CallArgument::Pointer(pointer) => {
                let resolved = self.resolve_pointer(pointer.region());
                let offset = if pointer.offset() == &Term::int(0) {
                    resolved.offset().clone()
                } else {
                    Term::add(resolved.offset().clone(), pointer.offset().clone())
                };
                let before = self.current_memory(resolved.region()).clone();
                let after = if memory_effect == CallMemoryEffect::HavocMemory {
                    if self.visible_memory_roots.contains(resolved.region()) {
                        Memory::var(ProcedureInterface::output_memory_port(resolved.region()))
                    } else {
                        Memory::var(self.memory_symbol(resolved.region()))
                    }
                } else {
                    before.clone()
                };
                CallArgument::Pointer(PointerArgument::resolved(
                    resolved.region().to_string(),
                    offset,
                    before,
                    after,
                ))
            }
        }
    }

    fn finalize_call_argument(&self, argument: CallArgument) -> CallArgument {
        match argument {
            CallArgument::Pointer(pointer) => CallArgument::Pointer(PointerArgument::resolved(
                pointer.region().to_string(),
                pointer.offset().clone(),
                pointer
                    .memory_before()
                    .expect("prepared pointer arguments should record pre-call memory")
                    .clone(),
                self.current_memory(pointer.region()).clone(),
            )),
            other => other,
        }
    }

    fn materialize_visible_memory_effects(&mut self) -> Vec<TransferEffect> {
        let mut effects = Vec::new();
        for root in self.visible_memory_roots.clone() {
            self.ensure_region(&root);
            effects.push(TransferEffect::Assume(Formula::memory_eq(
                Memory::var(ProcedureInterface::output_memory_port(&root)),
                self.current_memory(&root).clone(),
            )));
        }
        effects
    }
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
    let mut engine = RuleModuleEngine::new(std::slice::from_ref(graph), &BTreeSet::new())?;
    engine.analyze_procedure(&graph.name)
}

pub fn analyze_function_graph_rules_with_purity(
    graph: &FunctionGraph,
    memory_pure_functions: &BTreeSet<String>,
) -> Result<RuleProcedureReport, DriverError> {
    let mut engine = RuleModuleEngine::new(std::slice::from_ref(graph), memory_pure_functions)?;
    engine.analyze_procedure(&graph.name)
}

pub fn analyze_function_graphs_rules_with_purity(
    graphs: &[FunctionGraph],
    memory_pure_functions: &BTreeSet<String>,
) -> Result<Vec<RuleProcedureReport>, DriverError> {
    let mut engine = RuleModuleEngine::new(graphs, memory_pure_functions)?;
    engine.analyze_all()
}

pub fn analyze_function_graphs_rules_with_purity_best_effort(
    graphs: &[FunctionGraph],
    memory_pure_functions: &BTreeSet<String>,
) -> Result<Vec<(String, Result<RuleProcedureReport, DriverError>)>, DriverError> {
    let mut engine = RuleModuleEngine::new(graphs, memory_pure_functions)?;
    let mut reports = Vec::new();
    for procedure in engine.order.clone() {
        let report = engine.analyze_procedure(&procedure);
        reports.push((procedure, report));
    }
    Ok(reports)
}

pub fn analyze_adapted_procedure_rules(
    procedure: &str,
    adapted: &AdaptedProcedure,
) -> Result<RuleProcedureReport, DriverError> {
    let mut engine = RuleModuleEngine::from_adapted(vec![adapted.clone()])?;
    engine.analyze_procedure(procedure)
}

#[derive(Clone, Debug)]
struct PreparedRuleProcedure {
    adapted: AdaptedProcedure,
    base_rule_procedure: AssertionQueryProcedure,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PendingRuleQuery {
    query: ReachabilityQuery,
}

#[derive(Clone, Debug)]
struct QueryAnalysisOutcome {
    judgement: QueryJudgement,
    stats: RuleSearchStats,
}

struct RuleModuleEngine {
    procedures: BTreeMap<String, PreparedRuleProcedure>,
    order: Vec<String>,
    oracle: Oracle,
    summaries: SummaryRepository,
    active_queries: Vec<ReachabilityQuery>,
    completed_queries: Vec<(ReachabilityQuery, QueryJudgement)>,
    pending_queries: VecDeque<PendingRuleQuery>,
}

impl RuleModuleEngine {
    fn new(
        graphs: &[FunctionGraph],
        memory_pure_functions: &BTreeSet<String>,
    ) -> Result<Self, DriverError> {
        let mut adapted = Vec::new();
        for graph in graphs {
            adapted.push(adapt_function_graph_with_purity(
                graph,
                memory_pure_functions,
            )?);
        }
        Self::from_adapted(adapted)
    }

    fn from_adapted(procedures: Vec<AdaptedProcedure>) -> Result<Self, DriverError> {
        let mut prepared = BTreeMap::new();
        let mut order = Vec::new();
        let mut summaries = SummaryRepository::new();
        for adapted in procedures {
            summaries.init_procedure(adapted.name.clone());
            order.push(adapted.name.clone());
            prepared.insert(
                adapted.name.clone(),
                PreparedRuleProcedure {
                    base_rule_procedure: build_base_rule_procedure(&adapted)?,
                    adapted,
                },
            );
        }
        Ok(Self {
            procedures: prepared,
            order,
            oracle: Oracle::new(),
            summaries,
            active_queries: Vec::new(),
            completed_queries: Vec::new(),
            pending_queries: VecDeque::new(),
        })
    }

    fn analyze_all(&mut self) -> Result<Vec<RuleProcedureReport>, DriverError> {
        let mut reports = Vec::new();
        for procedure in self.order.clone() {
            reports.push(self.analyze_procedure(&procedure)?);
        }
        Ok(reports)
    }

    fn analyze_procedure(&mut self, procedure: &str) -> Result<RuleProcedureReport, DriverError> {
        let adapted = self
            .procedures
            .get(procedure)
            .ok_or_else(|| DriverError::UnsupportedRuleEffect {
                effect: format!("unknown procedure {procedure}"),
            })?
            .adapted
            .clone();
        let assertion_sites = collect_assertion_sites(&adapted);
        let mut assertions = Vec::new();
        for (node, site) in assertion_sites {
            let raw_query_procedure = build_assertion_query_procedure(&adapted, node, &site)?;
            if raw_query_procedure.summary_structure.has_loops() {
                return Err(DriverError::CyclicRuleProcedure);
            }
            let query_procedure = rewrite_rule_query_procedure(&raw_query_procedure)?;
            ensure_rule_query_supported(&query_procedure)?;
            let query = ReachabilityQuery::new(
                format!("{procedure}#assert{}", site.id),
                Formula::True,
                Formula::True,
            );
            let outcome = self.solve_query(&query_procedure, query)?;
            assertions.push(rule_assertion_report(
                &site,
                outcome.judgement,
                outcome.stats,
                &query_procedure,
                &self.oracle,
            )?);
        }
        Ok(RuleProcedureReport {
            procedure: procedure.to_string(),
            judgement: aggregate_assertion_judgement(&assertions),
            assertions,
        })
    }

    fn solve_query(
        &mut self,
        query_procedure: &AssertionQueryProcedure,
        query: ReachabilityQuery,
    ) -> Result<QueryAnalysisOutcome, DriverError> {
        if let Some((_, judgement)) = self
            .completed_queries
            .iter()
            .find(|(known, _)| known == &query)
        {
            return Ok(QueryAnalysisOutcome {
                judgement: *judgement,
                stats: RuleSearchStats::default(),
            });
        }
        if self.active_queries.contains(&query) {
            return Ok(QueryAnalysisOutcome {
                judgement: QueryJudgement::Unknown,
                stats: RuleSearchStats::default(),
            });
        }
        ensure_rule_query_supported(query_procedure)?;
        if query_procedure.summary_structure.has_loops() {
            return Err(DriverError::CyclicRuleProcedure);
        }

        self.active_queries.push(query.clone());
        let mut frame = ProcedureFrame::new(query_procedure.cfg.clone(), query.clone());
        rules::figure5::INIT_PI_NE(&mut frame)?;
        rules::figure6::INIT_OMEGA(&mut frame)?;

        let mut stats = RuleSearchStats::default();
        loop {
            if rules::figure6::BUGFOUND(&frame, &self.oracle)? == QueryJudgement::Yes {
                self.record_summary_for_judgement(query_procedure, &frame, QueryJudgement::Yes)?;
                self.completed_queries
                    .push((query.clone(), QueryJudgement::Yes));
                self.active_queries.pop();
                return Ok(QueryAnalysisOutcome {
                    judgement: QueryJudgement::Yes,
                    stats,
                });
            }
            if rules::figure5::VERIFIED(&frame, &self.oracle)? == QueryJudgement::No {
                self.record_summary_for_judgement(query_procedure, &frame, QueryJudgement::No)?;
                self.completed_queries
                    .push((query.clone(), QueryJudgement::No));
                self.active_queries.pop();
                return Ok(QueryAnalysisOutcome {
                    judgement: QueryJudgement::No,
                    stats,
                });
            }

            stats.rounds += 1;
            let mut changed = false;
            changed |=
                apply_must_post_round(&mut frame, query_procedure, &self.oracle, &mut stats)?;
            changed |=
                apply_notmay_pre_round(&mut frame, query_procedure, &self.oracle, &mut stats)?;
            changed |= apply_notmay_closure_round(&mut frame, &self.oracle, &mut stats)?;
            changed |= self.apply_call_summary_round(&mut frame, query_procedure, &mut stats)?;
            changed |= self.apply_call_subquery_round(&frame, query_procedure)?;

            if !changed {
                break;
            }
        }

        let final_judgement =
            if rules::figure6::BUGFOUND(&frame, &self.oracle)? == QueryJudgement::Yes {
                QueryJudgement::Yes
            } else if rules::figure5::VERIFIED(&frame, &self.oracle)? == QueryJudgement::No {
                QueryJudgement::No
            } else {
                QueryJudgement::Unknown
            };
        self.record_summary_for_judgement(query_procedure, &frame, final_judgement)?;
        self.completed_queries
            .push((query.clone(), final_judgement));
        self.active_queries.pop();
        Ok(QueryAnalysisOutcome {
            judgement: final_judgement,
            stats,
        })
    }

    fn apply_call_summary_round(
        &mut self,
        frame: &mut ProcedureFrame,
        query_procedure: &AssertionQueryProcedure,
        stats: &mut RuleSearchStats,
    ) -> Result<bool, DriverError> {
        let mut changed = false;
        for (edge_id, call) in call_edges(query_procedure) {
            let Some(callee) = self.procedures.get(&call.callee) else {
                continue;
            };
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
            for summary in self.summaries.must_candidates(&call.callee) {
                if let Some(instantiated) = instantiate_must_summary_at_call(
                    &call,
                    &callee.base_rule_procedure.interface,
                    &summary.summary,
                ) {
                    if instantiated.postcondition == Formula::True {
                        continue;
                    }
                    for phi_1 in &source_regions {
                        for phi_2 in &target_regions {
                            let theta = instantiated.postcondition.clone();
                            changed |= attempt_mutating_rule(frame, stats, |frame| {
                                rules::figure10::MUST_POST_USESUMMARY(
                                    frame,
                                    edge_id,
                                    phi_1,
                                    phi_2,
                                    &instantiated,
                                    theta.clone(),
                                    &self.oracle,
                                )
                            })?;
                        }
                    }
                }
            }
            for summary in self.summaries.notmay_candidates(&call.callee) {
                if let Some(instantiated) = instantiate_notmay_summary_at_call(
                    &call,
                    &callee.base_rule_procedure.interface,
                    &summary.summary,
                ) {
                    if instantiated.precondition == Formula::False {
                        continue;
                    }
                    for phi_1 in &source_regions {
                        for phi_2 in &target_regions {
                            let theta = instantiated.precondition.clone();
                            changed |= attempt_mutating_rule(frame, stats, |frame| {
                                rules::figure10::NOTMAY_PRE_USESUMMARY(
                                    frame,
                                    edge_id,
                                    phi_1,
                                    phi_2,
                                    &instantiated,
                                    theta.clone(),
                                    &self.oracle,
                                )
                            })?;
                        }
                    }
                }
            }
        }
        Ok(changed)
    }

    fn apply_call_subquery_round(
        &mut self,
        frame: &ProcedureFrame,
        query_procedure: &AssertionQueryProcedure,
    ) -> Result<bool, DriverError> {
        let before = self.summary_counts();
        for (edge_id, call) in call_edges(query_procedure) {
            let Some(callee) = self.procedures.get(&call.callee).cloned() else {
                continue;
            };
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
            let omega_target = frame.omega(edge.target).cloned().unwrap_or(Formula::False);
            for phi_1 in &source_regions {
                for phi_2 in &target_regions {
                    let may_query =
                        rules::figure8::MAY_CALL(&call.callee, phi_1.clone(), phi_2.clone());
                    if let Some(mapped) = map_query_to_callee_interface(
                        &call,
                        &callee.base_rule_procedure,
                        &may_query,
                    ) {
                        self.maybe_enqueue_query(mapped);
                    }

                    let must_query = rules::figure9::MUST_CALL(
                        &call.callee,
                        omega_source.clone(),
                        phi_2.clone(),
                    );
                    if let Some(mapped) = map_query_to_callee_interface(
                        &call,
                        &callee.base_rule_procedure,
                        &must_query,
                    ) {
                        self.maybe_enqueue_query(mapped);
                    }

                    if let Ok(mixed_query) = rules::figure10::MAY_MUST_CALL(
                        &call.callee,
                        phi_1,
                        phi_2,
                        &omega_source,
                        &omega_target,
                        &self.oracle,
                    ) {
                        if let Some(mapped) = map_query_to_callee_interface(
                            &call,
                            &callee.base_rule_procedure,
                            &mixed_query,
                        ) {
                            self.maybe_enqueue_query(mapped);
                        }
                    }
                }
            }
        }
        self.drain_pending_queries()?;
        Ok(self.summary_counts() != before)
    }

    fn drain_pending_queries(&mut self) -> Result<(), DriverError> {
        while let Some(pending) = self.pending_queries.pop_front() {
            if self
                .completed_queries
                .iter()
                .any(|(known, _)| known == &pending.query)
                || self.active_queries.contains(&pending.query)
            {
                continue;
            }
            let Some(prepared) = self.procedures.get(&pending.query.procedure).cloned() else {
                continue;
            };
            let _ = self.solve_query(&prepared.base_rule_procedure, pending.query)?;
        }
        Ok(())
    }

    fn maybe_enqueue_query(&mut self, query: ReachabilityQuery) {
        if self
            .completed_queries
            .iter()
            .any(|(known, _)| known == &query)
            || self.active_queries.contains(&query)
            || self
                .pending_queries
                .iter()
                .any(|pending| pending.query == query)
        {
            return;
        }
        self.pending_queries.push_back(PendingRuleQuery { query });
    }

    fn record_summary_for_judgement(
        &mut self,
        query_procedure: &AssertionQueryProcedure,
        frame: &ProcedureFrame,
        judgement: QueryJudgement,
    ) -> Result<(), DriverError> {
        if !query_procedure.summary_capable {
            return Ok(());
        }
        let interface = query_procedure.interface.clone();
        match judgement {
            QueryJudgement::No => {
                rules::figure8::CREATE_NOTMAYSUMMARY(
                    frame,
                    self.summaries.tables_mut(),
                    |formula| project_summary_formula(formula, &interface),
                    &self.oracle,
                )?;
            }
            QueryJudgement::Yes => {
                rules::figure9::CREATE_MUSTSUMMARY(
                    frame,
                    self.summaries.tables_mut(),
                    |formula| project_summary_formula(formula, &interface),
                    &self.oracle,
                )?;
            }
            QueryJudgement::Unknown => {}
        }
        Ok(())
    }

    fn summary_counts(&self) -> (usize, usize) {
        let notmay = self
            .order
            .iter()
            .map(|procedure| self.summaries.tables().notmay(procedure).len())
            .sum();
        let must = self
            .order
            .iter()
            .map(|procedure| self.summaries.tables().must(procedure).len())
            .sum();
        (notmay, must)
    }
}

fn rule_assertion_report(
    site: &AdaptedAssertionSite,
    judgement: QueryJudgement,
    stats: RuleSearchStats,
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
) -> Result<RuleAssertionReport, DriverError> {
    let result = match judgement {
        QueryJudgement::No => AssertionResult::True,
        QueryJudgement::Yes => AssertionResult::False,
        QueryJudgement::Unknown => AssertionResult::Unknown,
    };
    let witness = if judgement == QueryJudgement::Yes {
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
        procedure: adapted.name.clone(),
        interface: adapted.interface.clone(),
        summary_capable: false,
        loops: cfg.extract_loops(),
        summary_structure: cfg.summary_structure(),
        cfg,
        node_effects,
        edge_effects,
    })
}

fn build_base_rule_procedure(
    adapted: &AdaptedProcedure,
) -> Result<AssertionQueryProcedure, DriverError> {
    let original_entry = adapted.cfg.entry();
    let mut cfg = Cfg::new("__summary_entry");
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
        .expect("summary entry should connect to the original entry");

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
    for (edge_id, edge) in adapted.cfg.edges() {
        let copied = cfg
            .add_edge(
                node_map[&edge.source],
                node_map[&edge.target],
                edge.relation.clone(),
            )
            .map_err(|error| DriverError::Cfg(error.to_string()))?;
        if let Some(effects) = adapted.edge_effects.get(edge_id) {
            edge_effects.insert(copied, effects.clone());
        }
    }
    for exit in adapted.cfg.concrete_exits() {
        cfg.mark_exit(node_map[exit])
            .map_err(|error| DriverError::Cfg(error.to_string()))?;
    }
    cfg.ensure_single_exit()
        .map_err(|error| DriverError::Cfg(error.to_string()))?;

    let raw = AssertionQueryProcedure {
        procedure: adapted.name.clone(),
        interface: adapted.interface.clone(),
        summary_capable: true,
        loops: cfg.extract_loops(),
        summary_structure: cfg.summary_structure(),
        cfg,
        node_effects,
        edge_effects,
    };
    if raw.summary_structure.has_loops() {
        return Ok(raw);
    }
    rewrite_rule_query_procedure(&raw)
}

/// Rewrites the currently supported acyclic memory/call slice into a
/// path-expanded scalar query so the Figure 5/6/7 scheduler can stay in terms
/// of `Assign` / `Assume` / `Gamma_e`.
fn rewrite_rule_query_procedure(
    query_procedure: &AssertionQueryProcedure,
) -> Result<AssertionQueryProcedure, DriverError> {
    let entry_label = query_procedure
        .cfg
        .node(query_procedure.cfg.entry())
        .ok_or(DriverError::UnknownNode {
            node: query_procedure.cfg.entry(),
        })?
        .label
        .clone();
    let mut cfg = Cfg::new(entry_label);
    let mut node_effects = BTreeMap::<CfgNodeId, Vec<TransferEffect>>::new();
    let mut edge_effects = BTreeMap::<CfgEdgeId, Vec<TransferEffect>>::new();
    let expanded_entry = cfg.entry();

    expand_rule_query_node(
        query_procedure,
        &mut cfg,
        &mut node_effects,
        &mut edge_effects,
        query_procedure.cfg.entry(),
        expanded_entry,
        RuleRewriteState::from_interface(&query_procedure.interface),
    )?;

    cfg.ensure_single_exit()
        .map_err(|error| DriverError::Cfg(error.to_string()))?;

    Ok(AssertionQueryProcedure {
        procedure: query_procedure.procedure.clone(),
        interface: query_procedure.interface.clone(),
        summary_capable: query_procedure.summary_capable,
        loops: cfg.extract_loops(),
        summary_structure: cfg.summary_structure(),
        cfg,
        node_effects,
        edge_effects,
    })
}

fn expand_rule_query_node(
    query_procedure: &AssertionQueryProcedure,
    expanded_cfg: &mut Cfg,
    expanded_node_effects: &mut BTreeMap<CfgNodeId, Vec<TransferEffect>>,
    expanded_edge_effects: &mut BTreeMap<CfgEdgeId, Vec<TransferEffect>>,
    original_node: CfgNodeId,
    expanded_node: CfgNodeId,
    mut rewrite_state: RuleRewriteState,
) -> Result<(), DriverError> {
    let mut lowered = query_procedure
        .node_effects
        .get(&original_node)
        .map(|effects| rewrite_state.lower_effects(effects))
        .transpose()?
        .unwrap_or_default();
    if query_procedure
        .cfg
        .concrete_exits()
        .contains(&original_node)
    {
        lowered.extend(rewrite_state.materialize_visible_memory_effects());
    }
    if !lowered.is_empty() {
        expanded_node_effects.insert(expanded_node, lowered);
    }

    let outgoing = query_procedure
        .cfg
        .outgoing_edges(original_node)
        .map_err(|_| DriverError::UnknownNode {
            node: original_node,
        })?;
    if outgoing.is_empty() {
        if query_procedure
            .cfg
            .concrete_exits()
            .contains(&original_node)
        {
            expanded_cfg
                .mark_exit(expanded_node)
                .map_err(|error| DriverError::Cfg(error.to_string()))?;
        }
        return Ok(());
    }

    for edge_id in outgoing {
        let edge = query_procedure
            .cfg
            .edge(edge_id)
            .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
        let mut edge_state = rewrite_state.clone();
        let lowered_edge_effects = query_procedure
            .edge_effects
            .get(&edge_id)
            .map(|effects| edge_state.lower_effects(effects))
            .transpose()?
            .unwrap_or_default();
        let target_label = query_procedure
            .cfg
            .node(edge.target)
            .ok_or(DriverError::UnknownNode { node: edge.target })?
            .label
            .clone();
        let expanded_target = expanded_cfg.add_node(target_label);
        let expanded_edge = expanded_cfg
            .add_edge(expanded_node, expanded_target, edge.relation.clone())
            .map_err(|error| DriverError::Cfg(error.to_string()))?;
        if !lowered_edge_effects.is_empty() {
            expanded_edge_effects.insert(expanded_edge, lowered_edge_effects);
        }
        expand_rule_query_node(
            query_procedure,
            expanded_cfg,
            expanded_node_effects,
            expanded_edge_effects,
            edge.target,
            expanded_target,
            edge_state,
        )?;
    }

    Ok(())
}

fn ensure_rule_query_supported(
    query_procedure: &AssertionQueryProcedure,
) -> Result<(), DriverError> {
    // APPROX_HEAVY: until loop summaries/invariants exist, the rule-driven
    // slice rejects cyclic CFGs and leaves loop handling to the temporary
    // bounded explorer.
    if query_procedure.summary_structure.has_loops() {
        return Err(DriverError::CyclicRuleProcedure);
    }
    for effects in query_procedure
        .node_effects
        .values()
        .chain(query_procedure.edge_effects.values())
    {
        for effect in effects {
            match effect {
                TransferEffect::Assign { .. }
                | TransferEffect::Assume(_)
                | TransferEffect::Nop
                | TransferEffect::Call { .. } => {}
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct CallSiteEffect {
    callee: String,
    arguments: Vec<CallArgument>,
    return_target: Option<Var>,
    memory_effect: CallMemoryEffect,
}

fn call_edges(query_procedure: &AssertionQueryProcedure) -> Vec<(CfgEdgeId, CallSiteEffect)> {
    let mut edges = Vec::new();
    for edge_id in query_procedure.cfg.edges().keys().copied() {
        if let Some(call) = call_effect_for_edge(query_procedure, edge_id) {
            edges.push((edge_id, call));
        }
    }
    edges
}

fn call_effect_for_edge(
    query_procedure: &AssertionQueryProcedure,
    edge_id: CfgEdgeId,
) -> Option<CallSiteEffect> {
    let edge = query_procedure.cfg.edge(edge_id)?;
    let effects = query_procedure.node_effects.get(&edge.target)?;
    effects.iter().find_map(|effect| match effect {
        TransferEffect::Call {
            callee,
            arguments,
            return_target,
            memory_effect,
        } => Some(CallSiteEffect {
            callee: callee.clone(),
            arguments: arguments.clone(),
            return_target: return_target.clone(),
            memory_effect: *memory_effect,
        }),
        _ => None,
    })
}

fn instantiate_must_summary_at_call(
    call: &CallSiteEffect,
    callee_interface: &ProcedureInterface,
    summary: &MustSummary,
) -> Option<MustSummary> {
    Some(MustSummary {
        precondition: instantiate_formula_at_callsite(
            &summary.precondition,
            call,
            callee_interface,
            false,
        )?,
        postcondition: instantiate_formula_at_callsite(
            &summary.postcondition,
            call,
            callee_interface,
            true,
        )?,
    })
}

fn instantiate_notmay_summary_at_call(
    call: &CallSiteEffect,
    callee_interface: &ProcedureInterface,
    summary: &NotMaySummary,
) -> Option<NotMaySummary> {
    Some(NotMaySummary {
        precondition: instantiate_formula_at_callsite(
            &summary.precondition,
            call,
            callee_interface,
            false,
        )?,
        postcondition: instantiate_formula_at_callsite(
            &summary.postcondition,
            call,
            callee_interface,
            true,
        )?,
    })
}

fn instantiate_formula_at_callsite(
    formula: &Formula,
    call: &CallSiteEffect,
    callee_interface: &ProcedureInterface,
    include_post_state: bool,
) -> Option<Formula> {
    let mut fresh = FreshNameGenerator::new();
    let mut alpha_map = BTreeMap::<String, Var>::new();
    let mut memory_alpha = BTreeMap::<String, String>::new();
    let mut term_subst = BTreeMap::<String, Term>::new();
    let mut bool_subst = BTreeMap::<String, Formula>::new();
    let mut memory_subst = BTreeMap::<String, Memory>::new();

    for (formal_name, argument) in callee_interface.parameters.iter().zip(&call.arguments) {
        let formal = fresh_formal_var(&mut fresh, "call", formal_name, argument)?;
        alpha_map.insert(formal_name.clone(), formal.clone());
        match argument {
            CallArgument::Term(term) => {
                term_subst.insert(formal.name().to_string(), term.clone());
            }
            CallArgument::Predicate(predicate) => {
                bool_subst.insert(formal.name().to_string(), predicate.clone());
            }
            CallArgument::Pointer(pointer) => {
                let fresh_offset =
                    fresh.freshened_var(&ProcedureInterface::offset_var(formal_name), "call");
                alpha_map.insert(
                    ProcedureInterface::offset_var(formal_name)
                        .name()
                        .to_string(),
                    fresh_offset.clone(),
                );
                term_subst.insert(fresh_offset.name().to_string(), pointer.offset().clone());

                let input_name = ProcedureInterface::input_memory_port(formal_name);
                let fresh_input = fresh.freshened_name(&input_name, "call");
                memory_alpha.insert(input_name.clone(), fresh_input.clone());
                memory_subst.insert(fresh_input, pointer.memory_before()?.clone());

                let output_name = ProcedureInterface::output_memory_port(formal_name);
                let fresh_output = fresh.freshened_name(&output_name, "call");
                memory_alpha.insert(output_name.clone(), fresh_output.clone());
                let output_memory = if include_post_state {
                    pointer.memory_after()?.clone()
                } else {
                    pointer.memory_before()?.clone()
                };
                memory_subst.insert(fresh_output, output_memory);
            }
        }
    }

    if include_post_state {
        if let (Some(return_target), Some(return_value)) =
            (&call.return_target, &callee_interface.return_value)
        {
            let fresh_return = fresh.freshened_var(return_value, "call");
            alpha_map.insert(return_value.name().to_string(), fresh_return.clone());
            match return_target.sort() {
                Sort::Bool => {
                    bool_subst.insert(
                        fresh_return.name().to_string(),
                        Formula::Var(return_target.clone()),
                    );
                }
                Sort::Int | Sort::Real => {
                    term_subst.insert(
                        fresh_return.name().to_string(),
                        Term::Var(return_target.clone()),
                    );
                }
            }
        }
    }

    let alpha_renamed = formula
        .alpha_rename(&alpha_map)
        .alpha_rename_memory(&memory_alpha);
    Some(alpha_renamed.substitute_interface(&term_subst, &bool_subst, &memory_subst))
}

fn fresh_formal_var(
    fresh: &mut FreshNameGenerator,
    stem: &str,
    formal_name: &str,
    argument: &CallArgument,
) -> Option<Var> {
    let prototype = match argument {
        CallArgument::Term(term) => Var::new(formal_name.to_string(), term.sort().ok()?),
        CallArgument::Predicate(_) => Var::bool(formal_name.to_string()),
        CallArgument::Pointer(_) => Var::int(formal_name.to_string()),
    };
    Some(fresh.freshened_var(&prototype, stem))
}

fn map_query_to_callee_interface(
    call: &CallSiteEffect,
    callee_procedure: &AssertionQueryProcedure,
    caller_query: &ReachabilityQuery,
) -> Option<ReachabilityQuery> {
    let precondition = project_query_formula_to_callee(
        &caller_query.precondition,
        call,
        &callee_procedure.interface,
        false,
    )?;
    let postcondition = project_query_formula_to_callee(
        &caller_query.postcondition,
        call,
        &callee_procedure.interface,
        true,
    )?;
    Some(ReachabilityQuery::new(
        &call.callee,
        precondition,
        postcondition,
    ))
}

fn project_query_formula_to_callee(
    formula: &Formula,
    call: &CallSiteEffect,
    callee_interface: &ProcedureInterface,
    include_return: bool,
) -> Option<Formula> {
    let visible = caller_visible_names(call, include_return);
    let projected = project_formula_to_visible(formula, &visible);
    let mut term_subst = BTreeMap::<String, Term>::new();
    let mut bool_subst = BTreeMap::<String, Formula>::new();
    let mut memory_subst = BTreeMap::<String, Memory>::new();
    let mut extra_bindings = Vec::<Formula>::new();

    for (formal_name, argument) in callee_interface.parameters.iter().zip(&call.arguments) {
        match argument {
            CallArgument::Term(term) => {
                let formal = Term::var(formal_name.clone(), term.sort().ok()?);
                match term {
                    Term::Var(var) => {
                        term_subst.insert(var.name().to_string(), formal);
                    }
                    _ => extra_bindings.push(Formula::eq(formal, term.clone())),
                }
            }
            CallArgument::Predicate(predicate) => {
                let formal = Formula::bool_var(formal_name.clone());
                match predicate {
                    Formula::Var(var) => {
                        bool_subst.insert(var.name().to_string(), formal);
                    }
                    Formula::True | Formula::False => {
                        extra_bindings.push(Formula::iff(formal, predicate.clone()));
                    }
                    _ => return None,
                }
            }
            CallArgument::Pointer(pointer) => {
                let formal_offset = Term::Var(ProcedureInterface::offset_var(formal_name));
                match pointer.offset() {
                    Term::Var(var) => {
                        term_subst.insert(var.name().to_string(), formal_offset);
                    }
                    other => extra_bindings.push(Formula::eq(formal_offset, other.clone())),
                }

                let formal_input = Memory::var(ProcedureInterface::input_memory_port(formal_name));
                match pointer.memory_before()? {
                    Memory::Var(name) => {
                        memory_subst.insert(name.clone(), formal_input);
                    }
                    other => extra_bindings.push(Formula::memory_eq(formal_input, other.clone())),
                }

                if include_return {
                    let formal_output =
                        Memory::var(ProcedureInterface::output_memory_port(formal_name));
                    match pointer.memory_after()? {
                        Memory::Var(name) => {
                            memory_subst.insert(name.clone(), formal_output);
                        }
                        other => {
                            extra_bindings.push(Formula::memory_eq(formal_output, other.clone()))
                        }
                    }
                }
            }
        }
    }

    if include_return {
        if let (Some(return_target), Some(return_value)) =
            (&call.return_target, &callee_interface.return_value)
        {
            match return_target.sort() {
                Sort::Bool => {
                    bool_subst.insert(
                        return_target.name().to_string(),
                        Formula::Var(return_value.clone()),
                    );
                }
                Sort::Int | Sort::Real => {
                    term_subst.insert(
                        return_target.name().to_string(),
                        Term::Var(return_value.clone()),
                    );
                }
            }
        }
    }

    let transformed = projected.substitute_interface(&term_subst, &bool_subst, &memory_subst);
    let result = Formula::and_all(
        std::iter::once(transformed)
            .chain(extra_bindings)
            .collect::<Vec<_>>(),
    );
    Some(result)
}

fn caller_visible_names(call: &CallSiteEffect, include_return: bool) -> BTreeSet<String> {
    let mut visible = BTreeSet::new();
    for argument in &call.arguments {
        match argument {
            CallArgument::Term(term) => {
                visible.extend(term_variable_names(term));
            }
            CallArgument::Predicate(predicate) => {
                visible.extend(predicate.free_variable_names());
            }
            CallArgument::Pointer(pointer) => {
                visible.extend(term_variable_names(pointer.offset()));
                visible.extend(
                    pointer
                        .memory_before()
                        .map(Memory::free_symbol_names)
                        .unwrap_or_default(),
                );
                if include_return {
                    visible.extend(
                        pointer
                            .memory_after()
                            .map(Memory::free_symbol_names)
                            .unwrap_or_default(),
                    );
                }
            }
        }
    }
    if include_return {
        if let Some(return_target) = &call.return_target {
            visible.insert(return_target.name().to_string());
        }
    }
    visible
}

fn callee_visible_names(interface: &ProcedureInterface) -> BTreeSet<String> {
    let mut visible = interface
        .parameters
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if let Some(return_value) = &interface.return_value {
        visible.insert(return_value.name().to_string());
    }
    for root in &interface.visible_memory_roots {
        visible.insert(ProcedureInterface::input_memory_port(root));
        visible.insert(ProcedureInterface::output_memory_port(root));
        visible.insert(ProcedureInterface::offset_var(root).name().to_string());
    }
    visible
}

fn project_summary_formula(formula: &Formula, interface: &ProcedureInterface) -> Formula {
    project_formula_to_visible(formula, &callee_visible_names(interface))
}

fn project_formula_to_visible(formula: &Formula, visible: &BTreeSet<String>) -> Formula {
    let mut conjuncts = match formula.clone() {
        Formula::And(items) => items,
        other => vec![other],
    };
    loop {
        let mut changed = false;
        for index in 0..conjuncts.len() {
            if let Some((var, term)) = hidden_numeric_assignment(&conjuncts[index], visible) {
                conjuncts.remove(index);
                conjuncts = conjuncts
                    .into_iter()
                    .map(|conjunct| substitute_term_assignment(&conjunct, &var, &term))
                    .collect();
                changed = true;
                break;
            }
            if let Some((var, predicate)) = hidden_boolean_assignment(&conjuncts[index], visible) {
                conjuncts.remove(index);
                conjuncts = conjuncts
                    .into_iter()
                    .map(|conjunct| substitute_bool_assignment(&conjunct, &var, &predicate))
                    .collect();
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
    }
    Formula::and_all(
        conjuncts
            .into_iter()
            .filter(|conjunct| conjunct.mentions_only(visible))
            .collect::<Vec<_>>(),
    )
}

fn hidden_numeric_assignment(formula: &Formula, visible: &BTreeSet<String>) -> Option<(Var, Term)> {
    match formula {
        Formula::Eq(Term::Var(var), term)
            if !visible.contains(var.name()) && !term_variable_names(term).contains(var.name()) =>
        {
            Some((var.clone(), term.clone()))
        }
        Formula::Eq(term, Term::Var(var))
            if !visible.contains(var.name()) && !term_variable_names(term).contains(var.name()) =>
        {
            Some((var.clone(), term.clone()))
        }
        _ => None,
    }
}

fn hidden_boolean_assignment(
    formula: &Formula,
    visible: &BTreeSet<String>,
) -> Option<(Var, Formula)> {
    let Formula::And(items) = formula else {
        return None;
    };
    if items.len() != 2 {
        return None;
    }
    match (&items[0], &items[1]) {
        (Formula::Implies(lhs1, rhs1), Formula::Implies(lhs2, rhs2))
            if rhs1 == lhs2 && lhs1 == rhs2 =>
        {
            if let Formula::Var(var) = lhs1.as_ref() {
                if !visible.contains(var.name()) {
                    return Some((var.clone(), rhs1.as_ref().clone()));
                }
            }
            if let Formula::Var(var) = rhs1.as_ref() {
                if !visible.contains(var.name()) {
                    return Some((var.clone(), lhs1.as_ref().clone()));
                }
            }
            None
        }
        _ => None,
    }
}

fn term_variable_names(term: &Term) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_term_variable_names(term, &mut names);
    names
}

fn collect_term_variable_names(term: &Term, names: &mut BTreeSet<String>) {
    match term {
        Term::Var(var) => {
            names.insert(var.name().to_string());
        }
        Term::Int(_) | Term::Real(_) => {}
        Term::Select(_, index) => collect_term_variable_names(index, names),
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            collect_term_variable_names(lhs, names);
            collect_term_variable_names(rhs, names);
        }
        Term::Neg(inner) => collect_term_variable_names(inner, names),
    }
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

fn apply_must_post_round(
    frame: &mut ProcedureFrame,
    query_procedure: &AssertionQueryProcedure,
    oracle: &Oracle,
    stats: &mut RuleSearchStats,
) -> Result<bool, DriverError> {
    let mut changed = false;
    let edges = frame.cfg().edges().keys().copied().collect::<Vec<_>>();
    for edge_id in edges {
        if call_effect_for_edge(query_procedure, edge_id).is_some() {
            continue;
        }
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
        if call_effect_for_edge(query_procedure, edge_id).is_some() {
            continue;
        }
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
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_memory(lhs, target, replacement),
            substitute_memory(rhs, target, replacement),
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
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(lhs.clone(), rhs.clone()),
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

    fn analyze_named_rules(ir: &str, name: &str) -> RuleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_rule_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        let pure = crate::analysis::llvm_adapter::infer_memory_pure_functions(&graphs);
        analyze_function_graphs_rules_with_purity(&graphs, &pure)
            .unwrap()
            .into_iter()
            .find(|report| report.procedure == name)
            .unwrap()
    }

    fn analyze_first_rules(ir: &str) -> RuleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_rule_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        analyze_function_graph_rules(&graphs[0]).unwrap()
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
    fn rule_driver_supports_alloca_store_load_memory() {
        let report = analyze_first_rules(
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
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::True);
        assert!(report.assertions[0].witness.is_none());
    }

    #[test]
    fn rule_driver_tracks_memory_across_branching_paths() {
        let report = analyze_first_rules(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %cond) {
                entry:
                    %ptr = alloca i32
                    br i1 %cond, label %then, label %else
                then:
                    store i32 1, ptr %ptr
                    br label %merge
                else:
                    store i32 2, ptr %ptr
                    br label %merge
                merge:
                    %expected = phi i32 [1, %then], [2, %else]
                    %value = load i32, ptr %ptr
                    %ok = icmp eq i32 %value, %expected
                    call void @may_assert(i1 %ok)
                    ret void
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
    fn rule_driver_havocs_memory_for_impure_calls() {
        let report = analyze_named_rules(
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
        );

        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        assert!(report.assertions[0].witness.is_some());
    }

    #[test]
    fn rule_driver_uses_summary_driven_integer_returns() {
        let report = analyze_named_rules(
            r#"
                declare void @may_assert(i1)

                define i32 @helper(i32 %x) {
                entry:
                    %y = add i32 %x, 1
                    ret i32 %y
                }

                define void @main(i32 %x) {
                entry:
                    %value = call i32 @helper(i32 %x)
                    %expected = add i32 %x, 1
                    %ok = icmp eq i32 %value, %expected
                    call void @may_assert(i1 %ok)
                    ret void
                }
            "#,
            "main",
        );

        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::True);
    }

    #[test]
    fn rule_driver_can_report_false_callers_from_summary_driven_returns() {
        let report = analyze_named_rules(
            r#"
                declare void @may_assert(i1)

                define i32 @helper(i32 %x) {
                entry:
                    %y = add i32 %x, 1
                    ret i32 %y
                }

                define void @main(i32 %x) {
                entry:
                    %value = call i32 @helper(i32 %x)
                    %ok = icmp eq i32 %value, %x
                    call void @may_assert(i1 %ok)
                    ret void
                }
            "#,
            "main",
        );

        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.assertions.len(), 1);
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        assert!(report.assertions[0].witness.is_some());
    }

    #[test]
    fn rule_driver_attaches_a_witness_by_default() {
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
        assert_eq!(report.assertions[0].result, AssertionResult::False);
        let witness = report.assertions[0]
            .witness
            .as_ref()
            .expect("false rule result should carry a witness by default");
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
    fn rule_driver_false_results_render_with_witnesses_by_default() {
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
        assert!(report.assertions[0].witness.is_some());
    }

    #[test]
    fn safe_rule_results_do_not_attach_witnesses() {
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
        assert!(report.assertions[0].witness.is_none());
    }

    #[test]
    fn rule_report_display_renders_witness_trace() {
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
