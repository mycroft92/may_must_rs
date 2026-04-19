//! SMT-backed analysis coordinator.
//!
//! `smt::solver` is the low-level Z3 wrapper: variables, assertions, solver
//! scopes, satisfiability, and models. This module is intentionally higher
//! level. It owns analysis concerns such as query ordering, summary lookup,
//! worklist traversal, and transfer-function dispatch.

#![allow(dead_code)]

use crate::analysis::domain::SummaryKind;
use crate::analysis::predicates::{Formula, PredicateResult};
use crate::analysis::smt_path::SmtPathState;
use crate::analysis::summary_store::{
    FunctionSummary, SmtQuery, SummaryEvidence, SummaryStore, SummaryTarget,
};
use crate::analysis::transfer::{BranchStates, TransferFunctions, TransferOutcome};
use crate::llvm_utils::llvm_wrap::Instruction;
use crate::llvm_utils::program_graph::FunctionGraph;
use std::collections::{HashMap, VecDeque};

#[derive(Clone, Debug)]
pub struct SmtEngineConfig {
    pub max_steps: usize,
    pub max_visits_per_instruction: usize,
}

impl Default for SmtEngineConfig {
    fn default() -> Self {
        Self {
            max_steps: 20_000,
            max_visits_per_instruction: 64,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtSummaryAnswer<'a> {
    BugFound { summary: &'a FunctionSummary },
    ProvenSafe { summary: &'a FunctionSummary },
}

impl<'a> SmtSummaryAnswer<'a> {
    pub fn kind(&self) -> SummaryKind {
        match self {
            SmtSummaryAnswer::BugFound { .. } => SummaryKind::Must,
            SmtSummaryAnswer::ProvenSafe { .. } => SummaryKind::NotMay,
        }
    }
}

#[derive(Clone, Debug)]
pub enum SmtAnalysisAnswer {
    BugFound { trace: Vec<String> },
    ProvenSafe,
    Unknown { reason: String },
}

#[derive(Clone, Debug)]
pub struct SmtAnalysisReport {
    pub query: SmtQuery,
    pub answer: SmtAnalysisAnswer,
    pub must_summaries: usize,
    pub not_may_summaries: usize,
}

#[derive(Clone, Debug)]
struct SmtExecutionResult {
    bug: Option<SmtBugWitness>,
    complete: bool,
    unknown_reasons: Vec<String>,
}

#[derive(Clone, Debug)]
struct SmtBugWitness {
    trace: Vec<String>,
    relation: Formula,
}

impl SmtExecutionResult {
    fn safe() -> Self {
        Self {
            bug: None,
            complete: true,
            unknown_reasons: Vec::new(),
        }
    }

    fn bug(trace: Vec<String>, relation: Formula) -> Self {
        Self {
            bug: Some(SmtBugWitness { trace, relation }),
            complete: true,
            unknown_reasons: Vec::new(),
        }
    }

    fn unknown(reason: impl Into<String>) -> Self {
        Self {
            bug: None,
            complete: false,
            unknown_reasons: vec![reason.into()],
        }
    }

    fn merge_unknown(&mut self, reason: impl Into<String>) {
        self.complete = false;
        self.unknown_reasons.push(reason.into());
    }
}

#[derive(Clone, Debug, Default)]
pub struct SmtAnalysisEngine {
    config: SmtEngineConfig,
    summaries: SummaryStore,
}

impl SmtAnalysisEngine {
    pub fn new(config: SmtEngineConfig) -> Self {
        Self {
            config,
            summaries: SummaryStore::new(),
        }
    }

    pub fn config(&self) -> &SmtEngineConfig {
        &self.config
    }

    pub fn summaries(&self) -> &SummaryStore {
        &self.summaries
    }

    pub fn summaries_mut(&mut self) -> &mut SummaryStore {
        &mut self.summaries
    }

    /// Analyze every function that directly contains an embedded `may_assert`.
    ///
    /// This is the first SMT-backed top-level entry point. It intentionally
    /// stays intraprocedural until call-summary transfer is wired in: direct
    /// `may_assert` sites are decided with SMT path conditions, while ordinary
    /// calls currently make a path `UNKNOWN`.
    pub fn analyze_embedded_assertions(
        &mut self,
        graphs: &[FunctionGraph],
    ) -> Vec<SmtAnalysisReport> {
        let mut graphs = graphs
            .iter()
            .filter(|graph| !graph.asserts.is_empty())
            .collect::<Vec<_>>();
        graphs.sort_by(|left, right| left.name.cmp(&right.name));

        graphs
            .into_iter()
            .map(|graph| self.analyze_embedded_assertions_in_graph(graph))
            .collect()
    }

    fn analyze_embedded_assertions_in_graph(&mut self, graph: &FunctionGraph) -> SmtAnalysisReport {
        let query = SmtQuery::new(
            graph.name.clone(),
            SummaryTarget::assertion("any_may_assert"),
            Formula::True,
            Formula::True,
        );

        let cached = match self.answer_from_summaries(&query) {
            Ok(answer) => answer,
            Err(err) => {
                return self.report(
                    query,
                    SmtAnalysisAnswer::Unknown {
                        reason: err.to_string(),
                    },
                )
            }
        };

        if let Some(answer) = cached {
            return self.report_from_summary(query, answer);
        }

        let result = self.execute_embedded_assertion_query(graph, &query);
        let answer = if let Some(witness) = result.bug {
            self.record_must(
                graph.name.clone(),
                query.target.clone(),
                query.pre.clone(),
                query.post.clone(),
                witness.relation,
                witness.trace.clone(),
            );
            SmtAnalysisAnswer::BugFound {
                trace: witness.trace,
            }
        } else if result.complete {
            self.record_not_may(
                graph.name.clone(),
                query.target.clone(),
                query.pre.clone(),
                query.post.clone(),
                "all supported SMT paths completed without an assertion violation",
            );
            SmtAnalysisAnswer::ProvenSafe
        } else {
            SmtAnalysisAnswer::Unknown {
                reason: result.unknown_reasons.join("; "),
            }
        };

        self.report(query, answer)
    }

    /// Follow the same high-level SMASH order as the toy analyzer:
    ///
    /// 1. An applicable must summary proves reachability.
    /// 2. An applicable not-may summary proves unreachability.
    /// 3. If neither exists, the worklist/transfer layer must run.
    pub fn answer_from_summaries(
        &self,
        query: &SmtQuery,
    ) -> PredicateResult<Option<SmtSummaryAnswer<'_>>> {
        if let Some(summary) = self.summaries.find_applicable_must(query)? {
            return Ok(Some(SmtSummaryAnswer::BugFound { summary }));
        }

        if let Some(summary) = self.summaries.find_applicable_not_may(query)? {
            return Ok(Some(SmtSummaryAnswer::ProvenSafe { summary }));
        }

        Ok(None)
    }

    pub fn record_must(
        &mut self,
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        relation: Formula,
        trace: Vec<String>,
    ) -> bool {
        self.summaries
            .add_must(function, target, pre, post, relation, trace)
    }

    pub fn record_not_may(
        &mut self,
        function: impl Into<String>,
        target: SummaryTarget,
        pre: Formula,
        post: Formula,
        reason: impl Into<String>,
    ) -> bool {
        self.summaries
            .add_not_may(function, target, pre, post, reason)
    }

    fn execute_embedded_assertion_query(
        &self,
        graph: &FunctionGraph,
        query: &SmtQuery,
    ) -> SmtExecutionResult {
        let Some(start) = graph.start else {
            return SmtExecutionResult::unknown(format!("function {} has no entry", graph.name));
        };

        let mut initial = SmtPathState::with_formal_params(graph.name.clone(), &graph.params);
        initial.assume(query.pre.clone());

        let mut result = SmtExecutionResult::safe();
        let mut steps = 0usize;
        let mut visits: HashMap<Instruction, usize> = HashMap::new();
        let mut worklist = VecDeque::from([(start, initial)]);

        while let Some((instruction, mut state)) = worklist.pop_front() {
            steps += 1;
            if steps > self.config.max_steps {
                result.merge_unknown(format!("step limit reached in {}", graph.name));
                continue;
            }

            let count = visits.entry(instruction).or_insert(0);
            *count += 1;
            if *count > self.config.max_visits_per_instruction {
                result.merge_unknown(format!(
                    "visit limit reached at {}",
                    one_line_instruction(instruction)
                ));
                continue;
            }

            state.push_trace(one_line_instruction(instruction));

            if instruction.get_called_function().as_deref() == Some("may_assert") {
                match self.transfer_may_assert(graph, instruction, state, query, &mut worklist) {
                    Ok(Some(witness)) => {
                        return SmtExecutionResult::bug(witness.trace, witness.relation);
                    }
                    Ok(None) => {}
                    Err(reason) => result.merge_unknown(reason),
                }
                continue;
            }

            match TransferFunctions::transfer(instruction, state) {
                Ok(TransferOutcome::Continue(next_state)) => {
                    enqueue_successors(graph, instruction, next_state, &mut worklist);
                }
                Ok(TransferOutcome::Branch(branches)) => {
                    if let Err(reason) =
                        enqueue_branch_successors(instruction, branches, &mut worklist)
                    {
                        result.merge_unknown(reason);
                    }
                }
                Ok(TransferOutcome::Return(_final_state)) => {}
                Err(err) => result.merge_unknown(err.to_string()),
            }
        }

        result
    }

    fn transfer_may_assert(
        &self,
        graph: &FunctionGraph,
        instruction: Instruction,
        state: SmtPathState,
        query: &SmtQuery,
        worklist: &mut VecDeque<(Instruction, SmtPathState)>,
    ) -> Result<Option<SmtBugWitness>, String> {
        let Some(arg) = instruction.get_call_args().first().copied() else {
            return Err("may_assert has no argument".to_string());
        };

        let assertion_holds = bool_value(arg, &state);
        let violation = assertion_holds.negate();
        let target_condition =
            Formula::and([state.path_condition(), violation, query.post.clone()]);

        let violation_is_reachable = target_condition
            .is_satisfiable_in(state.function())
            .map_err(|err| err.to_string())?;

        if violation_is_reachable {
            return Ok(Some(SmtBugWitness {
                trace: state.trace().to_vec(),
                relation: target_condition,
            }));
        }

        enqueue_successors(graph, instruction, state, worklist);
        Ok(None)
    }

    fn report_from_summary(
        &self,
        query: SmtQuery,
        answer: SmtSummaryAnswer<'_>,
    ) -> SmtAnalysisReport {
        let answer = match answer {
            SmtSummaryAnswer::BugFound { summary } => SmtAnalysisAnswer::BugFound {
                trace: trace_from_evidence(&summary.evidence),
            },
            SmtSummaryAnswer::ProvenSafe { .. } => SmtAnalysisAnswer::ProvenSafe,
        };

        self.report(query, answer)
    }

    fn report(&self, query: SmtQuery, answer: SmtAnalysisAnswer) -> SmtAnalysisReport {
        SmtAnalysisReport {
            query,
            answer,
            must_summaries: self.summaries.must_count(),
            not_may_summaries: self.summaries.not_may_count(),
        }
    }
}

fn enqueue_successors(
    graph: &FunctionGraph,
    instruction: Instruction,
    state: SmtPathState,
    worklist: &mut VecDeque<(Instruction, SmtPathState)>,
) {
    if let Some(node) = graph.edges.get(&instruction) {
        for successor in &node.successors {
            worklist.push_back((*successor, state.clone()));
        }
    }
}

fn enqueue_branch_successors(
    instruction: Instruction,
    branches: BranchStates,
    worklist: &mut VecDeque<(Instruction, SmtPathState)>,
) -> Result<(), String> {
    let successors = instruction.get_successors();

    if let Some(state) = branches.true_state {
        let Some(successor) = successors.first().copied() else {
            return Err(format!(
                "conditional branch has no true successor: {}",
                one_line_instruction(instruction)
            ));
        };
        worklist.push_back((successor, state));
    }

    if let Some(state) = branches.false_state {
        let Some(successor) = successors.get(1).copied() else {
            return Err(format!(
                "conditional branch has no false successor: {}",
                one_line_instruction(instruction)
            ));
        };
        worklist.push_back((successor, state));
    }

    Ok(())
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

fn value_name(value: Instruction) -> Option<String> {
    value
        .get_name()
        .or_else(|| value.get_assignment_var())
        .map(normalize_name)
}

fn normalize_name(name: impl AsRef<str>) -> String {
    let name = name.as_ref();
    if name.starts_with('%') {
        name.to_string()
    } else {
        format!("%{name}")
    }
}

fn trace_from_evidence(evidence: &SummaryEvidence) -> Vec<String> {
    match evidence {
        SummaryEvidence::WitnessTrace(trace) => trace.clone(),
        _ => Vec::new(),
    }
}

fn one_line_instruction(instruction: Instruction) -> String {
    let text = instruction.print().replace('\n', " ");
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::predicates::IntTerm;
    use crate::analysis::state::SummaryPhase;

    #[test]
    fn summary_lookup_checks_must_before_not_may() {
        let mut engine = SmtAnalysisEngine::default();
        let target = SummaryTarget::assertion("a0");

        engine.record_not_may(
            "main",
            target.clone(),
            Formula::True,
            Formula::True,
            "not-may proof",
        );
        engine.record_must(
            "main",
            target.clone(),
            Formula::True,
            Formula::True,
            Formula::True,
            vec!["witness".to_string()],
        );

        let query = SmtQuery::new("main", target, Formula::True, Formula::True);
        let answer = engine.answer_from_summaries(&query).unwrap().unwrap();

        assert_eq!(answer.kind(), SummaryKind::Must);
    }

    #[test]
    fn summary_lookup_returns_none_when_cache_misses() {
        let engine = SmtAnalysisEngine::default();
        let query = SmtQuery::new(
            "missing",
            SummaryTarget::assertion("a0"),
            Formula::True,
            Formula::True,
        );

        assert!(engine.answer_from_summaries(&query).unwrap().is_none());
    }

    #[test]
    fn paper_section2_example1_not_may_summary_answers_g_negative_return_query() {
        let mut engine = SmtAnalysisEngine::default();
        let ret = IntTerm::summary_return(SummaryPhase::Post);
        let negative_return = Formula::lt(ret, IntTerm::int(0));

        engine.record_not_may(
            "g",
            SummaryTarget::Return,
            Formula::True,
            negative_return.clone(),
            "Figure 1: g always returns a non-negative value",
        );

        let query = SmtQuery::new("g", SummaryTarget::Return, Formula::True, negative_return);
        let answer = engine.answer_from_summaries(&query).unwrap().unwrap();

        assert_eq!(answer.kind(), SummaryKind::NotMay);
    }

    #[test]
    fn paper_section2_example2_must_summary_answers_f_positive_return_query() {
        let mut engine = SmtAnalysisEngine::default();
        let input = IntTerm::summary_param(SummaryPhase::Pre, 0);
        let ret = IntTerm::summary_return(SummaryPhase::Post);
        let positive_input = Formula::gt(input, IntTerm::int(0));
        let positive_return = Formula::gt(ret, IntTerm::int(0));

        engine.record_must(
            "f",
            SummaryTarget::Return,
            positive_input,
            positive_return.clone(),
            positive_return.clone(),
            vec!["Figure 2: take f's if branch and avoid h(i)".to_string()],
        );

        let query = SmtQuery::new("f", SummaryTarget::Return, Formula::True, positive_return);
        let answer = engine.answer_from_summaries(&query).unwrap().unwrap();

        assert_eq!(answer.kind(), SummaryKind::Must);
    }
}
