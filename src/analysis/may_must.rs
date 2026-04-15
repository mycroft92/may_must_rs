//! SMASH-style analysis driver for LLVM IR.
//!
//! Paper mapping:
//!
//! - Section 2 introduces reachability queries and procedure summaries.
//! - Sections 3 and 4 define may/must reasoning rules. This file implements a
//!   bounded symbolic executor as the current intraprocedural engine for those
//!   rules.
//! - Section 4.3 defines the SMASH alternation point at calls. `transfer_call`
//!   is where this prototype issues demand-driven callee queries and consumes
//!   callee summaries.
//! - Section 5.1 describes a deterministic implementation order: use an
//!   applicable must summary, then an applicable not-may summary, otherwise
//!   analyze the procedure and create one of those summaries. `analyze_query`
//!   follows that order.
//!
//! Important limitation: the paper's implementation uses Z3 over linear
//! arithmetic and uninterpreted functions. This prototype does not yet call the
//! SMT wrapper during SMASH decisions; it uses concrete folding plus syntactic
//! predicate checks and returns `Unknown` when that is insufficient.

use crate::analysis::domain::{Predicate, Query, Summary, SummaryKind};
use crate::expressions::exp::{Assertion, Expr, Op};
use crate::llvm_utils::llvm_wrap::{Instruction, InstructionOpcode};
use crate::llvm_utils::program_graph::FunctionGraph;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug)]
pub struct SmashConfig {
    pub max_steps: usize,
    pub max_visits_per_instruction: usize,
}

impl Default for SmashConfig {
    fn default() -> Self {
        Self {
            max_steps: 20_000,
            max_visits_per_instruction: 64,
        }
    }
}

#[derive(Clone, Debug)]
pub enum AnalysisAnswer {
    BugFound { trace: Vec<String> },
    ProvenSafe,
    Unknown { reason: String },
}

#[derive(Clone, Debug)]
pub struct AnalysisReport {
    pub query: Query,
    pub answer: AnalysisAnswer,
    pub must_summaries: usize,
    pub not_may_summaries: usize,
}

#[derive(Clone, Debug)]
enum CheckSpec {
    EmbeddedAssertions,
    UserAssertion(Assertion),
}

impl CheckSpec {
    fn post_predicate(&self) -> Predicate {
        match self {
            CheckSpec::EmbeddedAssertions => Predicate::atom("violate:any_may_assert"),
            CheckSpec::UserAssertion(assertion) => {
                Predicate::atom(format!("violate:{}", expr_to_string(&assertion.stmt.exp)))
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
struct FunctionSummaries {
    must: Vec<Summary>,
    not_may: Vec<Summary>,
}

#[derive(Clone, Debug, Default)]
struct SymbolicState {
    vars: HashMap<String, String>,
    memory: HashMap<String, String>,
    path_conditions: Vec<String>,
    trace: Vec<String>,
    steps: usize,
    visits: HashMap<Instruction, usize>,
}

#[derive(Clone, Debug)]
struct ExecutionResult {
    bug_trace: Option<Vec<String>>,
    complete: bool,
    unknown_reasons: Vec<String>,
}

impl ExecutionResult {
    fn bug(trace: Vec<String>) -> Self {
        Self {
            bug_trace: Some(trace),
            complete: true,
            unknown_reasons: Vec::new(),
        }
    }

    fn safe() -> Self {
        Self {
            bug_trace: None,
            complete: true,
            unknown_reasons: Vec::new(),
        }
    }

    fn unknown(reason: impl Into<String>) -> Self {
        Self {
            bug_trace: None,
            complete: false,
            unknown_reasons: vec![reason.into()],
        }
    }

    fn merge(&mut self, other: ExecutionResult) {
        if self.bug_trace.is_none() {
            self.bug_trace = other.bug_trace;
        }
        self.complete &= other.complete;
        self.unknown_reasons.extend(other.unknown_reasons);
    }
}

pub struct SmashAnalyzer {
    graphs: HashMap<String, FunctionGraph>,
    summaries: HashMap<String, FunctionSummaries>,
    config: SmashConfig,
    active_queries: Vec<String>,
}

impl SmashAnalyzer {
    pub fn new(graphs: Vec<FunctionGraph>, config: SmashConfig) -> Self {
        let graphs = graphs
            .into_iter()
            .map(|graph| (graph.name.clone(), graph))
            .collect();
        Self {
            graphs,
            summaries: HashMap::new(),
            config,
            active_queries: Vec::new(),
        }
    }

    pub fn analyze_embedded_assertions(&mut self) -> Vec<AnalysisReport> {
        let mut functions = self
            .graphs
            .values()
            .filter(|graph| self.function_or_callees_contain_assertion(&graph.name))
            .map(|graph| graph.name.clone())
            .collect::<Vec<_>>();
        functions.sort();

        functions
            .into_iter()
            .map(|function| self.analyze_query(&function, CheckSpec::EmbeddedAssertions))
            .collect()
    }

    pub fn analyze_assertion(&mut self, assertion: Assertion) -> AnalysisReport {
        self.analyze_query(
            &assertion.stmt.func.clone(),
            CheckSpec::UserAssertion(assertion),
        )
    }

    pub fn all_summaries(&self) -> Vec<&Summary> {
        self.summaries
            .values()
            .flat_map(|summaries| summaries.must.iter().chain(summaries.not_may.iter()))
            .collect()
    }

    fn analyze_query(&mut self, function: &str, spec: CheckSpec) -> AnalysisReport {
        let query = Query::new(function, Predicate::True, spec.post_predicate());

        // Section 5.1 deterministic SMASH order, step 1:
        // an applicable must summary is a witness for reachability.
        if let Some(summary) = self.find_applicable_must_summary(&query) {
            return self.report_from_summary(query, summary);
        }

        // Section 5.1 deterministic SMASH order, step 2:
        // an applicable not-may summary proves this query cannot reach `post`.
        if let Some(summary) = self.find_applicable_not_may_summary(&query) {
            return self.report_from_summary(query, summary);
        }

        if self.active_queries.iter().any(|active| active == function) {
            return AnalysisReport {
                query,
                answer: AnalysisAnswer::Unknown {
                    reason: format!("recursive query for {function} is already active"),
                },
                must_summaries: self.must_summary_count(),
                not_may_summaries: self.not_may_summary_count(),
            };
        }

        self.active_queries.push(function.to_string());
        let result = match self.graphs.get(function).cloned() {
            Some(graph) => self.execute_function(&graph, &spec),
            None => ExecutionResult::unknown(format!("no definition for function {function}")),
        };
        self.active_queries.pop();

        let answer = if let Some(trace) = result.bug_trace {
            // CREATE-MUSTSUMMARY: the trace is the witness execution.
            self.add_summary(Summary::must(
                function,
                Predicate::True,
                spec.post_predicate(),
                trace.clone(),
            ));
            AnalysisAnswer::BugFound { trace }
        } else if result.complete {
            // CREATE-MAYSUMMARY in the paper stores a not-may summary: all
            // supported paths were explored without reaching the violation.
            self.add_summary(Summary::not_may(
                function,
                Predicate::True,
                spec.post_predicate(),
            ));
            AnalysisAnswer::ProvenSafe
        } else {
            AnalysisAnswer::Unknown {
                reason: result.unknown_reasons.join("; "),
            }
        };

        AnalysisReport {
            query,
            answer,
            must_summaries: self.must_summary_count(),
            not_may_summaries: self.not_may_summary_count(),
        }
    }

    fn report_from_summary(&self, query: Query, summary: &Summary) -> AnalysisReport {
        let answer = match summary.kind {
            SummaryKind::Must => AnalysisAnswer::BugFound {
                trace: summary.trace.clone(),
            },
            SummaryKind::NotMay => AnalysisAnswer::ProvenSafe,
        };
        AnalysisReport {
            query,
            answer,
            must_summaries: self.must_summary_count(),
            not_may_summaries: self.not_may_summary_count(),
        }
    }

    fn execute_function(&mut self, graph: &FunctionGraph, spec: &CheckSpec) -> ExecutionResult {
        let Some(start) = graph.start else {
            return ExecutionResult::unknown(format!("function {} has no entry", graph.name));
        };

        let mut initial = SymbolicState::default();
        for param in &graph.params {
            initial.vars.insert(param.clone(), param.clone());
        }

        let mut result = ExecutionResult::safe();
        let mut worklist = VecDeque::from([(start, initial)]);

        while let Some((instruction, mut state)) = worklist.pop_front() {
            state.steps += 1;
            if state.steps > self.config.max_steps {
                result.merge(ExecutionResult::unknown(format!(
                    "step limit reached in {}",
                    graph.name
                )));
                continue;
            }

            let visits = state.visits.entry(instruction).or_insert(0);
            *visits += 1;
            if *visits > self.config.max_visits_per_instruction {
                result.merge(ExecutionResult::unknown(format!(
                    "visit limit reached at {}",
                    one_line_instruction(instruction)
                )));
                continue;
            }

            state.trace.push(one_line_instruction(instruction));

            match self.transfer(graph, instruction, state) {
                StepResult::Bug(trace) => return ExecutionResult::bug(trace),
                StepResult::Return(final_state) => {
                    if let CheckSpec::UserAssertion(assertion) = spec {
                        match eval_user_expr(&assertion.stmt.exp, &final_state) {
                            Some(true) => {}
                            Some(false) => return ExecutionResult::bug(final_state.trace),
                            None => result.merge(ExecutionResult::unknown(format!(
                                "could not decide assertion {} at return from {}",
                                expr_to_string(&assertion.stmt.exp),
                                graph.name
                            ))),
                        }
                    }
                }
                StepResult::Continue(next) => {
                    for item in next {
                        worklist.push_back(item);
                    }
                }
                StepResult::Unknown(reason) => result.merge(ExecutionResult::unknown(reason)),
            }
        }

        result
    }

    fn transfer(
        &mut self,
        graph: &FunctionGraph,
        instruction: Instruction,
        mut state: SymbolicState,
    ) -> StepResult {
        match instruction.get_opcode() {
            InstructionOpcode::Alloca => {
                if let Some(target) = assigned_name(instruction) {
                    state.vars.insert(target.clone(), target);
                }
            }
            InstructionOpcode::Store => {
                let operands = instruction.get_operands();
                if let (Some(value), Some(ptr)) = (operands.get(0), operands.get(1)) {
                    let value = eval_llvm_value(*value, &state);
                    let ptr = eval_llvm_value(*ptr, &state);
                    state.memory.insert(ptr, value);
                }
            }
            InstructionOpcode::Load => {
                if let Some(target) = assigned_name(instruction) {
                    if let Some(ptr) = instruction.get_operand(0) {
                        let ptr = eval_llvm_value(ptr, &state);
                        let value = state
                            .memory
                            .get(&ptr)
                            .cloned()
                            .unwrap_or_else(|| format!("load({ptr})"));
                        state.vars.insert(target, value);
                    }
                }
            }
            InstructionOpcode::Add
            | InstructionOpcode::Sub
            | InstructionOpcode::Mul
            | InstructionOpcode::SDiv
            | InstructionOpcode::UDiv
            | InstructionOpcode::SRem
            | InstructionOpcode::URem
            | InstructionOpcode::And
            | InstructionOpcode::Or
            | InstructionOpcode::Xor
            | InstructionOpcode::Shl
            | InstructionOpcode::AShr
            | InstructionOpcode::LShr => self.transfer_binary(instruction, &mut state),
            InstructionOpcode::ICmp => self.transfer_icmp(instruction, &mut state),
            InstructionOpcode::Call => {
                if let Some(result) = self.transfer_call(graph, instruction, &mut state) {
                    return result;
                }
            }
            InstructionOpcode::Ret => {
                if let Some(value) = instruction.get_operand(0) {
                    let value = eval_llvm_value(value, &state);
                    state.vars.insert("return".to_string(), value);
                }
                return StepResult::Return(state);
            }
            InstructionOpcode::PHI => {
                if let Some(target) = assigned_name(instruction) {
                    state.vars.insert(target.clone(), format!("phi({target})"));
                }
            }
            _ => {}
        }

        StepResult::Continue(self.successor_states(graph, instruction, state))
    }

    fn transfer_binary(&self, instruction: Instruction, state: &mut SymbolicState) {
        let Some(target) = assigned_name(instruction) else {
            return;
        };
        let Some(left) = instruction.get_operand(0) else {
            return;
        };
        let Some(right) = instruction.get_operand(1) else {
            return;
        };

        let left = eval_llvm_value(left, state);
        let right = eval_llvm_value(right, state);
        let op = match instruction.get_opcode() {
            InstructionOpcode::Add => "+",
            InstructionOpcode::Sub => "-",
            InstructionOpcode::Mul => "*",
            InstructionOpcode::SDiv | InstructionOpcode::UDiv => "/",
            InstructionOpcode::SRem | InstructionOpcode::URem => "%",
            InstructionOpcode::And => "&",
            InstructionOpcode::Or => "|",
            InstructionOpcode::Xor => "^",
            InstructionOpcode::Shl => "<<",
            InstructionOpcode::AShr | InstructionOpcode::LShr => ">>",
            _ => "?",
        };
        state.vars.insert(target, eval_binary(op, &left, &right));
    }

    fn transfer_icmp(&self, instruction: Instruction, state: &mut SymbolicState) {
        let Some(target) = assigned_name(instruction) else {
            return;
        };
        let Some(left) = instruction.get_operand(0) else {
            return;
        };
        let Some(right) = instruction.get_operand(1) else {
            return;
        };

        let left = eval_llvm_value(left, state);
        let right = eval_llvm_value(right, state);
        let predicate = instruction.get_icmp_predicate().unwrap_or("?");
        state
            .vars
            .insert(target, eval_comparison(predicate, &left, &right));
    }

    fn transfer_call(
        &mut self,
        graph: &FunctionGraph,
        instruction: Instruction,
        state: &mut SymbolicState,
    ) -> Option<StepResult> {
        let callee = instruction.get_called_function()?;

        // Embedded assertions are the current assertion-failure target. A
        // definitely false argument creates a must summary; a definitely true
        // argument lets this path continue.
        if callee == "may_assert" {
            let Some(arg) = instruction.get_call_args().first().copied() else {
                return Some(StepResult::Unknown(
                    "may_assert has no argument".to_string(),
                ));
            };
            let assertion_value = eval_llvm_value(arg, state);
            match bool_value(&assertion_value) {
                Some(true) => return None,
                Some(false) => return Some(StepResult::Bug(state.trace.clone())),
                None => {
                    return Some(StepResult::Unknown(format!(
                        "could not decide may_assert argument {assertion_value} in {}",
                        graph.name
                    )));
                }
            }
        }

        // Section 4.3 MAYMUST-CALL: calls are the alternation point. This
        // demand-driven query may produce either a callee must summary or a
        // callee not-may summary, and the caller uses that result immediately.
        if self.function_or_callees_contain_assertion(&callee) {
            let report = self.analyze_query(&callee, CheckSpec::EmbeddedAssertions);
            if let AnalysisAnswer::BugFound { trace } = report.answer {
                let mut full_trace = state.trace.clone();
                full_trace.push(format!("call {callee} reaches assertion violation"));
                full_trace.extend(trace);
                return Some(StepResult::Bug(full_trace));
            }
        }

        if let Some(target) = assigned_name(instruction) {
            let args = instruction
                .get_call_args()
                .into_iter()
                .map(|arg| eval_llvm_value(arg, state))
                .collect::<Vec<_>>()
                .join(", ");
            state.vars.insert(target, format!("{callee}({args})"));
        }

        None
    }

    fn successor_states(
        &self,
        graph: &FunctionGraph,
        instruction: Instruction,
        state: SymbolicState,
    ) -> Vec<(Instruction, SymbolicState)> {
        if instruction.is_branch_instruction() {
            let successors = instruction.get_successors();
            // LLVMGetCondition is only valid for conditional branches. Calling
            // it on an unconditional branch exits abnormally through LLVM.
            if successors.len() < 2 {
                return successors
                    .into_iter()
                    .map(|successor| (successor, state.clone()))
                    .collect();
            }

            let Some(condition) = instruction.get_branch_condition() else {
                return successors
                    .into_iter()
                    .map(|successor| (successor, state.clone()))
                    .collect();
            };

            let condition = eval_llvm_value(condition, &state);
            return match bool_value(&condition) {
                Some(true) => successors
                    .first()
                    .copied()
                    .map(|successor| vec![(successor, state)])
                    .unwrap_or_default(),
                Some(false) => successors
                    .get(1)
                    .copied()
                    .map(|successor| vec![(successor, state)])
                    .unwrap_or_default(),
                None => {
                    let mut next = Vec::new();
                    if let Some(true_successor) = successors.first().copied() {
                        if let Some(true_state) = with_condition(state.clone(), condition.clone()) {
                            next.push((true_successor, true_state));
                        }
                    }
                    if let Some(false_successor) = successors.get(1).copied() {
                        if let Some(false_state) = with_condition(state, format!("!({condition})"))
                        {
                            next.push((false_successor, false_state));
                        }
                    }
                    next
                }
            };
        }

        graph
            .edges
            .get(&instruction)
            .map(|node| {
                node.successors
                    .iter()
                    .copied()
                    .map(|successor| (successor, state.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }

    fn find_applicable_must_summary(&self, query: &Query) -> Option<&Summary> {
        self.summaries
            .get(&query.function)?
            .must
            .iter()
            .find(|summary| summary.pre.entails(&query.pre) && summary.post.intersects(&query.post))
    }

    fn find_applicable_not_may_summary(&self, query: &Query) -> Option<&Summary> {
        self.summaries
            .get(&query.function)?
            .not_may
            .iter()
            .find(|summary| query.pre.entails(&summary.pre) && query.post.entails(&summary.post))
    }

    fn add_summary(&mut self, summary: Summary) {
        let summaries = self.summaries.entry(summary.function.clone()).or_default();
        let target = match summary.kind {
            SummaryKind::Must => &mut summaries.must,
            SummaryKind::NotMay => &mut summaries.not_may,
        };
        if !target.iter().any(|existing| {
            existing.kind == summary.kind
                && existing.pre == summary.pre
                && existing.post == summary.post
        }) {
            target.push(summary);
        }
    }

    fn must_summary_count(&self) -> usize {
        self.summaries
            .values()
            .map(|summaries| summaries.must.len())
            .sum()
    }

    fn not_may_summary_count(&self) -> usize {
        self.summaries
            .values()
            .map(|summaries| summaries.not_may.len())
            .sum()
    }

    fn function_or_callees_contain_assertion(&self, function: &str) -> bool {
        self.function_or_callees_contain_assertion_inner(function, &mut HashSet::new())
    }

    fn function_or_callees_contain_assertion_inner(
        &self,
        function: &str,
        visited: &mut HashSet<String>,
    ) -> bool {
        if !visited.insert(function.to_string()) {
            return false;
        }
        let Some(graph) = self.graphs.get(function) else {
            return false;
        };
        if !graph.asserts.is_empty() {
            return true;
        }
        graph.vertices.iter().any(|instruction| {
            instruction
                .get_called_function()
                .map(|callee| self.function_or_callees_contain_assertion_inner(&callee, visited))
                .unwrap_or(false)
        })
    }
}

#[derive(Clone, Debug)]
enum StepResult {
    Continue(Vec<(Instruction, SymbolicState)>),
    Return(SymbolicState),
    Bug(Vec<String>),
    Unknown(String),
}

fn assigned_name(instruction: Instruction) -> Option<String> {
    instruction
        .get_assignment_var()
        .map(|name| normalize_name(&name))
}

fn normalize_name(name: &str) -> String {
    if name.starts_with('%') {
        name.to_string()
    } else {
        format!("%{name}")
    }
}

fn eval_llvm_value(value: Instruction, state: &SymbolicState) -> String {
    if let Some(value) = value.as_constant_int() {
        return value.to_string();
    }

    if let Some(name) = value.get_name() {
        let normalized = normalize_name(&name);
        return state.vars.get(&normalized).cloned().unwrap_or(normalized);
    }

    if let Some(name) = value.get_assignment_var() {
        let normalized = normalize_name(&name);
        return state.vars.get(&normalized).cloned().unwrap_or(normalized);
    }

    one_line_instruction(value)
}

fn eval_binary(op: &str, left: &str, right: &str) -> String {
    if let (Some(left), Some(right)) = (int_value(left), int_value(right)) {
        return match op {
            "+" => (left + right).to_string(),
            "-" => (left - right).to_string(),
            "*" => (left * right).to_string(),
            "/" if right != 0 => (left / right).to_string(),
            "%" if right != 0 => (left % right).to_string(),
            "&" => (left & right).to_string(),
            "|" => (left | right).to_string(),
            "^" => (left ^ right).to_string(),
            "<<" => (left << right).to_string(),
            ">>" => (left >> right).to_string(),
            _ => format!("({left} {op} {right})"),
        };
    }

    if let (Some(left), Some(right)) = (bool_value(left), bool_value(right)) {
        return match op {
            "&" => bool_literal(left && right),
            "|" => bool_literal(left || right),
            "^" => bool_literal(left ^ right),
            _ => format!("({left} {op} {right})"),
        };
    }

    format!("({left} {op} {right})")
}

fn eval_comparison(op: &str, left: &str, right: &str) -> String {
    if let (Some(left), Some(right)) = (int_value(left), int_value(right)) {
        return bool_literal(match op {
            "==" => left == right,
            "!=" => left != right,
            ">" => left > right,
            ">=" => left >= right,
            "<" => left < right,
            "<=" => left <= right,
            _ => return format!("({left} {op} {right})"),
        });
    }

    if matches!(op, "==" | "!=") && left == right {
        return bool_literal(op == "==");
    }

    format!("({left} {op} {right})")
}

fn eval_user_expr(expr: &Expr, state: &SymbolicState) -> Option<bool> {
    bool_value(&eval_user_value(expr, state))
}

fn eval_user_value(expr: &Expr, state: &SymbolicState) -> String {
    match expr {
        Expr::Ident(name) => {
            let normalized = normalize_name(name);
            state
                .vars
                .get(&normalized)
                .or_else(|| state.memory.get(&normalized))
                .cloned()
                .unwrap_or(normalized)
        }
        Expr::Const(value) => value.clone(),
        Expr::Unop(inner) => match bool_value(&eval_user_value(inner, state)) {
            Some(value) => bool_literal(!value),
            None => format!("!({})", eval_user_value(inner, state)),
        },
        Expr::Binop(left, op, right) => {
            let left = eval_user_value(left, state);
            let right = eval_user_value(right, state);
            match op {
                Op::Plus => eval_binary("+", &left, &right),
                Op::Minus => eval_binary("-", &left, &right),
                Op::Div => eval_binary("/", &left, &right),
                Op::Mult => eval_binary("*", &left, &right),
                Op::LAnd => eval_binary("&", &left, &right),
                Op::LOr => eval_binary("|", &left, &right),
                Op::Gt => eval_comparison(">", &left, &right),
                Op::Ge => eval_comparison(">=", &left, &right),
                Op::Lt => eval_comparison("<", &left, &right),
                Op::Le => eval_comparison("<=", &left, &right),
                Op::Eeq => eval_comparison("==", &left, &right),
                Op::LNot | Op::Arrow | Op::Named => format!("({left} {op} {right})"),
            }
        }
    }
}

fn with_condition(mut state: SymbolicState, condition: String) -> Option<SymbolicState> {
    match bool_value(&condition) {
        Some(true) => return Some(state),
        Some(false) => return None,
        None => {}
    }

    let negated = if condition.starts_with("!(") && condition.ends_with(')') {
        condition
            .trim_start_matches("!(")
            .trim_end_matches(')')
            .to_string()
    } else {
        format!("!({condition})")
    };

    if state.path_conditions.iter().any(|known| known == &negated) {
        return None;
    }
    if !state
        .path_conditions
        .iter()
        .any(|known| known == &condition)
    {
        state.path_conditions.push(condition);
    }
    Some(state)
}

fn bool_value(value: &str) -> Option<bool> {
    match value.trim() {
        "true" | "1" => Some(true),
        "false" | "0" => Some(false),
        _ => None,
    }
}

fn bool_literal(value: bool) -> String {
    if value {
        "true".to_string()
    } else {
        "false".to_string()
    }
}

fn int_value(value: &str) -> Option<i64> {
    value.trim().parse::<i64>().ok()
}

fn expr_to_string(expr: &Expr) -> String {
    match expr {
        Expr::Ident(name) => name.clone(),
        Expr::Const(value) => value.clone(),
        Expr::Unop(inner) => format!("!({})", expr_to_string(inner)),
        Expr::Binop(left, op, right) => {
            format!("{} {} {}", expr_to_string(left), op, expr_to_string(right))
        }
    }
}

fn one_line_instruction(instruction: Instruction) -> String {
    let text = instruction.print().replace('\n', " ");
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    const LIMIT: usize = 180;
    if text.len() > LIMIT {
        format!("{}...", &text[..LIMIT])
    } else {
        text
    }
}
