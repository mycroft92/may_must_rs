#![allow(dead_code)]

use crate::common::adapter::ReturnSummary;
use crate::common::formula::{Formula, Sort, Term};
use crate::may_must_analysis::llm_response_parser;
use crate::may_must_analysis::loops::LoopInfo;
use crate::may_must_analysis::providers::{CandidateProvider, LoopContext};
use std::collections::BTreeMap;
use std::process::Command;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CegisAttempt {
    pub candidate: Formula,
    pub failure: String,
}

#[derive(Clone, Debug)]
pub struct FullLoopContext {
    pub base: LoopContext,
    pub assertion_location: String,
    pub header_wp: Formula,
    pub variable_sorts: BTreeMap<String, Sort>,
    pub header_label: String,
    pub latch_label: String,
    pub header_out_edges: Vec<String>,
    pub entry_edges: Vec<String>,
    pub body_node_labels: Vec<String>,
    pub exit_edges: Vec<String>,
    pub back_edge_guard: Formula,
    pub source_location: Option<String>,
    pub exit_postcondition: Formula,
    pub previous_attempts: Vec<CegisAttempt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecursiveContext {
    pub function: String,
    pub formal_parameters: Vec<String>,
    pub current_relation: Formula,
    pub caller_entry_formula: Formula,
}

pub trait LlmBackend: Send + Sync {
    fn propose(&self, prompt: &str) -> Option<String>;
}

#[derive(Default)]
pub struct StubLlmBackend;

impl LlmBackend for StubLlmBackend {
    fn propose(&self, _prompt: &str) -> Option<String> {
        None
    }
}

pub struct LlmCandidateProvider {
    backend: Box<dyn LlmBackend>,
    max_proposals: usize,
    manual_summaries: BTreeMap<String, ReturnSummary>,
}

pub struct SubprocessLlmBackend {
    pub script_path: String,
    pub model: String,
}

impl LlmCandidateProvider {
    pub fn new(backend: Box<dyn LlmBackend>) -> Self {
        Self {
            backend,
            max_proposals: 1,
            manual_summaries: BTreeMap::new(),
        }
    }

    pub fn with_max_proposals(mut self, max_proposals: usize) -> Self {
        self.max_proposals = max_proposals.max(1);
        self
    }

    pub fn with_manual_summary(mut self, summary: ReturnSummary) -> Self {
        self.manual_summaries
            .insert(summary.function.clone(), summary);
        self
    }

    pub fn propose_loop_invariants(
        &self,
        ctx: &FullLoopContext,
        seeds: &BTreeMap<String, Sort>,
    ) -> Vec<Formula> {
        let prompt = build_loop_invariant_prompt(ctx, None);
        let mut candidates = Vec::new();
        for _ in 0..self.max_proposals {
            let Some(raw) = self.backend.propose(&prompt) else {
                continue;
            };
            if let Some(candidate) = parse_candidate(&raw, seeds) {
                candidates.push(candidate);
            }
        }
        candidates
    }

    pub fn propose_recursive_summary(&self, ctx: &RecursiveContext) -> Option<ReturnSummary> {
        let prompt = build_recursive_summary_prompt(ctx);
        let raw = self.backend.propose(&prompt)?;
        let seeds = BTreeMap::from([(format!("{}$__retval", ctx.function), Sort::Int)]);
        let relation = parse_candidate(&raw, &seeds)?;
        Some(ReturnSummary {
            function: ctx.function.clone(),
            formal_parameters: ctx.formal_parameters.clone(),
            retval_name: format!("{}$__retval", ctx.function),
            relation,
            write_effects: Vec::new(),
        })
    }
}

impl CandidateProvider for LlmCandidateProvider {
    fn function_summary(&self, callee: &str) -> Option<ReturnSummary> {
        self.manual_summaries.get(callee).cloned()
    }
}

impl LlmBackend for SubprocessLlmBackend {
    fn propose(&self, prompt: &str) -> Option<String> {
        let output = Command::new("python3")
            .arg(&self.script_path)
            .arg("--model")
            .arg(&self.model)
            .arg(prompt)
            .output()
            .ok()?;
        if !output.status.success() || output.stdout.is_empty() {
            return None;
        }
        Some(String::from_utf8_lossy(&output.stdout).into_owned())
    }
}

pub fn collect_variable_sorts(
    _loop_info: &LoopInfo,
    _cfg: &crate::common::abstract_cfg::AbstractCfg,
) -> BTreeMap<String, Sort> {
    BTreeMap::new()
}

pub fn build_full_loop_context(
    base: LoopContext,
    loop_info: &LoopInfo,
    cfg: &crate::common::abstract_cfg::AbstractCfg,
    assertion_location: String,
    exit_postcondition: Formula,
    previous_attempts: Vec<CegisAttempt>,
) -> FullLoopContext {
    FullLoopContext {
        base,
        assertion_location,
        header_wp: Formula::True,
        variable_sorts: collect_variable_sorts(loop_info, cfg),
        header_label: cfg
            .node(loop_info.header)
            .map(|node| clean_node_label(&node.label))
            .unwrap_or_default(),
        latch_label: cfg
            .node(loop_info.latch)
            .map(|node| clean_node_label(&node.label))
            .unwrap_or_default(),
        header_out_edges: Vec::new(),
        entry_edges: Vec::new(),
        body_node_labels: Vec::new(),
        exit_edges: Vec::new(),
        back_edge_guard: loop_info.back_edge_guard.clone(),
        source_location: loop_info.source_location.as_ref().map(ToString::to_string),
        exit_postcondition,
        previous_attempts,
    }
}

pub fn build_loop_invariant_prompt(ctx: &FullLoopContext, template_opt: Option<&str>) -> String {
    if let Some(template) = template_opt {
        return render_template(template, ctx);
    }
    format!(
        "Propose a loop invariant for {} at {}. Back edge guard: {}. Exit postcondition: {}.",
        ctx.base.function, ctx.assertion_location, ctx.back_edge_guard, ctx.exit_postcondition
    )
}

pub fn render_template(template: &str, ctx: &FullLoopContext) -> String {
    template
        .replace("{{function}}", &ctx.base.function)
        .replace("{{assertion_location}}", &ctx.assertion_location)
        .replace("{{back_edge_guard}}", &ctx.back_edge_guard.to_string())
        .replace(
            "{{exit_postcondition}}",
            &ctx.exit_postcondition.to_string(),
        )
}

pub fn build_recursive_summary_prompt(ctx: &RecursiveContext) -> String {
    format!(
        "Propose <POSTCONDITION> for recursive function {} with relation {}.",
        ctx.function, ctx.current_relation
    )
}

pub fn parse_candidate(raw: &str, variable_sorts: &BTreeMap<String, Sort>) -> Option<Formula> {
    let candidate = tagged(raw, "INVARIANT")
        .or_else(|| tagged(raw, "POSTCONDITION"))
        .unwrap_or(raw)
        .trim()
        .trim_matches('`')
        .trim_start_matches("Invariant:")
        .trim_start_matches("Postcondition:")
        .trim();
    let parsed = llm_response_parser::parse_invariant(candidate, variable_sorts).ok()?;
    (parsed != Formula::True).then_some(parsed)
}

pub fn collect_formula_var_sorts(formula: &Formula) -> BTreeMap<String, Sort> {
    let mut vars = BTreeMap::new();
    collect_formula_var_sorts_rec(formula, &mut vars);
    vars
}

pub fn stub_backend() -> Box<dyn LlmBackend> {
    Box::new(StubLlmBackend)
}

pub fn clean_node_label(label: &str) -> String {
    label.lines().next().unwrap_or(label).trim().to_string()
}

pub fn classify_var_name(name: &str) -> &'static str {
    if name.starts_with('%') {
        "ssa register"
    } else if name.contains("$stack") || name.contains("$__ext_") {
        "stack region"
    } else if name.contains('$') {
        "named local / parameter"
    } else {
        "global / unknown scope"
    }
}

pub fn format_guard_disjunction(guards: &[Formula]) -> String {
    if guards.is_empty() {
        "false".to_string()
    } else {
        Formula::or_all(guards.iter().cloned()).to_string()
    }
}

fn tagged<'a>(raw: &'a str, tag: &str) -> Option<&'a str> {
    let open = format!("<{tag}>");
    let close = format!("</{tag}>");
    let start = raw.find(&open)? + open.len();
    let end = raw[start..].find(&close)? + start;
    Some(&raw[start..end])
}

fn collect_formula_var_sorts_rec(formula: &Formula, vars: &mut BTreeMap<String, Sort>) {
    match formula {
        Formula::True | Formula::False => {}
        Formula::Var(var) => {
            vars.insert(var.name().to_string(), var.sort());
        }
        Formula::Not(inner) => collect_formula_var_sorts_rec(inner, vars),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_formula_var_sorts_rec(item, vars);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_formula_var_sorts_rec(lhs, vars);
            collect_formula_var_sorts_rec(rhs, vars);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_term_var_sorts(lhs, vars);
            collect_term_var_sorts(rhs, vars);
        }
        Formula::MemoryEq(_, _) => {}
    }
}

fn collect_term_var_sorts(term: &Term, vars: &mut BTreeMap<String, Sort>) {
    match term {
        Term::Var(var) => {
            vars.insert(var.name().to_string(), var.sort());
        }
        Term::Int(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_formula_var_sorts_rec(inner, vars),
        Term::Select(_, index) => collect_term_var_sorts(index, vars),
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            collect_term_var_sorts(lhs, vars);
            collect_term_var_sorts(rhs, vars);
        }
        Term::Neg(inner) => collect_term_var_sorts(inner, vars),
    }
}
