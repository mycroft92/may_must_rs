#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgEdgeId, CfgNodeId, TransferEffect};
use crate::common::adapter::AssertionSite;
use crate::common::formula::Formula;
use crate::common::oracle::{Oracle, OracleError};
use crate::may_must_analysis::llm_provider::{
    build_full_loop_context, build_loop_invariant_prompt, parse_candidate, CegisAttempt, LlmBackend,
};
use crate::may_must_analysis::loops::{
    algorithmic_candidates, chc_loop_invariant, check_loop_invariant_verbose,
    collect_loop_body_int_constants, detect_loops, houdini_candidates, sort_innermost_first,
    InvariantCheckResult,
};
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::providers::LoopContext;
use crate::may_must_analysis::rules::{Judgement, RuleEngine, RuleError};
use crate::may_must_analysis::summaries::SummaryTables;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct AssertionResult {
    pub site_id: usize,
    pub site_label: String,
    pub judgement: Judgement,
    pub entry_summary: NodeSummary,
    pub assertion_summary: NodeSummary,
}

#[derive(Debug, thiserror::Error)]
pub enum BackwardError {
    #[error("CFG has a cycle and no loop invariant was accepted")]
    CyclicCfgUnsupported,
    #[error(transparent)]
    Rule(#[from] RuleError),
    #[error(transparent)]
    Oracle(#[from] OracleError),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum InvariantMethod {
    Chc,
    Houdini,
    Template,
}

pub struct InvariantConfig {
    pub methods: Vec<InvariantMethod>,
    pub llm: Option<LlmInvariantConfig>,
    pub skip_algorithmic: bool,
}

impl Default for InvariantConfig {
    fn default() -> Self {
        Self {
            methods: Vec::new(),
            llm: None,
            skip_algorithmic: false,
        }
    }
}

pub struct LlmInvariantConfig {
    pub backend: Box<dyn LlmBackend>,
    pub max_tries: usize,
    pub force: bool,
    pub prompt_template: Option<String>,
}

pub fn analyze(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
) -> Result<AssertionResult, BackwardError> {
    analyze_with_tables(cfg, "", site, oracle, &SummaryTables::new(), None, None)
}

pub fn analyze_with_tables(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    tables: &SummaryTables,
    config: Option<&InvariantConfig>,
    precomputed: Option<&[(CfgNodeId, Formula)]>,
) -> Result<AssertionResult, BackwardError> {
    if cfg.topological_order().is_some() {
        return run_backward(cfg, site, oracle, &BTreeSet::new(), &[], tables);
    }

    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();
    let force_llm = config
        .and_then(|config| config.llm.as_ref())
        .is_some_and(|llm| llm.force);
    let invariants = if let Some(precomputed) = precomputed {
        if !precomputed.is_empty() && !force_llm {
            precomputed.to_vec()
        } else {
            synthesize_loop_invariants(cfg, function, site, oracle, config, &excluded)?
        }
    } else {
        synthesize_loop_invariants(cfg, function, site, oracle, config, &excluded)?
    };

    if invariants.is_empty() {
        return Err(BackwardError::CyclicCfgUnsupported);
    }

    run_backward(cfg, site, oracle, &excluded, &invariants, tables)
}

fn run_backward(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    excluded_edges: &BTreeSet<crate::common::abstract_cfg::CfgEdgeId>,
    loop_invariants: &[(CfgNodeId, Formula)],
    tables: &SummaryTables,
) -> Result<AssertionResult, BackwardError> {
    let mut cfg = cfg.clone();
    inject_loop_invariants(&mut cfg, loop_invariants)?;

    let order = cfg
        .topological_order_excluding(excluded_edges)
        .ok_or(BackwardError::CyclicCfgUnsupported)?;

    let mut engine = RuleEngine::new(&cfg);
    engine.init();

    for edge in excluded_edges {
        engine.block_edge(*edge);
    }

    for node in &order {
        for edge in cfg.outgoing_edges(*node) {
            engine.must_post(edge)?;
        }
    }

    let neg_obligation = Formula::not(site.obligation.clone());
    let pre_at_assertion = cfg
        .node(site.node)
        .map_err(|_| crate::may_must_analysis::rules::RuleError::UnknownNode { node: site.node })?
        .transfer
        .wp(&neg_obligation);
    engine.set_state(site.node, pre_at_assertion)?;
    engine.run_to_fixpoint(&order, tables, oracle)?;

    let bug = engine.bugfound(cfg.entry(), oracle)?;
    let judgement = if let Some(model) = bug {
        Judgement::BugFound { model }
    } else if engine.verified(cfg.entry(), oracle)? {
        Judgement::Verified
    } else {
        Judgement::Unknown
    };

    Ok(AssertionResult {
        site_id: site.id,
        site_label: site.location.clone(),
        judgement,
        entry_summary: engine.summary(cfg.entry())?.clone(),
        assertion_summary: engine.summary(site.node)?.clone(),
    })
}

pub fn discover_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    _oracle: &Oracle,
) -> Option<Vec<(CfgNodeId, Formula)>> {
    if cfg.topological_order().is_some() {
        return None;
    }
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let mut accepted = Vec::new();

    for (index, loop_info) in loops.into_iter().enumerate() {
        let candidates = algorithmic_candidates(&loop_info, cfg);
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} algorithmic candidates: {}",
            index + 1,
            format_candidates(&candidates)
        );
        let Some(candidate) = candidates.into_iter().next() else {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} produced no algorithmic candidate",
                index + 1
            );
            return None;
        };
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} precomputed algorithmic invariant: {}",
            index + 1,
            pretty_formula(&candidate)
        );
        accepted.push((loop_info.header, candidate));
    }

    Some(accepted)
}

fn synthesize_loop_invariants(
    cfg: &AbstractCfg,
    function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    config: Option<&InvariantConfig>,
    excluded_back_edges: &BTreeSet<CfgEdgeId>,
) -> Result<Vec<(CfgNodeId, Formula)>, BackwardError> {
    let assertion_postconditions =
        compute_preliminary_backward_states(cfg, site, excluded_back_edges)?;
    let mut loops = detect_loops(cfg);
    sort_innermost_first(&mut loops);
    let variable_sorts = collect_variable_sorts(cfg);
    let methods = selected_methods(config);
    let skip_algorithmic = config.is_some_and(|config| config.skip_algorithmic);
    let llm_config = config.and_then(|config| config.llm.as_ref());
    let force_llm = llm_config.is_some_and(|llm| llm.force);
    let mut accepted = Vec::<(CfgNodeId, Formula)>::new();

    for (index, loop_info) in loops.into_iter().enumerate() {
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} header {:?} body {:?}",
            index + 1,
            loop_info.header,
            loop_info.body
        );
        let augmented_cfg = cfg_with_invariants(cfg, &accepted)?;
        let mut accepted_candidate = None;

        if !skip_algorithmic && !force_llm {
            let candidates = algorithmic_candidates(&loop_info, cfg);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} algorithmic candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "algorithmic",
                &loop_info,
                &augmented_cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Chc) {
            let candidates = chc_loop_invariant(&loop_info, cfg)
                .into_iter()
                .collect::<Vec<_>>();
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} CHC candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "chc",
                &loop_info,
                &augmented_cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Houdini) {
            let header_wp = assertion_postconditions
                .get(&loop_info.header)
                .cloned()
                .unwrap_or(Formula::True);
            let loop_constants = collect_loop_body_int_constants(&loop_info, cfg);
            let candidates = houdini_candidates(&variable_sorts, &header_wp, &loop_constants);
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} houdini candidates: {}",
                index + 1,
                format_candidates(&candidates)
            );
            accepted_candidate = first_accepted_candidate(
                function,
                index + 1,
                "houdini",
                &loop_info,
                &augmented_cfg,
                &candidates,
                oracle,
                &assertion_postconditions,
                &accepted,
            );
        }

        if accepted_candidate.is_none() && methods.contains(&InvariantMethod::Template) {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} template candidates: []",
                index + 1
            );
            accepted_candidate = try_template_invariant();
        }

        if accepted_candidate.is_none() {
            if let Some(llm) = llm_config {
                let exit_postcondition = exit_postcondition_for_loop(
                    &loop_info,
                    &assertion_postconditions,
                    &augmented_cfg,
                );
                let mut attempts = Vec::<CegisAttempt>::new();
                for _ in 0..llm.max_tries.max(1) {
                    let ctx = build_full_loop_context(
                        LoopContext {
                            function: function.to_string(),
                            loop_id: index + 1,
                        },
                        &loop_info,
                        &augmented_cfg,
                        site.location.clone(),
                        exit_postcondition.clone(),
                        attempts.clone(),
                    );
                    let prompt = build_loop_invariant_prompt(&ctx, llm.prompt_template.as_deref());
                    let Some(raw) = llm.backend.propose(&prompt) else {
                        log::debug!(
                            target: "loop_invariant",
                            "function {function} loop {} llm candidate: <none>",
                            index + 1
                        );
                        continue;
                    };
                    let Some(candidate) = parse_candidate(&raw, &variable_sorts) else {
                        log::debug!(
                            target: "loop_invariant",
                            "function {function} loop {} llm candidate parse failed: {}",
                            index + 1,
                            raw.trim()
                        );
                        continue;
                    };
                    let result = check_loop_invariant_verbose(
                        &loop_info,
                        &augmented_cfg,
                        &candidate,
                        oracle,
                        &assertion_postconditions,
                        &accepted,
                    );
                    log::debug!(
                        target: "loop_invariant",
                        "function {function} loop {} llm candidate {} => {}",
                        index + 1,
                        pretty_formula(&candidate),
                        render_invariant_result(&result)
                    );
                    if result == InvariantCheckResult::Accepted {
                        accepted_candidate = Some(candidate);
                        break;
                    }
                    attempts.push(CegisAttempt {
                        candidate,
                        failure: render_invariant_result(&result),
                    });
                }
            }
        }

        if accepted_candidate.is_none() {
            log::debug!(
                target: "loop_invariant",
                "function {function} loop {} accepted no invariant",
                index + 1
            );
            return Err(BackwardError::CyclicCfgUnsupported);
        }

        let candidate = accepted_candidate.expect("checked accepted candidate presence");
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} accepted invariant: {}",
            index + 1,
            pretty_formula(&candidate)
        );
        accepted.push((loop_info.header, candidate));
    }

    Ok(accepted)
}

fn compute_preliminary_backward_states(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    excluded_back_edges: &BTreeSet<CfgEdgeId>,
) -> Result<BTreeMap<CfgNodeId, Formula>, BackwardError> {
    let order = cfg
        .topological_order_excluding(excluded_back_edges)
        .ok_or(BackwardError::CyclicCfgUnsupported)?;
    let mut engine = RuleEngine::new(cfg);
    engine.init();
    for edge in excluded_back_edges {
        engine.block_edge(*edge);
    }

    let neg_obligation = Formula::not(site.obligation.clone());
    let pre_at_assertion = cfg
        .node(site.node)
        .map_err(|_| crate::may_must_analysis::rules::RuleError::UnknownNode { node: site.node })?
        .transfer
        .wp(&neg_obligation);
    engine.set_state(site.node, pre_at_assertion)?;

    for node in order.iter().rev() {
        for edge in cfg.incoming_edges(*node) {
            engine.notmay_pre(edge)?;
        }
    }

    Ok(engine
        .summaries()
        .iter()
        .map(|(id, summary)| (*id, summary.state.clone()))
        .collect())
}

fn collect_variable_sorts(cfg: &AbstractCfg) -> BTreeMap<String, crate::common::formula::Sort> {
    let mut sorts = BTreeMap::new();
    for node in cfg.nodes().values() {
        for effect in &node.transfer.effects {
            collect_effect_sorts(effect, &mut sorts);
        }
    }
    for edge in cfg.edges().values() {
        collect_formula_sorts(&edge.guard, &mut sorts);
        for effect in &edge.effects {
            collect_effect_sorts(effect, &mut sorts);
        }
    }
    sorts
}

fn collect_effect_sorts(
    effect: &TransferEffect,
    sorts: &mut BTreeMap<String, crate::common::formula::Sort>,
) {
    use crate::common::abstract_cfg::AssignValue;
    match effect {
        TransferEffect::Assign { target, value } => {
            sorts.insert(target.name().to_string(), target.sort());
            match value {
                AssignValue::Term(term) => collect_term_sorts(term, sorts),
                AssignValue::Predicate(formula) => collect_formula_sorts(formula, sorts),
            }
        }
        TransferEffect::Assume(formula) | TransferEffect::Obligation(formula) => {
            collect_formula_sorts(formula, sorts)
        }
        TransferEffect::Load { target, .. } => {
            sorts.insert(target.name().to_string(), target.sort());
        }
        TransferEffect::MemoryStore { offset, value, .. } => {
            collect_term_sorts(offset, sorts);
            collect_term_sorts(value, sorts);
        }
        TransferEffect::GetElementPtr { offset, .. }
        | TransferEffect::Store { value: offset, .. } => {
            collect_term_sorts(offset, sorts);
        }
        TransferEffect::Alloca { .. }
        | TransferEffect::PointerStore { .. }
        | TransferEffect::PointerLoad { .. }
        | TransferEffect::Nop
        | TransferEffect::Call { .. } => {}
    }
}

fn collect_formula_sorts(
    formula: &Formula,
    sorts: &mut BTreeMap<String, crate::common::formula::Sort>,
) {
    match formula {
        Formula::True | Formula::False => {}
        Formula::Var(var) => {
            sorts.insert(var.name().to_string(), var.sort());
        }
        Formula::Not(inner) => collect_formula_sorts(inner, sorts),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_formula_sorts(item, sorts);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_formula_sorts(lhs, sorts);
            collect_formula_sorts(rhs, sorts);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_term_sorts(lhs, sorts);
            collect_term_sorts(rhs, sorts);
        }
        Formula::MemoryEq(_, _) => {}
    }
}

fn collect_term_sorts(
    term: &crate::common::formula::Term,
    sorts: &mut BTreeMap<String, crate::common::formula::Sort>,
) {
    use crate::common::formula::Term;

    match term {
        Term::Var(var) => {
            sorts.insert(var.name().to_string(), var.sort());
        }
        Term::Int(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_formula_sorts(inner, sorts),
        Term::Select(_, index) => collect_term_sorts(index, sorts),
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            collect_term_sorts(lhs, sorts);
            collect_term_sorts(rhs, sorts);
        }
        Term::Neg(inner) => collect_term_sorts(inner, sorts),
    }
}

fn selected_methods(config: Option<&InvariantConfig>) -> Vec<InvariantMethod> {
    let Some(config) = config else {
        return vec![
            InvariantMethod::Chc,
            InvariantMethod::Houdini,
            InvariantMethod::Template,
        ];
    };
    if config.methods.is_empty() {
        vec![
            InvariantMethod::Chc,
            InvariantMethod::Houdini,
            InvariantMethod::Template,
        ]
    } else {
        config.methods.clone()
    }
}

fn cfg_with_invariants(
    cfg: &AbstractCfg,
    invariants: &[(CfgNodeId, Formula)],
) -> Result<AbstractCfg, BackwardError> {
    let mut cfg = cfg.clone();
    inject_loop_invariants(&mut cfg, invariants)?;
    Ok(cfg)
}

fn inject_loop_invariants(
    cfg: &mut AbstractCfg,
    invariants: &[(CfgNodeId, Formula)],
) -> Result<(), BackwardError> {
    for (node, invariant) in invariants {
        let header = cfg
            .node_mut(*node)
            .map_err(|_| crate::may_must_analysis::rules::RuleError::UnknownNode { node: *node })?;
        let mut effects = vec![TransferEffect::Assume(invariant.clone())];
        effects.extend(std::mem::take(&mut header.transfer.effects));
        header.transfer.effects = effects;
    }
    Ok(())
}

fn first_accepted_candidate(
    function: &str,
    loop_index: usize,
    phase: &str,
    loop_info: &crate::may_must_analysis::loops::LoopInfo,
    cfg: &AbstractCfg,
    candidates: &[Formula],
    oracle: &Oracle,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    accepted_inner: &[(CfgNodeId, Formula)],
) -> Option<Formula> {
    for candidate in candidates {
        let result = check_loop_invariant_verbose(
            loop_info,
            cfg,
            candidate,
            oracle,
            assertion_postconditions,
            accepted_inner,
        );
        log::debug!(
            target: "loop_invariant",
            "function {function} loop {} {} candidate {} => {}",
            loop_index,
            phase,
            pretty_formula(candidate),
            render_invariant_result(&result)
        );
        if result == InvariantCheckResult::Accepted {
            return Some(candidate.clone());
        }
    }
    None
}

fn try_template_invariant() -> Option<Formula> {
    None
}

fn exit_postcondition_for_loop(
    loop_info: &crate::may_must_analysis::loops::LoopInfo,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    cfg: &AbstractCfg,
) -> Formula {
    let mut postconditions = Vec::new();
    for edge_id in &loop_info.exit_edges {
        let Ok(edge) = cfg.edge(*edge_id) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        postconditions.push(postcondition.clone());
    }
    Formula::or_all(postconditions)
}

fn render_invariant_result(result: &InvariantCheckResult) -> String {
    match result {
        InvariantCheckResult::Accepted => "accepted".to_string(),
        InvariantCheckResult::InitiationFailed => "rejected: initiation failed".to_string(),
        InvariantCheckResult::InductivenessFailed => "rejected: inductiveness failed".to_string(),
        InvariantCheckResult::ExitClosureFailed { exit_edge } => {
            format!("rejected: exit closure failed at edge {:?}", exit_edge)
        }
    }
}

fn format_candidates(candidates: &[Formula]) -> String {
    if candidates.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            candidates
                .iter()
                .map(pretty_formula)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub fn render_result(result: &AssertionResult) -> String {
    let mut lines = vec![format!(
        "  assertion #{} ({})",
        result.site_id, result.site_label
    )];
    lines.push(format!("    reach: {}", result.entry_summary.reach));
    lines.push(format!("    state: {}", result.entry_summary.state));
    match &result.judgement {
        Judgement::Verified => lines.push("    judgement: Verified".to_string()),
        Judgement::Unknown => lines.push("    judgement: Unknown".to_string()),
        Judgement::BugFound { model } => {
            lines.push("    judgement: BugFound".to_string());
            if let Some(model) = model.as_ref() {
                lines.push("    counterexample:".to_string());
                for line in model.to_string().lines() {
                    lines.push(format!("      {line}"));
                }
            }
        }
    }
    lines.join("\n")
}

pub fn pretty_formula(formula: &Formula) -> String {
    const WRAP_WIDTH: usize = 100;
    let rendered = formula.to_string();
    if rendered.len() <= WRAP_WIDTH {
        rendered
    } else {
        rendered.replace(" && ", "\n      && ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AssignValue, SourceLocation, TransferEffect, TransferFn};
    use crate::common::formula::{Sort, Term, Var};

    fn one_assertion_cfg() -> (AbstractCfg, AssertionSite) {
        let mut cfg = AbstractCfg::new("entry");
        let assert_node = cfg.add_node(
            "assert",
            TransferFn::new(vec![TransferEffect::Assign {
                target: Var::int("x"),
                value: AssignValue::Term(Term::int(1)),
            }]),
        );
        cfg.add_edge(cfg.entry(), assert_node, Formula::True, vec![])
            .unwrap();
        cfg.mark_exit(assert_node).unwrap();
        cfg.ensure_single_exit().unwrap();

        let site = AssertionSite {
            id: 1,
            node: assert_node,
            source_location: SourceLocation::new("t.c", 1, 1),
            location: "after assert".to_string(),
            obligation: Formula::eq(Term::var("x", Sort::Int), Term::int(1)),
        };
        (cfg, site)
    }

    #[test]
    fn analyze_returns_verified_for_trivial_safe_case() {
        let (cfg, site) = one_assertion_cfg();
        let oracle = Oracle::new();
        let result = analyze(&cfg, &site, &oracle).unwrap();
        assert!(matches!(result.judgement, Judgement::Verified));
    }

    #[test]
    fn analyze_rejects_cyclic_cfg() {
        let mut cfg = AbstractCfg::new("entry");
        let n = cfg.add_node("n", TransferFn::identity());
        cfg.add_edge(cfg.entry(), n, Formula::True, vec![]).unwrap();
        cfg.add_edge(n, cfg.entry(), Formula::True, vec![]).unwrap();
        cfg.mark_exit(n).unwrap();
        let site = AssertionSite {
            id: 1,
            node: n,
            source_location: SourceLocation::new("t.c", 1, 1),
            location: "loop".to_string(),
            obligation: Formula::True,
        };
        let oracle = Oracle::new();
        assert!(matches!(
            analyze(&cfg, &site, &oracle),
            Err(BackwardError::CyclicCfgUnsupported)
        ));
    }

    #[test]
    fn render_result_contains_judgement() {
        let (cfg, site) = one_assertion_cfg();
        let oracle = Oracle::new();
        let result = analyze(&cfg, &site, &oracle).unwrap();
        let rendered = render_result(&result);
        assert!(rendered.contains("judgement: Verified"));
    }
}
