#![allow(dead_code)]

use crate::common::abstract_cfg::{AbstractCfg, CfgNodeId};
use crate::common::adapter::AssertionSite;
use crate::common::formula::Formula;
use crate::common::oracle::{Oracle, OracleError};
use crate::may_must_analysis::llm_provider::LlmBackend;
use crate::may_must_analysis::node_summary::NodeSummary;
use crate::may_must_analysis::rules::{Judgement, RuleEngine, RuleError};
use crate::may_must_analysis::summaries::SummaryTables;
use std::collections::BTreeSet;

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
    #[error("CFG has a cycle; loops are not supported")]
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
    _function: &str,
    site: &AssertionSite,
    oracle: &Oracle,
    _tables: &SummaryTables,
    _config: Option<&InvariantConfig>,
    precomputed: Option<&[(CfgNodeId, Formula)]>,
) -> Result<AssertionResult, BackwardError> {
    let excluded = if cfg.topological_order().is_none() {
        if let Some(invariants) = precomputed {
            if !invariants.is_empty() {
                cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>()
            } else {
                return Err(BackwardError::CyclicCfgUnsupported);
            }
        } else {
            return Err(BackwardError::CyclicCfgUnsupported);
        }
    } else {
        BTreeSet::new()
    };

    run_backward(cfg, site, oracle, &excluded, precomputed.unwrap_or(&[]))
}

fn run_backward(
    cfg: &AbstractCfg,
    site: &AssertionSite,
    oracle: &Oracle,
    excluded_edges: &BTreeSet<crate::common::abstract_cfg::CfgEdgeId>,
    loop_invariants: &[(CfgNodeId, Formula)],
) -> Result<AssertionResult, BackwardError> {
    let order = cfg
        .topological_order_excluding(excluded_edges)
        .ok_or(BackwardError::CyclicCfgUnsupported)?;

    let mut engine = RuleEngine::new(cfg);
    engine.init();

    for edge in excluded_edges {
        engine.block_edge(*edge);
    }

    for (node, invariant) in loop_invariants {
        let reach = engine.summary(*node)?.reach.clone();
        engine.summary_mut(*node)?.reach = Formula::and(reach, invariant.clone());
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

    for node in order.iter().rev() {
        for edge in cfg.incoming_edges(*node) {
            engine.notmay_pre(edge)?;
        }
    }

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
    _function: &str,
    _oracle: &Oracle,
) -> Option<Vec<(CfgNodeId, Formula)>> {
    if cfg.topological_order().is_some() {
        return None;
    }
    None
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
