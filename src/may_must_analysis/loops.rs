#![allow(dead_code)]

use crate::common::abstract_cfg::{
    AbstractCfg, AssignValue, CfgEdgeId, CfgNodeId, SourceLocation, TransferEffect,
};
use crate::common::formula::{Formula, Sort, Term, Var};
use crate::common::oracle::{Oracle, Validity};
use crate::may_must_analysis::chc;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopInfo {
    pub header: CfgNodeId,
    pub latch: CfgNodeId,
    pub back_edge: CfgEdgeId,
    pub body: BTreeSet<CfgNodeId>,
    pub exit_edges: Vec<CfgEdgeId>,
    pub back_edge_guard: Formula,
    pub source_location: Option<SourceLocation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CounterInit {
    Literal(i64),
    Variable(String),
    Unknown,
}

pub type InnerInvariants<'a> = &'a [(CfgNodeId, Formula)];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InvariantCheckResult {
    Accepted,
    InitiationFailed,
    InductivenessFailed,
    ExitClosureFailed { exit_edge: CfgEdgeId },
}

pub fn fmt_loop_loc(info: &LoopInfo) -> String {
    info.source_location
        .as_ref()
        .map(|location| location.to_string())
        .unwrap_or_else(|| format!("header {:?}", info.header))
}

pub fn detect_loops(cfg: &AbstractCfg) -> Vec<LoopInfo> {
    cfg.detect_back_edges()
        .into_iter()
        .filter_map(|edge_id| {
            let edge = cfg.edge(edge_id).ok()?.clone();
            let mut body = BTreeSet::new();
            body.insert(edge.target);
            body.insert(edge.source);
            let mut queue = VecDeque::from([edge.source]);
            while let Some(node) = queue.pop_front() {
                for pred in cfg.predecessors(node) {
                    if body.insert(pred) {
                        queue.push_back(pred);
                    }
                }
            }
            let mut exit_edges = Vec::new();
            for node in &body {
                for out in cfg.outgoing_edges(*node) {
                    let out_edge = cfg.edge(out).ok()?;
                    if !body.contains(&out_edge.target) {
                        exit_edges.push(out);
                    }
                }
            }
            Some(LoopInfo {
                header: edge.target,
                latch: edge.source,
                back_edge: edge.id,
                body,
                exit_edges,
                back_edge_guard: edge.guard,
                source_location: cfg
                    .node(edge.target)
                    .ok()
                    .and_then(|node| node.source_location.clone()),
            })
        })
        .collect()
}

pub fn sort_innermost_first(loops: &mut [LoopInfo]) {
    loops.sort_by_key(|info| info.body.len());
}

pub fn algorithmic_candidates(info: &LoopInfo, cfg: &AbstractCfg) -> Vec<Formula> {
    let mut candidates = Vec::new();
    push_nontrivial(&mut candidates, info.back_edge_guard.clone());
    for edge_id in &info.exit_edges {
        if let Ok(edge) = cfg.edge(*edge_id) {
            push_nontrivial(&mut candidates, Formula::not(edge.guard.clone()));
        }
    }
    for node in &info.body {
        if let Ok(node) = cfg.node(*node) {
            for effect in &node.transfer.effects {
                if let TransferEffect::Assign {
                    value: AssignValue::Predicate(predicate),
                    ..
                } = effect
                {
                    push_nontrivial(&mut candidates, predicate.clone());
                    push_nontrivial(&mut candidates, Formula::not(predicate.clone()));
                }
            }
        }
    }
    candidates
}

pub fn houdini_candidates(
    variable_sorts: &BTreeMap<String, Sort>,
    header_wp: &Formula,
) -> Vec<Formula> {
    let constants = collect_int_constants(header_wp)
        .into_iter()
        .chain([-1, 0, 1])
        .collect::<BTreeSet<_>>();
    let vars = variable_sorts
        .iter()
        .filter_map(|(name, sort)| (*sort == Sort::Int).then_some(Var::int(name.clone())))
        .collect::<Vec<_>>();
    let mut candidates = Vec::new();
    for var in &vars {
        for constant in &constants {
            let term = Term::Var(var.clone());
            candidates.push(Formula::ge(term.clone(), Term::int(*constant)));
            candidates.push(Formula::le(term, Term::int(*constant)));
        }
    }
    for left in &vars {
        for right in &vars {
            if left == right {
                continue;
            }
            candidates.push(Formula::le(
                Term::Var(left.clone()),
                Term::Var(right.clone()),
            ));
            candidates.push(Formula::ge(
                Term::Var(left.clone()),
                Term::Var(right.clone()),
            ));
            candidates.push(Formula::le(
                Term::add(Term::Var(left.clone()), Term::int(1)),
                Term::Var(right.clone()),
            ));
        }
    }
    candidates
}

pub fn chc_loop_invariant(info: &LoopInfo, cfg: &AbstractCfg) -> Option<Formula> {
    let guard = &info.back_edge_guard;
    if let Formula::Lt(Term::Var(counter), Term::Var(bound)) = guard {
        return chc::solve_loop_chc(counter.clone(), bound.clone(), Some(0), 1, None);
    }
    let _ = cfg;
    None
}

pub fn check_loop_invariant(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    candidate: &Formula,
    oracle: &Oracle,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
) -> bool {
    matches!(
        check_loop_invariant_verbose(
            info,
            cfg,
            candidate,
            oracle,
            assertion_postconditions,
            inner
        ),
        InvariantCheckResult::Accepted
    )
}

pub fn check_loop_invariant_verbose(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    candidate: &Formula,
    oracle: &Oracle,
    _assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    _inner: InnerInvariants<'_>,
) -> InvariantCheckResult {
    let normalized = cfg
        .node(info.header)
        .map(|node| node.transfer.wp(candidate))
        .unwrap_or_else(|_| candidate.clone());
    match oracle.implies(&normalized, candidate) {
        Ok(Validity::Invalid) => InvariantCheckResult::InductivenessFailed,
        Ok(Validity::Unknown) | Err(_) => InvariantCheckResult::InitiationFailed,
        Ok(Validity::Valid) => InvariantCheckResult::Accepted,
    }
}

fn push_nontrivial(candidates: &mut Vec<Formula>, formula: Formula) {
    if formula != Formula::True && formula != Formula::False && !candidates.contains(&formula) {
        candidates.push(formula);
    }
}

fn collect_int_constants(formula: &Formula) -> Vec<i64> {
    let mut constants = Vec::new();
    collect_int_constants_formula(formula, &mut constants);
    constants
}

fn collect_int_constants_formula(formula: &Formula, out: &mut Vec<i64>) {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => {}
        Formula::Not(inner) => collect_int_constants_formula(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_int_constants_formula(item, out);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_int_constants_formula(lhs, out);
            collect_int_constants_formula(rhs, out);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_int_constants_term(lhs, out);
            collect_int_constants_term(rhs, out);
        }
        Formula::MemoryEq(_, _) => {}
    }
}

fn collect_int_constants_term(term: &Term, out: &mut Vec<i64>) {
    match term {
        Term::Int(value) => out.push(*value),
        Term::Var(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_int_constants_formula(inner, out),
        Term::Select(_, index) => collect_int_constants_term(index, out),
        Term::Add(lhs, rhs) | Term::Sub(lhs, rhs) | Term::Mul(lhs, rhs) | Term::Div(lhs, rhs) => {
            collect_int_constants_term(lhs, out);
            collect_int_constants_term(rhs, out);
        }
        Term::Neg(inner) => collect_int_constants_term(inner, out),
    }
}
