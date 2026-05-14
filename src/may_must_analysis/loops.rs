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
    emit_counter_bounds(&mut candidates, &info.back_edge_guard);
    for edge_id in cfg.outgoing_edges(info.header) {
        if let Ok(edge) = cfg.edge(edge_id) {
            if info.body.contains(&edge.target) {
                push_nontrivial(&mut candidates, edge.guard.clone());
                emit_counter_bounds(&mut candidates, &edge.guard);
            }
        }
    }
    for edge_id in &info.exit_edges {
        if let Ok(edge) = cfg.edge(*edge_id) {
            push_nontrivial(&mut candidates, Formula::not(edge.guard.clone()));
            emit_counter_bounds(&mut candidates, &edge.guard);
        }
    }
    for node in &info.body {
        if let Ok(node) = cfg.node(*node) {
            for effect in &node.transfer.effects {
                match effect {
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Predicate(predicate),
                    } => {
                        push_nontrivial(&mut candidates, predicate.clone());
                        push_nontrivial(&mut candidates, Formula::not(predicate.clone()));
                        emit_counter_bounds(&mut candidates, predicate);
                        if target.sort() == Sort::Bool {
                            push_nontrivial(
                                &mut candidates,
                                Formula::implies(Formula::Var(target.clone()), predicate.clone()),
                            );
                        }
                    }
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Term(Term::Int(value)),
                    } if target.sort() == Sort::Int => {
                        push_nontrivial(
                            &mut candidates,
                            Formula::ge(Term::Var(target.clone()), Term::int(*value)),
                        );
                    }
                    TransferEffect::Assign {
                        target,
                        value: AssignValue::Term(term),
                    } if target.sort() == Sort::Int => {
                        if is_self_increment(target, term) {
                            push_nontrivial(
                                &mut candidates,
                                Formula::ge(Term::Var(target.clone()), Term::int(0)),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    candidates
}

pub fn houdini_candidates(
    variable_sorts: &BTreeMap<String, Sort>,
    header_wp: &Formula,
    loop_constants: &BTreeSet<i64>,
) -> Vec<Formula> {
    let constants = collect_int_constants(header_wp)
        .into_iter()
        .chain(loop_constants.iter().copied())
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
        let constants_vec = constants.iter().copied().collect::<Vec<_>>();
        for (index, lower) in constants_vec.iter().enumerate() {
            for upper in constants_vec.iter().skip(index + 1) {
                candidates.push(Formula::and(
                    Formula::ge(Term::Var(var.clone()), Term::int(*lower)),
                    Formula::le(Term::Var(var.clone()), Term::int(*upper)),
                ));
            }
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
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    _inner: InnerInvariants<'_>,
) -> InvariantCheckResult {
    let excluded = cfg.detect_back_edges().into_iter().collect::<BTreeSet<_>>();
    let Some(initiation_states) = backward_states(
        cfg,
        &[(info.header, Formula::not(candidate.clone()))],
        &excluded,
        None,
    ) else {
        return InvariantCheckResult::InitiationFailed;
    };
    let entry_violation = initiation_states
        .get(&cfg.entry())
        .cloned()
        .unwrap_or(Formula::False);
    match oracle.feasibility(&entry_violation) {
        Ok(crate::common::oracle::Feasibility::Feasible) => {
            return InvariantCheckResult::InitiationFailed;
        }
        Ok(crate::common::oracle::Feasibility::Unknown) | Err(_) => {
            return InvariantCheckResult::InitiationFailed;
        }
        Ok(crate::common::oracle::Feasibility::Infeasible) => {}
    }

    let Some(back_edge_requirement) = edge_source_requirement(cfg, info.back_edge, candidate)
    else {
        return InvariantCheckResult::InductivenessFailed;
    };
    let Some(inductive_states) = backward_states(
        cfg,
        &[(info.latch, back_edge_requirement)],
        &excluded,
        Some(&info.body),
    ) else {
        return InvariantCheckResult::InductivenessFailed;
    };
    let inductive_header = inductive_states
        .get(&info.header)
        .cloned()
        .unwrap_or(Formula::False);
    match oracle.implies(candidate, &inductive_header) {
        Ok(Validity::Valid) => {}
        Ok(Validity::Invalid) => return InvariantCheckResult::InductivenessFailed,
        Ok(Validity::Unknown) | Err(_) => return InvariantCheckResult::InductivenessFailed,
    }

    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(postcondition) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *postcondition == Formula::False {
            continue;
        }
        let Some(exit_requirement) = edge_source_requirement(cfg, *exit_edge, postcondition) else {
            return InvariantCheckResult::ExitClosureFailed {
                exit_edge: *exit_edge,
            };
        };
        let Some(exit_states) = backward_states(
            cfg,
            &[(edge.source, exit_requirement)],
            &excluded,
            Some(&info.body),
        ) else {
            return InvariantCheckResult::ExitClosureFailed {
                exit_edge: *exit_edge,
            };
        };
        let exit_header = exit_states
            .get(&info.header)
            .cloned()
            .unwrap_or(Formula::False);
        match oracle.implies(candidate, &exit_header) {
            Ok(Validity::Valid) => {}
            Ok(Validity::Invalid) | Ok(Validity::Unknown) | Err(_) => {
                return InvariantCheckResult::ExitClosureFailed {
                    exit_edge: *exit_edge,
                };
            }
        }
    }

    InvariantCheckResult::Accepted
}

fn emit_counter_bounds(candidates: &mut Vec<Formula>, formula: &Formula) {
    let Some((counter, bound)) = extract_counter_bound(formula) else {
        return;
    };
    let lower = Formula::ge(counter.clone(), Term::int(0));
    let upper = Formula::le(counter.clone(), bound);
    push_nontrivial(candidates, lower.clone());
    push_nontrivial(candidates, upper.clone());
    push_nontrivial(candidates, Formula::and(lower, upper));
}

fn push_nontrivial(candidates: &mut Vec<Formula>, formula: Formula) {
    if formula != Formula::True && formula != Formula::False && !candidates.contains(&formula) {
        candidates.push(formula);
    }
}

fn extract_counter_bound(formula: &Formula) -> Option<(Term, Term)> {
    match formula {
        Formula::Lt(counter, bound) | Formula::Le(counter, bound) => {
            matches_int_counter(counter, bound)
        }
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Ge(counter, bound) => matches_int_counter(counter, bound),
            _ => None,
        },
        _ => None,
    }
}

fn matches_int_counter(counter: &Term, bound: &Term) -> Option<(Term, Term)> {
    if !matches!(counter, Term::Var(var) if var.sort() == Sort::Int) {
        return None;
    }
    if bound.sort().ok()? != Sort::Int {
        return None;
    }
    Some((counter.clone(), bound.clone()))
}

fn is_self_increment(target: &Var, term: &Term) -> bool {
    match term {
        Term::Add(lhs, rhs) => {
            matches_same_var(lhs, target) && matches!(rhs.as_ref(), Term::Int(_))
                || matches_same_var(rhs, target) && matches!(lhs.as_ref(), Term::Int(_))
        }
        Term::Sub(lhs, rhs) => {
            matches_same_var(lhs, target) && matches!(rhs.as_ref(), Term::Int(_))
        }
        _ => false,
    }
}

fn matches_same_var(term: &Term, target: &Var) -> bool {
    matches!(term, Term::Var(var) if var == target)
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

fn backward_states(
    cfg: &AbstractCfg,
    seeds: &[(CfgNodeId, Formula)],
    excluded_edges: &BTreeSet<CfgEdgeId>,
    restrict_to: Option<&BTreeSet<CfgNodeId>>,
) -> Option<BTreeMap<CfgNodeId, Formula>> {
    let order = cfg.topological_order_excluding(excluded_edges)?;
    let mut states = cfg
        .node_ids()
        .map(|id| (id, Formula::False))
        .collect::<BTreeMap<_, _>>();
    for (node, formula) in seeds {
        let entry = states.entry(*node).or_insert(Formula::False);
        *entry = Formula::or(entry.clone(), formula.clone());
    }

    for node in order.iter().rev() {
        for edge_id in cfg.incoming_edges(*node) {
            if excluded_edges.contains(&edge_id) {
                continue;
            }
            let edge = cfg.edge(edge_id).ok()?;
            if let Some(body) = restrict_to {
                if !body.contains(&edge.source) || !body.contains(&edge.target) {
                    continue;
                }
            }
            let target_state = states.get(&edge.target).cloned().unwrap_or(Formula::False);
            let edge_pre = edge.transfer().wp(&target_state);
            let post_at_source = Formula::and(edge.guard.clone(), edge_pre);
            let pre_at_source = cfg.node(edge.source).ok()?.transfer.wp(&post_at_source);
            let existing = states.get(&edge.source).cloned().unwrap_or(Formula::False);
            states.insert(edge.source, Formula::or(existing, pre_at_source));
        }
    }

    Some(states)
}

fn edge_source_requirement(
    cfg: &AbstractCfg,
    edge_id: CfgEdgeId,
    target: &Formula,
) -> Option<Formula> {
    let edge = cfg.edge(edge_id).ok()?;
    let edge_pre = edge.transfer().wp(target);
    let post_at_source = Formula::and(edge.guard.clone(), edge_pre);
    Some(cfg.node(edge.source).ok()?.transfer.wp(&post_at_source))
}

pub fn collect_loop_body_int_constants(info: &LoopInfo, cfg: &AbstractCfg) -> BTreeSet<i64> {
    let mut constants = BTreeSet::new();
    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        for effect in &node.transfer.effects {
            match effect {
                TransferEffect::Assign {
                    value: AssignValue::Term(Term::Int(value)),
                    ..
                }
                | TransferEffect::MemoryStore {
                    value: Term::Int(value),
                    ..
                } => {
                    constants.insert(*value);
                }
                _ => {}
            }
        }
    }
    constants
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::abstract_cfg::{AssignValue, TransferFn};

    #[test]
    fn algorithmic_candidates_include_counter_bounds() {
        let mut cfg = AbstractCfg::new("entry");
        let header = cfg.add_node("header", TransferFn::identity());
        let latch = cfg.add_node(
            "latch",
            TransferFn::new(vec![TransferEffect::Assign {
                target: Var::int("i"),
                value: AssignValue::Term(Term::add(Term::var("i", Sort::Int), Term::int(1))),
            }]),
        );
        let exit = cfg.add_node("exit", TransferFn::identity());
        cfg.add_edge(cfg.entry(), header, Formula::True, vec![])
            .unwrap();
        cfg.add_edge(
            header,
            latch,
            Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
            vec![],
        )
        .unwrap();
        let back_edge = cfg
            .add_edge(
                latch,
                header,
                Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
                vec![],
            )
            .unwrap();
        let exit_edge = cfg
            .add_edge(
                latch,
                exit,
                Formula::not(Formula::lt(
                    Term::var("i", Sort::Int),
                    Term::var("n", Sort::Int),
                )),
                vec![],
            )
            .unwrap();
        let info = LoopInfo {
            header,
            latch,
            back_edge,
            body: BTreeSet::from([header, latch]),
            exit_edges: vec![exit_edge],
            back_edge_guard: Formula::lt(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
            source_location: None,
        };

        let candidates = algorithmic_candidates(&info, &cfg);

        assert!(candidates.contains(&Formula::ge(Term::var("i", Sort::Int), Term::int(0))));
        assert!(candidates.contains(&Formula::le(
            Term::var("i", Sort::Int),
            Term::var("n", Sort::Int)
        )));
        assert!(candidates.contains(&Formula::and(
            Formula::ge(Term::var("i", Sort::Int), Term::int(0)),
            Formula::le(Term::var("i", Sort::Int), Term::var("n", Sort::Int)),
        )));
    }

    #[test]
    fn houdini_candidates_include_range_conjunctions() {
        let variable_sorts = BTreeMap::from([("i".to_string(), Sort::Int)]);
        let loop_constants = BTreeSet::from([5]);
        let candidates = houdini_candidates(&variable_sorts, &Formula::True, &loop_constants);
        assert!(candidates.contains(&Formula::and(
            Formula::ge(Term::var("i", Sort::Int), Term::int(0)),
            Formula::le(Term::var("i", Sort::Int), Term::int(5)),
        )));
    }
}
