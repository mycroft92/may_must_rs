//! Grammar-based loop invariant synthesis with ICE (Inductive CounterExample) learning.
//!
//! Implements the ACHAR approach (Lahiri & Roy, ISSTA '22): enumerate candidates
//! from a grammar over the loop's variable vocabulary; use an SMT oracle as the
//! teacher to collect positive/negative example states; filter atoms by the
//! examples before generating conjunction/disjunction candidates.
//!
//! # ICE learning overview
//!
//! Three kinds of examples guide the search:
//! - **Positive examples** — states where the invariant *must* hold (initial state
//!   at the loop header, from the forward reach).
//! - **Negative examples** — states where the invariant *must not* hold (violation
//!   states at loop exits, from assertion postconditions).
//!
//! An atom is *positive-consistent* if it is not false on any positive example.
//! An atom is a *safety atom* if it is false on at least one negative example
//! (it rules out violation states).
//!
//! Candidates are generated in priority order:
//! 1. Positive-consistent atoms (good inductive candidates).
//! 2. Pairwise conjunctions of positive-consistent atoms (capped at [`MAX_CONJUNCTIONS`]).
//! 3. Observer-style and ICE-guided disjunctions: `pos_atom || safety_atom`.
//! 4. General pairwise disjunctions of positive-consistent atoms.
//!
//! # Vocabulary filtering
//!
//! LLVM-internal variables (`__vla_expr*` VLA size tracking) are excluded from
//! the term vocabulary.  They never participate in assertion conditions and only
//! inflate the atom space.
//!
//! This module is intentionally independent of the entry-safety synthesis pass
//! in `loops.rs`.

use crate::common::abstract_cfg::{AbstractCfg, AssignValue, CfgNodeId, TransferEffect};
use crate::common::formula::{Formula, Memory, ModelValue, SmtModel, Sort, Term, Var};
use crate::common::oracle::{Feasibility, Oracle};
use crate::may_must_analysis::loops::{
    extract_back_edge_counter, formula_conjuncts, forward_reach_at_header, negate_comparison,
    InnerInvariants, LoopInfo,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Cap on pairwise conjunctions, ICE-guided disjunctions, and general pairwise disjunctions.
const MAX_CONJUNCTIONS: usize = 60;
const MAX_ICE_DISJ: usize = 120;
const MAX_PAIRWISE_DISJ: usize = 60;

// ── ICE example types ─────────────────────────────────────────────────────────

/// A concrete program state extracted from an SMT model.
///
/// Scalar values are keyed by variable name. Array regions are stored as a
/// default value (the `ArrayDefault` constant Z3 assigns to unconstrained arrays).
#[derive(Clone, Debug, Default)]
pub(crate) struct IceState {
    pub scalars: HashMap<String, i64>,
    pub arrays: HashMap<String, i64>,
}

impl IceState {
    fn from_model(model: &SmtModel) -> Self {
        let mut scalars = HashMap::new();
        let mut arrays = HashMap::new();
        for (var, value) in &model.scalar {
            if let ModelValue::Int(n) = value {
                scalars.insert(var.name().to_string(), *n);
            }
            if let ModelValue::Bool(b) = value {
                scalars.insert(var.name().to_string(), if *b { 1 } else { 0 });
            }
        }
        for (name, value) in &model.memory {
            match value {
                ModelValue::ArrayDefault(inner) => {
                    if let ModelValue::Int(n) = inner.as_ref() {
                        arrays.insert(name.clone(), *n);
                    }
                }
                ModelValue::Int(n) => {
                    arrays.insert(name.clone(), *n);
                }
                _ => {}
            }
        }
        IceState { scalars, arrays }
    }
}

/// Evaluate a term at a concrete state. Returns `None` for unsupported shapes.
fn eval_term(term: &Term, state: &IceState) -> Option<i64> {
    match term {
        Term::Var(v) if v.sort() == Sort::Int => state.scalars.get(v.name()).copied(),
        Term::Int(n) => Some(*n),
        Term::Select(mem, idx) => {
            let idx_val = eval_term(idx, state)?;
            match mem.as_ref() {
                Memory::Var(name) => {
                    // Use default array value; may not match a specific index but
                    // is the best approximation from Z3's ArrayDefault model.
                    let default = state.arrays.get(name.as_str()).copied()?;
                    let _ = idx_val; // index not used with ArrayDefault
                    Some(default)
                }
                _ => None,
            }
        }
        Term::Add(a, b) => Some(eval_term(a, state)?.wrapping_add(eval_term(b, state)?)),
        Term::Sub(a, b) => Some(eval_term(a, state)?.wrapping_sub(eval_term(b, state)?)),
        Term::Mul(a, b) => Some(eval_term(a, state)?.wrapping_mul(eval_term(b, state)?)),
        Term::Div(a, b) => {
            let d = eval_term(b, state)?;
            if d == 0 {
                return None;
            }
            Some(eval_term(a, state)? / d)
        }
        Term::Rem(a, b) => {
            let d = eval_term(b, state)?;
            if d == 0 {
                return None;
            }
            Some(eval_term(a, state)? % d)
        }
        Term::Neg(a) => Some(-eval_term(a, state)?),
        _ => None,
    }
}

/// Evaluate an atom at a concrete state. Returns `None` for compound formulas.
fn eval_atom(atom: &Formula, state: &IceState) -> Option<bool> {
    match atom {
        Formula::Le(a, b) => Some(eval_term(a, state)? <= eval_term(b, state)?),
        Formula::Lt(a, b) => Some(eval_term(a, state)? < eval_term(b, state)?),
        Formula::Ge(a, b) => Some(eval_term(a, state)? >= eval_term(b, state)?),
        Formula::Gt(a, b) => Some(eval_term(a, state)? > eval_term(b, state)?),
        Formula::Eq(a, b) => Some(eval_term(a, state)? == eval_term(b, state)?),
        Formula::Not(inner) => eval_atom(inner, state).map(|b| !b),
        _ => None,
    }
}

// ── ICE example collection ────────────────────────────────────────────────────

/// Ask the oracle for a concrete model of the forward reach at the loop header.
/// Returns `None` if the formula is infeasible or the solver returns no model.
fn collect_positive_example(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    inner: InnerInvariants<'_>,
    oracle: &Oracle,
) -> Option<IceState> {
    let reach = forward_reach_at_header(cfg, info.header, inner);
    if reach == Formula::True {
        return None; // reach=True gives no useful constraints
    }
    let report = oracle.feasibility_with_model(&reach).ok()?;
    if report.feasibility != Feasibility::Feasible {
        return None;
    }
    report.model.as_ref().map(IceState::from_model)
}

/// Ask the oracle for concrete models of each exit violation.
/// Each feasible violation state becomes a negative example.
fn collect_negative_examples(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    oracle: &Oracle,
) -> Vec<IceState> {
    let mut examples = Vec::new();
    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(violation) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *violation == Formula::False {
            continue;
        }
        let Ok(report) = oracle.feasibility_with_model(violation) else {
            continue;
        };
        if let Some(model) = report.model {
            examples.push(IceState::from_model(&model));
        }
    }
    examples
}

// ── Atom filtering by ICE examples ───────────────────────────────────────────

/// Keep atoms that are not false on any positive example.
///
/// An atom that evaluates to `false` at the initial state cannot be part of the
/// invariant (it would fail initiation immediately). Atoms that evaluate to `None`
/// (unevaluable) are kept — they may still be useful.
fn filter_positive_consistent<'a>(atoms: &'a [Formula], positive: &IceState) -> Vec<&'a Formula> {
    atoms
        .iter()
        .filter(|atom| eval_atom(atom, positive) != Some(false))
        .collect()
}

/// Find atoms that are false on at least one negative example (violation state).
///
/// These "safety atoms" rule out violation states; they are strong candidates
/// for the safety condition in a disjunctive invariant `inductive || safety`.
fn find_safety_atoms<'a>(atoms: &'a [Formula], negatives: &[IceState]) -> Vec<&'a Formula> {
    atoms
        .iter()
        .filter(|atom| {
            negatives
                .iter()
                .any(|state| eval_atom(atom, state) == Some(false))
        })
        .collect()
}

// ── Vocabulary ────────────────────────────────────────────────────────────────

struct Vocab {
    /// Integer-sorted terms: loop variables and `select(region, idx)` reads.
    terms: Vec<Term>,
    /// Integer constants seen in the loop body, plus 0 and 1.
    constants: Vec<i64>,
}

fn collect_vocab(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
) -> Vocab {
    let mut vars: BTreeSet<Var> = BTreeSet::new();
    let mut consts: BTreeSet<i64> = BTreeSet::from([0, 1]);
    let mut selects: Vec<Term> = Vec::new();

    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        for effect in &node.transfer.effects {
            collect_effect_vocab(effect, &mut vars, &mut consts, &mut selects);
        }
    }
    collect_formula_vocab(&info.back_edge_guard, &mut vars, &mut consts);

    for formula in assertion_postconditions.values() {
        collect_select_terms(formula, &mut selects);
    }
    dedup_terms(&mut selects);

    // Filter LLVM-internal variables that don't correspond to source-level program state.
    // __vla_expr* are VLA size tracking variables; they add noise without helping proofs.
    let terms: Vec<Term> = vars
        .into_iter()
        .filter(|v| !v.name().contains("__vla_expr"))
        .map(Term::Var)
        .chain(selects)
        .collect();

    Vocab {
        terms,
        constants: consts.into_iter().collect(),
    }
}

fn collect_effect_vocab(
    effect: &TransferEffect,
    vars: &mut BTreeSet<Var>,
    consts: &mut BTreeSet<i64>,
    selects: &mut Vec<Term>,
) {
    match effect {
        TransferEffect::Assign { target, value } => {
            if target.sort() == Sort::Int {
                vars.insert(target.clone());
            }
            match value {
                AssignValue::Term(t) => collect_term_vocab(t, vars, consts, selects),
                AssignValue::Predicate(f) => collect_formula_vocab(f, vars, consts),
            }
        }
        TransferEffect::MemoryStore { value, .. } => {
            collect_term_vocab(value, vars, consts, selects);
        }
        _ => {}
    }
}

fn collect_term_vocab(
    term: &Term,
    vars: &mut BTreeSet<Var>,
    consts: &mut BTreeSet<i64>,
    selects: &mut Vec<Term>,
) {
    match term {
        Term::Var(v) if v.sort() == Sort::Int => {
            vars.insert(v.clone());
        }
        Term::Int(n) => {
            consts.insert(*n);
        }
        Term::Select(arr, idx) => {
            selects.push(Term::Select(arr.clone(), idx.clone()));
            collect_term_vocab(idx, vars, consts, selects);
        }
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            collect_term_vocab(a, vars, consts, selects);
            collect_term_vocab(b, vars, consts, selects);
        }
        Term::Neg(a) => collect_term_vocab(a, vars, consts, selects),
        _ => {}
    }
}

fn collect_formula_vocab(formula: &Formula, vars: &mut BTreeSet<Var>, consts: &mut BTreeSet<i64>) {
    let mut ignored = Vec::new();
    match formula {
        Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Eq(a, b)
        | Formula::Ge(a, b)
        | Formula::Gt(a, b) => {
            collect_term_vocab(a, vars, consts, &mut ignored);
            collect_term_vocab(b, vars, consts, &mut ignored);
        }
        Formula::And(items) | Formula::Or(items) => {
            for f in items {
                collect_formula_vocab(f, vars, consts);
            }
        }
        Formula::Not(f) => collect_formula_vocab(f, vars, consts),
        Formula::Implies(lhs, rhs) => {
            collect_formula_vocab(lhs, vars, consts);
            collect_formula_vocab(rhs, vars, consts);
        }
        _ => {}
    }
}

fn collect_select_terms(formula: &Formula, out: &mut Vec<Term>) {
    match formula {
        Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Eq(a, b)
        | Formula::Ge(a, b)
        | Formula::Gt(a, b) => {
            collect_select_in_term(a, out);
            collect_select_in_term(b, out);
        }
        Formula::And(items) | Formula::Or(items) => {
            for f in items {
                collect_select_terms(f, out);
            }
        }
        Formula::Not(f) => collect_select_terms(f, out),
        Formula::Implies(lhs, rhs) => {
            collect_select_terms(lhs, out);
            collect_select_terms(rhs, out);
        }
        _ => {}
    }
}

fn collect_select_in_term(term: &Term, out: &mut Vec<Term>) {
    match term {
        Term::Select(arr, idx) => {
            out.push(Term::Select(arr.clone(), idx.clone()));
            collect_select_in_term(idx, out);
        }
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            collect_select_in_term(a, out);
            collect_select_in_term(b, out);
        }
        Term::Neg(a) => collect_select_in_term(a, out),
        _ => {}
    }
}

fn dedup_terms(terms: &mut Vec<Term>) {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    terms.retain(|t| seen.insert(format!("{t:?}")));
}

// ── Atom generation ───────────────────────────────────────────────────────────

fn generate_atoms(vocab: &Vocab) -> Vec<Formula> {
    let mut atoms = Vec::new();

    let n = vocab.terms.len();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let a = &vocab.terms[i];
            let b = &vocab.terms[j];
            if format!("{a:?}") == format!("{b:?}") {
                continue;
            }
            atoms.push(Formula::le(a.clone(), b.clone()));
            atoms.push(Formula::lt(a.clone(), b.clone()));
            atoms.push(Formula::eq(a.clone(), b.clone()));
        }
    }

    for term in &vocab.terms {
        for &c in &vocab.constants {
            let a = term.clone();
            let b = Term::int(c);
            atoms.push(Formula::le(a.clone(), b.clone()));
            atoms.push(Formula::lt(a.clone(), b.clone()));
            atoms.push(Formula::ge(a.clone(), b.clone()));
            atoms.push(Formula::gt(a.clone(), b.clone()));
            atoms.push(Formula::eq(a, b));
        }
    }

    atoms
}

// ── Candidate generation ──────────────────────────────────────────────────────

fn append_pairwise_conjunctions(out: &mut Vec<Formula>, atoms: &[&Formula]) {
    let mut count = 0;
    'outer: for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            if count >= MAX_CONJUNCTIONS {
                break 'outer;
            }
            out.push(Formula::and((*atoms[i]).clone(), (*atoms[j]).clone()));
            count += 1;
        }
    }
}

fn append_pairwise_disjunctions(out: &mut Vec<Formula>, atoms: &[&Formula]) {
    let mut count = 0;
    'outer: for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            if count >= MAX_PAIRWISE_DISJ {
                break 'outer;
            }
            out.push(Formula::or((*atoms[i]).clone(), (*atoms[j]).clone()));
            count += 1;
        }
    }
}

/// Generate `pos_atom || safety_atom` disjunctions guided by ICE examples.
///
/// `pos_atoms` are positive-consistent atoms (good inductive candidates).
/// `safety_atoms` are atoms that are false on at least one violation state.
/// The observer counter pattern is placed first: `counter <= select_index || safety`.
fn append_ice_disjunctions(
    out: &mut Vec<Formula>,
    pos_atoms: &[&Formula],
    safety_atoms: &[&Formula],
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
) {
    if safety_atoms.is_empty() || pos_atoms.is_empty() {
        return;
    }

    let counter = extract_back_edge_counter(info);
    let mut count = 0;

    // Observer pattern first: counter <= k || safety for each select index k.
    if let Some(ref ctr) = counter {
        for exit_edge in &info.exit_edges {
            let Ok(edge) = cfg.edge(*exit_edge) else {
                continue;
            };
            let Some(violation) = assertion_postconditions.get(&edge.target) else {
                continue;
            };
            for k in collect_select_indices_from_formula(violation) {
                for safe in safety_atoms {
                    if count >= MAX_ICE_DISJ {
                        return;
                    }
                    out.push(Formula::or(
                        Formula::le(Term::Var(ctr.clone()), k.clone()),
                        (*safe).clone(),
                    ));
                    count += 1;
                }
            }
        }
    }

    // General ICE disjunctions: pos_atom || safety_atom.
    'outer: for safe in safety_atoms {
        for pos in pos_atoms {
            if count >= MAX_ICE_DISJ {
                break 'outer;
            }
            out.push(Formula::or((*pos).clone(), (*safe).clone()));
            count += 1;
        }
    }
}

fn collect_select_indices_from_formula(formula: &Formula) -> Vec<Term> {
    let mut out = Vec::new();
    collect_idx_formula(formula, &mut out);
    out
}

fn collect_idx_formula(formula: &Formula, out: &mut Vec<Term>) {
    match formula {
        Formula::Lt(l, r)
        | Formula::Le(l, r)
        | Formula::Gt(l, r)
        | Formula::Ge(l, r)
        | Formula::Eq(l, r) => {
            collect_idx_term(l, out);
            collect_idx_term(r, out);
        }
        Formula::Not(inner) => collect_idx_formula(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_idx_formula(item, out);
            }
        }
        _ => {}
    }
}

fn collect_idx_term(term: &Term, out: &mut Vec<Term>) {
    match term {
        Term::Select(_, index) => out.push(*index.clone()),
        Term::Add(l, r) | Term::Sub(l, r) | Term::Mul(l, r) | Term::Div(l, r) | Term::Rem(l, r) => {
            collect_idx_term(l, out);
            collect_idx_term(r, out);
        }
        Term::Neg(inner) => collect_idx_term(inner, out),
        _ => {}
    }
}

/// Generate safety atoms by negating violation conjuncts precisely.
///
/// For each conjunct `c` in the violation formulas, `negate_comparison(c)` gives
/// the exact negation without introducing double `Not`s. These atoms are candidates
/// for the safety disjunct in `counter <= k || safety`.
fn violation_negation_atoms(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
) -> Vec<Formula> {
    let mut atoms = Vec::new();
    for exit_edge in &info.exit_edges {
        let Ok(edge) = cfg.edge(*exit_edge) else {
            continue;
        };
        let Some(violation) = assertion_postconditions.get(&edge.target) else {
            continue;
        };
        if *violation == Formula::False {
            continue;
        }
        for conjunct in formula_conjuncts(violation) {
            if let Some(negated) = negate_comparison(conjunct) {
                atoms.push(negated);
            }
        }
    }
    atoms
}

// ── Public entry point ────────────────────────────────────────────────────────

/// Generate loop invariant candidates using ICE-guided grammar enumeration.
///
/// Candidates are generated in priority order:
/// 1. Positive-consistent atoms: atoms not false at the initial loop state.
/// 2. Pairwise conjunctions of positive-consistent atoms.
/// 3. ICE-guided disjunctions: `pos_atom || safety_atom` where safety atoms
///    are false on at least one violation state.
/// 4. General pairwise disjunctions of positive-consistent atoms.
///
/// The `oracle` is used to collect concrete example states from the forward
/// reach (positive) and exit violations (negative).  If example collection
/// fails (formula infeasible or solver returns no model), all atoms are kept
/// and the generator falls back to unguided enumeration.
pub fn grammar_candidates(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
    oracle: &Oracle,
) -> Vec<Formula> {
    let vocab = collect_vocab(info, cfg, assertion_postconditions);
    if vocab.terms.is_empty() {
        return vec![];
    }
    let atoms = generate_atoms(&vocab);

    // Collect ICE examples to guide filtering.
    let positive = collect_positive_example(info, cfg, inner, oracle);
    let negatives = collect_negative_examples(info, cfg, assertion_postconditions, oracle);

    log::debug!(
        target: "loop_invariant",
        "achar: {} atoms; positive_example={} negative_examples={}",
        atoms.len(),
        positive.is_some(),
        negatives.len()
    );

    // Filter atoms by positive example.
    let pos_consistent: Vec<&Formula> = if let Some(ref pos) = positive {
        filter_positive_consistent(&atoms, pos)
    } else {
        atoms.iter().collect()
    };

    log::debug!(
        target: "loop_invariant",
        "achar: {} positive-consistent atoms (of {})",
        pos_consistent.len(), atoms.len()
    );

    // Find safety atoms using negative examples.
    let ice_safety: Vec<&Formula> = if !negatives.is_empty() {
        find_safety_atoms(&atoms, &negatives)
    } else {
        vec![]
    };

    // Also generate safety atoms from precise violation negation (no oracle needed).
    let negation_atoms = violation_negation_atoms(info, cfg, assertion_postconditions);
    let negation_refs: Vec<&Formula> = negation_atoms.iter().collect();

    // Merge safety sources (ICE + precise negation), dedup.
    let mut all_safety: Vec<&Formula> = ice_safety;
    for atom in &negation_refs {
        if !all_safety
            .iter()
            .any(|a| format!("{a:?}") == format!("{atom:?}"))
        {
            all_safety.push(atom);
        }
    }

    log::debug!(
        target: "loop_invariant",
        "achar: {} safety atoms", all_safety.len()
    );

    // Build candidate list in priority order.
    let mut candidates: Vec<Formula> = pos_consistent.iter().map(|a| (*a).clone()).collect();
    append_pairwise_conjunctions(&mut candidates, &pos_consistent);
    append_ice_disjunctions(
        &mut candidates,
        &pos_consistent,
        &all_safety,
        info,
        cfg,
        assertion_postconditions,
    );
    append_pairwise_disjunctions(&mut candidates, &pos_consistent);

    candidates
}
