//! Grammar-based loop invariant synthesis (ACHAR approach).
//!
//! Generates candidates by enumerating a bounded grammar over the loop's
//! variable and memory vocabulary, returning them for the caller to validate
//! with `check_loop_invariant_verbose`.
//!
//! The approach follows "Almost Correct Invariants" (ISSTA '22, Lahiri & Roy):
//! enumerate candidates from a grammar G; use an SMT oracle as the teacher
//! instead of fuzzing. This module is the Learner side — it produces
//! candidates in priority order (atoms before conjunctions before disjunctions).
//!
//! # Observer subsumption
//!
//! Observer-style candidates (`counter <= k || NOT(violation_conjunct)`) are
//! generated here as a disjunction layer: for every exit-edge violation conjunct
//! `C`, each atom `A` yields `A || NOT(C)`.  Since the counter and select indices
//! are already in the atom vocabulary, the observer pattern is a strict subset of
//! what this layer produces.
//!
//! This module is intentionally independent of the entry-safety synthesis pass
//! in `loops.rs` — the two passes do not share candidate infrastructure.

use crate::common::abstract_cfg::{AbstractCfg, AssignValue, CfgNodeId, TransferEffect};
use crate::common::formula::{Formula, Sort, Term, Var};
use crate::may_must_analysis::loops::{
    extract_back_edge_counter, formula_conjuncts, negate_comparison, InnerInvariants, LoopInfo,
};
use std::collections::{BTreeMap, BTreeSet};

/// Cap on pairwise conjunctions, general pairwise disjunctions, and observer disjunctions.
const MAX_CONJUNCTIONS: usize = 60;
const MAX_PAIRWISE_DISJ: usize = 60;
const MAX_DISJUNCTIONS: usize = 60;

/// Generate loop invariant candidates using a grammar over the loop vocabulary.
///
/// Candidates are returned in priority order:
/// 1. Atoms: `lhs op rhs` over loop variables, select terms, and constants.
/// 2. Pairwise conjunctions of atoms (capped at [`MAX_CONJUNCTIONS`]).
/// 3. Pairwise disjunctions of atoms (capped at [`MAX_PAIRWISE_DISJ`]).
/// 4. Observer-style disjunctions: `atom || NOT(violation_conjunct)` for each
///    exit-edge violation conjunct (capped at [`MAX_DISJUNCTIONS`]).
pub fn grammar_candidates(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    _inner: InnerInvariants<'_>,
) -> Vec<Formula> {
    let vocab = collect_vocab(info, cfg, assertion_postconditions);
    if vocab.terms.is_empty() {
        return vec![];
    }
    let atoms = generate_atoms(&vocab);
    let mut candidates = atoms.clone();
    append_pairwise_conjunctions(&mut candidates, &atoms);
    append_pairwise_disjunctions(&mut candidates, &atoms);
    append_observer_disjunctions(&mut candidates, &atoms, info, cfg, assertion_postconditions);
    candidates
}

// ── Vocabulary ────────────────────────────────────────────────────────────────

struct Vocab {
    /// Integer-sorted terms: loop variables and `select(region, idx)` reads from
    /// both the loop body and the exit-edge violation postconditions.
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

    // Also collect select terms from exit violation postconditions.
    for formula in assertion_postconditions.values() {
        collect_select_terms(formula, &mut selects);
    }
    dedup_terms(&mut selects);

    let mut terms: Vec<Term> = vars.into_iter().map(Term::Var).collect();
    terms.extend(selects);

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
        // Collect the full select term into vocabulary (array read as a term).
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
    // Selects from guards are not added to vocabulary — only those from body effects
    // and postconditions are. We still recurse to pick up variables and constants.
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

/// Collect `select(region, idx)` sub-terms from a formula into `out`.
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

    // term op term (all ordered pairs; skip structurally identical pairs).
    let n = vocab.terms.len();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let a = &vocab.terms[i];
            let b = &vocab.terms[j];
            // Skip trivially-true atoms (a <= a, a >= a, a == a).
            if format!("{a:?}") == format!("{b:?}") {
                continue;
            }
            atoms.push(Formula::le(a.clone(), b.clone()));
            atoms.push(Formula::lt(a.clone(), b.clone()));
            atoms.push(Formula::eq(a.clone(), b.clone()));
        }
    }

    // term op constant (both directions for inequalities).
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

// ── Conjunction layer ─────────────────────────────────────────────────────────

fn append_pairwise_conjunctions(out: &mut Vec<Formula>, atoms: &[Formula]) {
    let mut count = 0;
    'outer: for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            if count >= MAX_CONJUNCTIONS {
                break 'outer;
            }
            out.push(Formula::and(atoms[i].clone(), atoms[j].clone()));
            count += 1;
        }
    }
}

// ── General pairwise disjunction layer ───────────────────────────────────────

fn append_pairwise_disjunctions(out: &mut Vec<Formula>, atoms: &[Formula]) {
    let mut count = 0;
    'outer: for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            if count >= MAX_PAIRWISE_DISJ {
                break 'outer;
            }
            out.push(Formula::or(atoms[i].clone(), atoms[j].clone()));
            count += 1;
        }
    }
}

// ── Observer-style disjunction layer ─────────────────────────────────────────

/// Generate `atom || NOT(conjunct)` candidates for each exit-edge violation conjunct.
///
/// This subsumes the observer phase: when `atom` = `counter <= k` and `conjunct`
/// is the array-comparison from the violation, the result is the same pattern
/// that the observer-disjunction generator produces.  The counter and index
/// terms are already in the atom vocabulary so no extra work is needed.
fn append_observer_disjunctions(
    out: &mut Vec<Formula>,
    atoms: &[Formula],
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
) {
    // Collect violation conjuncts from exit edges, same as observer does.
    let mut conjuncts: Vec<Formula> = Vec::new();
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
        for c in formula_conjuncts(violation) {
            conjuncts.push(c.clone());
        }
    }
    if conjuncts.is_empty() {
        return;
    }

    // For each conjunct C, emit NOT(C) alone and then atom || NOT(C).
    let counter = extract_back_edge_counter(info);
    let mut count = 0;
    'outer: for conjunct in &conjuncts {
        let negated = negate_comparison(conjunct).unwrap_or_else(|| Formula::not(conjunct.clone()));
        out.push(negated.clone());
        // Observer's exact pattern first: counter <= k || NOT(C) for each select index k.
        if let Some(ref ctr) = counter {
            for k in collect_select_indices(conjunct) {
                if count >= MAX_DISJUNCTIONS {
                    break 'outer;
                }
                out.push(Formula::or(
                    Formula::le(Term::Var(ctr.clone()), k),
                    negated.clone(),
                ));
                count += 1;
            }
        }
        // Generalisation: any atom || NOT(C).
        for atom in atoms {
            if count >= MAX_DISJUNCTIONS {
                break 'outer;
            }
            out.push(Formula::or(atom.clone(), negated.clone()));
            count += 1;
        }
    }
}

fn collect_select_indices(formula: &Formula) -> Vec<Term> {
    let mut out = Vec::new();
    collect_select_indices_in_formula(formula, &mut out);
    out
}

fn collect_select_indices_in_formula(formula: &Formula, out: &mut Vec<Term>) {
    match formula {
        Formula::Lt(l, r)
        | Formula::Le(l, r)
        | Formula::Gt(l, r)
        | Formula::Ge(l, r)
        | Formula::Eq(l, r) => {
            collect_select_idx_in_term(l, out);
            collect_select_idx_in_term(r, out);
        }
        Formula::Not(inner) => collect_select_indices_in_formula(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_select_indices_in_formula(item, out);
            }
        }
        _ => {}
    }
}

fn collect_select_idx_in_term(term: &Term, out: &mut Vec<Term>) {
    match term {
        Term::Select(_, index) => out.push(*index.clone()),
        Term::Add(l, r) | Term::Sub(l, r) | Term::Mul(l, r) | Term::Div(l, r) | Term::Rem(l, r) => {
            collect_select_idx_in_term(l, out);
            collect_select_idx_in_term(r, out);
        }
        Term::Neg(inner) => collect_select_idx_in_term(inner, out),
        _ => {}
    }
}
