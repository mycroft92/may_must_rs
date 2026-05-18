//! Grammar-based loop invariant synthesis (ACHAR approach).
//!
//! Generates candidates by enumerating a bounded grammar over the loop's
//! variable and memory vocabulary, returning them for the caller to validate
//! with `check_loop_invariant_verbose`.
//!
//! The approach follows "Almost Correct Invariants" (ISSTA '22, Lahiri & Roy):
//! enumerate candidates from a grammar G; use an SMT oracle as the teacher
//! instead of fuzzing. This module is the Learner side — it produces
//! candidates in priority order (atoms before conjunctions).
//!
//! This module is intentionally independent of the entry-safety synthesis pass
//! in `loops.rs` — the two passes do not share candidate infrastructure.

use crate::common::abstract_cfg::{AbstractCfg, AssignValue, CfgNodeId, TransferEffect};
use crate::common::formula::{Formula, Sort, Term, Var};
use crate::may_must_analysis::loops::{InnerInvariants, LoopInfo};
use std::collections::{BTreeMap, BTreeSet};

/// Cap on pairwise conjunctions to avoid combinatorial blowup.
const MAX_CONJUNCTIONS: usize = 60;

/// Generate loop invariant candidates using a grammar over the loop vocabulary.
///
/// Candidates are returned in priority order: atoms first, then pairwise
/// conjunctions of atoms. The caller validates each with
/// `check_loop_invariant_verbose`.
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
    candidates
}

// ── Vocabulary ────────────────────────────────────────────────────────────────

struct Vocab {
    /// Integer-sorted terms: loop variables and `select(region, idx)` reads
    /// extracted from exit postconditions.
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

    for node_id in &info.body {
        let Ok(node) = cfg.node(*node_id) else {
            continue;
        };
        for effect in &node.transfer.effects {
            collect_effect_vocab(effect, &mut vars, &mut consts);
        }
    }
    collect_formula_vocab(&info.back_edge_guard, &mut vars, &mut consts);

    let mut select_terms: Vec<Term> = Vec::new();
    for formula in assertion_postconditions.values() {
        collect_select_terms(formula, &mut select_terms);
    }
    dedup_terms(&mut select_terms);

    let mut terms: Vec<Term> = vars.into_iter().map(Term::Var).collect();
    terms.extend(select_terms);

    Vocab {
        terms,
        constants: consts.into_iter().collect(),
    }
}

fn collect_effect_vocab(
    effect: &TransferEffect,
    vars: &mut BTreeSet<Var>,
    consts: &mut BTreeSet<i64>,
) {
    match effect {
        TransferEffect::Assign { target, value } => {
            if target.sort() == Sort::Int {
                vars.insert(target.clone());
            }
            match value {
                AssignValue::Term(t) => collect_term_vocab(t, vars, consts),
                AssignValue::Predicate(f) => collect_formula_vocab(f, vars, consts),
            }
        }
        TransferEffect::MemoryStore { value, .. } => {
            collect_term_vocab(value, vars, consts);
        }
        _ => {}
    }
}

fn collect_term_vocab(term: &Term, vars: &mut BTreeSet<Var>, consts: &mut BTreeSet<i64>) {
    match term {
        Term::Var(v) if v.sort() == Sort::Int => {
            vars.insert(v.clone());
        }
        Term::Int(n) => {
            consts.insert(*n);
        }
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b)
        | Term::Rem(a, b) => {
            collect_term_vocab(a, vars, consts);
            collect_term_vocab(b, vars, consts);
        }
        Term::Neg(a) => collect_term_vocab(a, vars, consts),
        Term::Select(_, idx) => collect_term_vocab(idx, vars, consts),
        _ => {}
    }
}

fn collect_formula_vocab(formula: &Formula, vars: &mut BTreeSet<Var>, consts: &mut BTreeSet<i64>) {
    match formula {
        Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Eq(a, b)
        | Formula::Ge(a, b)
        | Formula::Gt(a, b) => {
            collect_term_vocab(a, vars, consts);
            collect_term_vocab(b, vars, consts);
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
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b)
        | Term::Rem(a, b) => {
            collect_select_in_term(a, out);
            collect_select_in_term(b, out);
        }
        Term::Neg(a) => collect_select_in_term(a, out),
        _ => {}
    }
}

fn dedup_terms(terms: &mut Vec<Term>) {
    // Use Debug representation as a stable dedup key — Term doesn't impl Hash/Ord.
    let mut seen: BTreeSet<String> = BTreeSet::new();
    terms.retain(|t| seen.insert(format!("{t:?}")));
}

// ── Atom generation ───────────────────────────────────────────────────────────

fn generate_atoms(vocab: &Vocab) -> Vec<Formula> {
    let mut atoms = Vec::new();

    // term op term (all ordered pairs, omitting i==j).
    let n = vocab.terms.len();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let a = vocab.terms[i].clone();
            let b = vocab.terms[j].clone();
            atoms.push(Formula::le(a.clone(), b.clone()));
            atoms.push(Formula::lt(a.clone(), b.clone()));
            atoms.push(Formula::eq(a, b));
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
