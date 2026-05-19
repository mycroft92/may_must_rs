//! Grammar-based loop invariant synthesis with ICE (Inductive CounterExample) learning
//! and CEGIS feedback loop.
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
//!   at the loop header, from the forward reach, plus states from initiation failure
//!   witnesses collected during the CEGIS loop).
//! - **Negative examples** — states where the invariant *must not* hold (violation
//!   states at loop exits, from assertion postconditions, plus exit-closure failure
//!   witnesses collected during the CEGIS loop).
//! - **Implication counterexamples** — pre-states where the candidate held but the
//!   body broke inductiveness; absorbed as must-hold states.
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
//! # CEGIS feedback loop
//!
//! [`synthesize_with_cegis`] drives the check loop internally.  After each rejected
//! candidate, the [`InvariantCheckResult`] witness model (a concrete SMT state) is
//! absorbed into [`IceFeedback`].  Subsequent candidates are pre-screened against
//! accumulated states with cheap local evaluation via [`eval_atom`], skipping SMT
//! calls for candidates that are already inconsistent with observed examples.
//!
//! - `InitiationFailed` witness → must-hold state (candidate was false at loop entry).
//!   Future candidates must evaluate to `true` here or they also fail initiation.
//! - `InductivenessFailed` witness → must-hold state (pre-state where candidate held
//!   but body broke it).
//! - `ExitClosureFailed` witness → must-not-hold state (candidate was true here but
//!   violation still reachable).  Future candidates that evaluate to `true` here are
//!   likely to also fail exit closure.
//!
//! # Vocabulary filtering
//!
//! LLVM-internal variables (`__vla_expr*` VLA size tracking) are excluded from
//! the term vocabulary.  They never participate in assertion conditions and only
//! inflate the atom space.

use crate::common::abstract_cfg::{AbstractCfg, AssignValue, CfgNodeId, TransferEffect};
use crate::common::formula::{Formula, Memory, ModelValue, SmtModel, Sort, Term, Var};
use crate::common::oracle::{Feasibility, Oracle};
use crate::may_must_analysis::loops::{
    check_loop_invariant_verbose, extract_back_edge_counter, formula_conjuncts,
    forward_reach_at_header, negate_comparison, preheader_store_facts_at_header, InnerInvariants,
    InvariantCheckResult, LoopInfo,
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
                    // Try per-index value first.  model_bindings stores per-index
                    // values as scalars keyed "region[idx]" when different indices
                    // have different values in Z3's model.
                    if let Some(&v) = state.scalars.get(&format!("{name}[{idx_val}]")) {
                        return Some(v);
                    }
                    // Fall back to the ArrayDefault uniform background value.
                    state.arrays.get(name.as_str()).copied()
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

// ── Predicate atom collection ─────────────────────────────────────────────────

/// Collect atomic predicate atoms directly from the loop CFG structure.
///
/// Mines edge guards and `Assume` / `Assign { Predicate }` effects from every
/// node and edge in the loop body (including exit edges and the back edge).
/// Each collected atomic comparison and its precise negation are included.
///
/// These atoms are tried before the combinatorial vocabulary expansion because
/// they are the predicates the programmer explicitly wrote — they are the
/// natural building blocks for loop invariants.
fn collect_predicate_atoms(info: &LoopInfo, cfg: &AbstractCfg) -> Vec<Formula> {
    let mut raw: Vec<Formula> = Vec::new();

    // Edge guards: all edges with source in the loop body.
    for &node_id in &info.body {
        for edge_id in cfg.outgoing_edges(node_id) {
            if let Ok(edge) = cfg.edge(edge_id) {
                collect_atomic_comparisons(&edge.guard, &mut raw);
            }
        }
    }

    // Assume and Predicate-Assign effects in loop body nodes.
    for &node_id in &info.body {
        if let Ok(node) = cfg.node(node_id) {
            for effect in &node.transfer.effects {
                match effect {
                    TransferEffect::Assume(f) => collect_atomic_comparisons(f, &mut raw),
                    TransferEffect::Assign {
                        value: AssignValue::Predicate(f),
                        ..
                    } => collect_atomic_comparisons(f, &mut raw),
                    _ => {}
                }
            }
        }
    }

    // Add precise negations.
    let negated: Vec<Formula> = raw.iter().filter_map(negate_comparison).collect();
    raw.extend(negated);

    // Filter LLVM internals, deduplicate.
    raw.retain(|f| !formula_contains_vla_var(f));
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    raw.retain(|f| seen.insert(format!("{f:?}")));
    raw
}

/// Recursively extract atomic comparisons (Le/Lt/Ge/Gt/Eq) from a formula.
fn collect_atomic_comparisons(formula: &Formula, out: &mut Vec<Formula>) {
    match formula {
        Formula::Le(..) | Formula::Lt(..) | Formula::Ge(..) | Formula::Gt(..) | Formula::Eq(..) => {
            out.push(formula.clone());
        }
        Formula::Not(inner) => collect_atomic_comparisons(inner, out),
        Formula::And(parts) | Formula::Or(parts) => {
            for p in parts {
                collect_atomic_comparisons(p, out);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_atomic_comparisons(lhs, out);
            collect_atomic_comparisons(rhs, out);
        }
        _ => {}
    }
}

/// Returns true if any variable in the formula contains `__vla_expr`.
fn formula_contains_vla_var(formula: &Formula) -> bool {
    match formula {
        Formula::Le(a, b)
        | Formula::Lt(a, b)
        | Formula::Ge(a, b)
        | Formula::Gt(a, b)
        | Formula::Eq(a, b) => term_contains_vla_var(a) || term_contains_vla_var(b),
        Formula::Not(f) => formula_contains_vla_var(f),
        _ => false,
    }
}

fn term_contains_vla_var(term: &Term) -> bool {
    match term {
        Term::Var(v) => v.name().contains("__vla_expr"),
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            term_contains_vla_var(a) || term_contains_vla_var(b)
        }
        Term::Neg(a) => term_contains_vla_var(a),
        Term::Select(_, idx) => term_contains_vla_var(idx),
        _ => false,
    }
}

// ── CEGIS synthesis ───────────────────────────────────────────────────────────

/// Accumulated ICE counterexample states from rejected candidates.
///
/// Each failure of `check_loop_invariant_verbose` optionally provides a witness
/// model.  Collected witnesses are used to pre-screen subsequent candidates
/// with cheap local evaluation, avoiding redundant SMT calls.
struct IceFeedback {
    /// States where the invariant must hold (initial reachable states from
    /// `InitiationFailed` witnesses; pre-states from `InductivenessFailed` witnesses).
    /// A candidate that evaluates to `false` on any of these is pre-screened out.
    must_hold: Vec<IceState>,
    /// States where the invariant must not hold (from `ExitClosureFailed` witnesses).
    /// A candidate that evaluates to `true` on any of these is pre-screened out.
    must_not_hold: Vec<IceState>,
}

impl IceFeedback {
    fn new(initial_positive: Option<IceState>, initial_negatives: Vec<IceState>) -> Self {
        IceFeedback {
            must_hold: initial_positive.into_iter().collect(),
            must_not_hold: initial_negatives,
        }
    }

    /// Ingest a failure witness into the feedback state.
    fn absorb(&mut self, result: &InvariantCheckResult) {
        match result {
            InvariantCheckResult::InitiationFailed {
                witness: Some(model),
            } => {
                // Witness is a reachable initial state where the candidate was false.
                // Future candidates must evaluate to true here to pass initiation.
                self.must_hold.push(IceState::from_model(model));
            }
            InvariantCheckResult::InductivenessFailed {
                witness: Some(model),
            } => {
                // Witness is a pre-state where candidate held but was not preserved.
                // Future candidates must also handle these states (treat as must-hold).
                self.must_hold.push(IceState::from_model(model));
            }
            InvariantCheckResult::ExitClosureFailed {
                witness: Some(model),
                ..
            } => {
                // Witness satisfies `I ∧ exit_header`: the candidate was true here but
                // a violation was still reachable.  A good invariant should be false on
                // such states (or prevent the violation via exit closure).
                self.must_not_hold.push(IceState::from_model(model));
            }
            _ => {}
        }
    }

    /// Returns true if the candidate is already inconsistent with accumulated states,
    /// making an SMT call unnecessary.
    fn screens_out(&self, candidate: &Formula) -> bool {
        match candidate {
            // A disjunction A || B is false iff both A and B are false.
            // If both disjuncts evaluate to false on any must-hold state, the
            // whole candidate fails initiation there — screen it out.
            Formula::Or(parts) => {
                for state in &self.must_hold {
                    if parts.iter().all(|p| eval_atom(p, state) == Some(false)) {
                        return true;
                    }
                }
                false
            }
            // Atom / conjunction: standard check
            _ => {
                for state in &self.must_hold {
                    if eval_atom(candidate, state) == Some(false) {
                        return true;
                    }
                }
                for state in &self.must_not_hold {
                    if eval_atom(candidate, state) == Some(true) {
                        return true;
                    }
                }
                false
            }
        }
    }
}

/// Try a slice of candidates under the CEGIS loop.
///
/// For each candidate, checks the deadline, applies pre-screening, normalizes,
/// checks for tautology, runs the full invariant check, and absorbs the failure
/// witness.  Returns the normalized form of the first accepted candidate, or
/// `None` if all fail, synthesis times out, or the list is empty.
#[allow(clippy::too_many_arguments)]
fn run_tier(
    tier_name: &str,
    candidates: &[Formula],
    postconditions: &BTreeMap<CfgNodeId, Formula>,
    info: &LoopInfo,
    cfg: &AbstractCfg,
    oracle: &Oracle,
    inner: InnerInvariants<'_>,
    function: &str,
    loop_index: usize,
    feedback: &mut IceFeedback,
    screened_out: &mut usize,
    deadline: std::time::Instant,
) -> Option<Formula> {
    use crate::may_must_analysis::loops::normalize_candidate;
    for candidate in candidates {
        if std::time::Instant::now() >= deadline {
            log::debug!(
                target: "loop_invariant",
                "achar cegis: function {function} loop {loop_index} tier {tier_name}: timeout"
            );
            return None;
        }
        if feedback.screens_out(candidate) {
            *screened_out += 1;
            continue;
        }
        let normalized = normalize_candidate(cfg, info.header, candidate);
        if crate::may_must_analysis::backward::is_tautology(&normalized) {
            continue;
        }
        let result =
            check_loop_invariant_verbose(info, cfg, candidate, oracle, postconditions, inner);
        log::debug!(
            target: "loop_invariant",
            "achar cegis: function {function} loop {loop_index} [{tier_name}] {} => {}",
            crate::may_must_analysis::backward::pretty_formula(&normalized),
            match &result {
                InvariantCheckResult::Accepted => "accepted",
                InvariantCheckResult::InitiationFailed { .. } => "initiation failed",
                InvariantCheckResult::InductivenessFailed { .. } => "inductiveness failed",
                InvariantCheckResult::ExitClosureFailed { .. } => "exit closure failed",
            }
        );
        if result.is_accepted() {
            log::info!(
                target: "loop_invariant",
                "achar cegis: function {function} loop {loop_index} [{tier_name}]: \
                 accepted invariant: {}",
                crate::may_must_analysis::backward::pretty_formula(&normalized)
            );
            return Some(normalized);
        }
        feedback.absorb(&result);
    }
    None
}

/// ACHAR loop invariant synthesis with predicate-first atoms, ICE CEGIS feedback, and timeout.
///
/// Candidates are generated in tiered priority order and checked with the full
/// `check_loop_invariant_verbose` three-way test (initiation, inductiveness, optional
/// exit closure).  After each rejection the failure witness is absorbed into
/// [`IceFeedback`] so subsequent candidates can be pre-screened cheaply.
///
/// # Candidate tiers (tried in order)
///
/// **Tier 1 — predicate atoms**: atomic comparisons mined directly from the loop's
/// CFG edge guards and `Assume` / `Predicate-Assign` effects.  These are the
/// comparisons the programmer wrote; they are the most targeted candidates.
///
/// **Tier 2 — predicate conjunctions**: pairwise conjunctions of predicate atoms.
///
/// **Tier 3 — Phase-B predicate disjunctions**: `counter_init || predicate_atom`,
/// tried *without exit closure* (Phase-B pattern).  Handles invariants that require
/// the `counter == init` escape hatch because the property holds only after the first
/// iteration (e.g. cross-region relational invariants where an array element is
/// uninitialized at loop entry).
///
/// **Tier 4 — combinatorial atoms**: all pairwise comparisons over the loop's
/// vocabulary terms (scalars and `select` terms).  Filtered by positive-consistency
/// (atoms false at the initial ICE state are dropped).  Includes cross-region
/// relational comparisons like `menor <= select(array_region, j)`.
///
/// **Tier 5 — combinatorial conjunctions**: pairwise conjunctions of combinatorial
/// atoms (capped at [`MAX_CONJUNCTIONS`]).
///
/// **Tier 6 — ICE disjunctions**: `pos_atom || safety_atom` guided by negative ICE
/// examples (capped at [`MAX_ICE_DISJ`]).
///
/// **Tier 7 — Phase-B combinatorial disjunctions**: `counter_init || atom` for ALL
/// atoms (including those filtered by positive-consistency), without exit closure.
/// This is the tier that enables cross-region relational invariants such as
/// `(j == 0) || (menor <= array[0])` for programs like `array-2`.
///
/// **Tier 8 — pairwise combinatorial disjunctions**: fallback pairwise disjunctions
/// (capped at [`MAX_PAIRWISE_DISJ`]).
///
/// The loop stops as soon as any tier produces an accepted invariant or `timeout`
/// elapses.
pub fn synthesize_with_cegis(
    info: &LoopInfo,
    cfg: &AbstractCfg,
    assertion_postconditions: &BTreeMap<CfgNodeId, Formula>,
    inner: InnerInvariants<'_>,
    oracle: &Oracle,
    function: &str,
    loop_index: usize,
    timeout: std::time::Duration,
) -> Option<Formula> {
    let deadline = std::time::Instant::now() + timeout;
    let empty_pc: BTreeMap<CfgNodeId, Formula> = BTreeMap::new();

    // ── Atom pools ────────────────────────────────────────────────────────────
    let pred_atoms = collect_predicate_atoms(info, cfg);
    let vocab = collect_vocab(info, cfg, assertion_postconditions);
    let combo_atoms = if vocab.terms.is_empty() {
        vec![]
    } else {
        generate_atoms(&vocab)
    };

    // ── ICE examples ──────────────────────────────────────────────────────────
    let initial_positive = collect_positive_example(info, cfg, inner, oracle);
    let initial_negatives = collect_negative_examples(info, cfg, assertion_postconditions, oracle);

    log::debug!(
        target: "loop_invariant",
        "achar cegis: function {function} loop {loop_index}: \
         pred_atoms={} combo_atoms={} positive={} negatives={}",
        pred_atoms.len(),
        combo_atoms.len(),
        initial_positive.is_some(),
        initial_negatives.len()
    );

    // ── Filter combo atoms by positive-consistency ────────────────────────────
    let pos_consistent: Vec<Formula> = if let Some(ref pos) = initial_positive {
        filter_positive_consistent(&combo_atoms, pos)
            .into_iter()
            .cloned()
            .collect()
    } else {
        combo_atoms.clone()
    };

    // ── Safety atoms for ICE disjunctions ─────────────────────────────────────
    let ice_safety_refs: Vec<&Formula> = if !initial_negatives.is_empty() {
        find_safety_atoms(&combo_atoms, &initial_negatives)
    } else {
        vec![]
    };
    let negation_atoms = violation_negation_atoms(info, cfg, assertion_postconditions);
    let mut all_safety: Vec<Formula> = ice_safety_refs.into_iter().cloned().collect();
    for atom in &negation_atoms {
        if !all_safety
            .iter()
            .any(|a| format!("{a:?}") == format!("{atom:?}"))
        {
            all_safety.push(atom.clone());
        }
    }
    let all_safety_refs: Vec<&Formula> = all_safety.iter().collect();

    // ── Counter-init equations for Phase-B tiers ──────────────────────────────
    let store_facts = preheader_store_facts_at_header(cfg, info.header, inner);
    let counter_inits: Vec<Formula> = store_facts
        .iter()
        .filter(|((_, offset), value)| *offset == 0 && matches!(value, Term::Int(_)))
        .map(|((region, offset), value)| {
            Formula::eq(
                Term::select(Memory::var(region.clone()), Term::int(*offset)),
                value.clone(),
            )
        })
        .collect();

    // ── CEGIS feedback state ──────────────────────────────────────────────────
    let mut feedback = IceFeedback::new(initial_positive, initial_negatives);
    let mut screened_out = 0usize;

    macro_rules! tier {
        ($name:expr, $cands:expr, $pc:expr) => {
            if let Some(inv) = run_tier(
                $name,
                &$cands,
                $pc,
                info,
                cfg,
                oracle,
                inner,
                function,
                loop_index,
                &mut feedback,
                &mut screened_out,
                deadline,
            ) {
                log::debug!(
                    target: "loop_invariant",
                    "achar cegis: function {function} loop {loop_index}: \
                     screened_out={screened_out}"
                );
                return Some(inv);
            }
            if std::time::Instant::now() >= deadline {
                log::debug!(
                    target: "loop_invariant",
                    "achar cegis: function {function} loop {loop_index}: timeout after tier {}",
                    $name
                );
                return None;
            }
        };
    }

    // Tier 1: predicate atoms from code (no positive-consistency filtering)
    tier!("pred-atoms", pred_atoms.clone(), assertion_postconditions);

    // Tier 2: pairwise conjunctions of predicate atoms
    {
        let pred_refs: Vec<&Formula> = pred_atoms.iter().collect();
        let mut conj = Vec::new();
        append_pairwise_conjunctions(&mut conj, &pred_refs);
        tier!("pred-conj", conj, assertion_postconditions);
    }

    // Tier 3: Phase-B predicate disjunctions: (counter_init) || pred_atom.
    // Only active in the pre-pass (no assertion site). When assertion_postconditions
    // is non-empty, exit closure is required and these candidates are not sound
    // without it — run_backward does not substitute for exit closure.
    if !counter_inits.is_empty() && assertion_postconditions.is_empty() {
        let mut phase_b_pred: Vec<Formula> = Vec::new();
        for ci in &counter_inits {
            for atom in &pred_atoms {
                phase_b_pred.push(Formula::or(ci.clone(), atom.clone()));
            }
        }
        tier!("phase-b-pred", phase_b_pred, &empty_pc);
    }

    // Tier 4: positive-consistent combinatorial atoms
    tier!(
        "combo-atoms",
        pos_consistent.clone(),
        assertion_postconditions
    );

    // Tier 5: pairwise conjunctions of combinatorial atoms
    {
        let pos_refs: Vec<&Formula> = pos_consistent.iter().collect();
        let mut conj = Vec::new();
        append_pairwise_conjunctions(&mut conj, &pos_refs);
        tier!("combo-conj", conj, assertion_postconditions);
    }

    // Tier 6: ICE-guided disjunctions
    {
        let pos_refs: Vec<&Formula> = pos_consistent.iter().collect();
        let mut disj = Vec::new();
        append_ice_disjunctions(
            &mut disj,
            &pos_refs,
            &all_safety_refs,
            info,
            cfg,
            assertion_postconditions,
        );
        tier!("ice-disj", disj, assertion_postconditions);
    }

    // Tier 7: Phase-B combinatorial disjunctions: (counter_init) || atom.
    // Includes ALL combo atoms (not just pos-consistent) to reach cross-region
    // relational invariants. Only active in the pre-pass for the same reason
    // as Tier 3: exit closure is required during assertion verification.
    if !counter_inits.is_empty() && assertion_postconditions.is_empty() {
        let mut phase_b_combo: Vec<Formula> = Vec::new();
        for ci in &counter_inits {
            for atom in &combo_atoms {
                phase_b_combo.push(Formula::or(ci.clone(), atom.clone()));
            }
        }
        tier!("phase-b-combo", phase_b_combo, &empty_pc);
    }

    // Tier 8: pairwise disjunctions of combinatorial atoms (fallback)
    {
        let pos_refs: Vec<&Formula> = pos_consistent.iter().collect();
        let mut disj = Vec::new();
        append_pairwise_disjunctions(&mut disj, &pos_refs);
        tier!("combo-disj", disj, assertion_postconditions);
    }

    log::debug!(
        target: "loop_invariant",
        "achar cegis: function {function} loop {loop_index}: \
         no invariant found (screened_out={screened_out}/{})",
        pred_atoms.len() + combo_atoms.len()
    );
    None
}
