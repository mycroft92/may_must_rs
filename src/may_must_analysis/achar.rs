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
//! Candidates are generated in tiered priority order (see [`synthesize_with_cegis`]).
//!
//! The search stops as soon as any candidate passes all three checks (initiation,
//! inductiveness, exit closure) or the per-loop timeout elapses.  No fixed caps
//! are applied to tier sizes — the timeout bounds the total budget.
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

// ── ICE example types ─────────────────────────────────────────────────────────

/// A concrete program state extracted from an SMT model.
///
/// Scalar values are keyed by variable name. Array regions are stored as a
/// default value (the `ArrayDefault` constant Z3 assigns to unconstrained arrays).
#[derive(Clone, Debug, Default)]
pub(crate) struct IceState {
    pub scalars: HashMap<String, i64>,
}

impl IceState {
    fn from_model(model: &SmtModel) -> Self {
        let mut scalars = HashMap::new();
        for (var, value) in &model.scalar {
            if let ModelValue::Int(n) = value {
                scalars.insert(var.name().to_string(), *n);
            }
            if let ModelValue::Bool(b) = value {
                scalars.insert(var.name().to_string(), if *b { 1 } else { 0 });
            }
        }
        // Memory bindings are intentionally ignored.  Z3 represents an array
        // model as `(store (const v) idx_1 v_1) ...` but `ModelValue::ArrayDefault`
        // captures only the outer constant, dropping the per-index store updates.
        // Using the default for `select(region, idx)` would mis-evaluate at any
        // index that was explicitly stored — see `eval_term` for the contract.
        IceState { scalars }
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
                    // Only return a value if the SMT model has an explicit
                    // per-index binding (key `region[idx]`).  We do NOT fall back
                    // to a uniform ArrayDefault because Z3 represents an array
                    // model as `(store (const d) i v) ...` where the per-index
                    // store overrides the default — but `ModelValue::ArrayDefault`
                    // captures only the outer constant.  Returning the default
                    // would let screening reject candidates whose actual select
                    // value at this index differs from the default (see array-1's
                    // `select(SIZE_region, 0) = 1` vs `ArrayDefault(-1)`).
                    state.scalars.get(&format!("{name}[{idx_val}]")).copied()
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
            // Only collect simple select(Var, idx) terms; skip store-expression
            // memory operands (select(store(...),...)) that arise in WP formulas —
            // they inflate the vocabulary without contributing useful atoms.
            if matches!(arr.as_ref(), crate::common::formula::Memory::Var(_)) {
                selects.push(Term::Select(arr.clone(), idx.clone()));
            }
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
            if matches!(arr.as_ref(), crate::common::formula::Memory::Var(_)) {
                out.push(Term::Select(arr.clone(), idx.clone()));
            }
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
    for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            out.push(Formula::and((*atoms[i]).clone(), (*atoms[j]).clone()));
        }
    }
}

fn append_pairwise_disjunctions(out: &mut Vec<Formula>, atoms: &[&Formula]) {
    for i in 0..atoms.len() {
        for j in (i + 1)..atoms.len() {
            out.push(Formula::or((*atoms[i]).clone(), (*atoms[j]).clone()));
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
                    out.push(Formula::or(
                        Formula::le(Term::Var(ctr.clone()), k.clone()),
                        (*safe).clone(),
                    ));
                }
            }
        }
    }

    // General ICE disjunctions: pos_atom || safety_atom.
    for safe in safety_atoms {
        for pos in pos_atoms {
            out.push(Formula::or((*pos).clone(), (*safe).clone()));
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

    // Substitute SSA-local variables defined inside the loop body with their
    // right-hand sides (Term::Assign effects).  This rewrites atoms like
    // `(main$%13 < main$%14)` (raw load names) into `(select stack2 0 < select
    // stack1 0)` so they are meaningful at the loop header.  Without this,
    // disjunctions like `(j < SIZE) || (array[0] >= menor)` go to the SMT solver
    // with free `%14` operands that can take any value, defeating exit closure.
    let subst = build_body_var_subst(info, cfg);
    if !subst.is_empty() {
        for atom in raw.iter_mut() {
            *atom = substitute_formula_vars_to_terms(atom, &subst);
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

/// Build a substitution map (Var name → Term) from all `Assign { value: Term(t) }`
/// effects in the loop body.  Resolves chained assignments to a fixpoint so that
/// e.g. `%15 → %13 → select(stack, 0)` collapses to `%15 → select(stack, 0)`.
fn build_body_var_subst(
    info: &LoopInfo,
    cfg: &AbstractCfg,
) -> std::collections::BTreeMap<String, Term> {
    let mut subst: std::collections::BTreeMap<String, Term> = std::collections::BTreeMap::new();
    for &node_id in &info.body {
        if let Ok(node) = cfg.node(node_id) {
            for effect in &node.transfer.effects {
                if let TransferEffect::Assign {
                    target,
                    value: AssignValue::Term(t),
                } = effect
                {
                    subst.insert(target.name().to_string(), t.clone());
                }
            }
        }
    }
    // Resolve chains: iterate until no entry rewrites further.
    for _ in 0..8 {
        let snapshot = subst.clone();
        let mut changed = false;
        for (_, value) in subst.iter_mut() {
            let new_value = substitute_term_vars_to_terms(value, &snapshot);
            if format!("{new_value:?}") != format!("{value:?}") {
                *value = new_value;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    subst
}

/// Substitute `Var(name)` → `Term` in a formula, applied recursively.
fn substitute_formula_vars_to_terms(
    formula: &Formula,
    subst: &std::collections::BTreeMap<String, Term>,
) -> Formula {
    let st = |t: &Term| substitute_term_vars_to_terms(t, subst);
    let sf = |f: &Formula| substitute_formula_vars_to_terms(f, subst);
    match formula {
        Formula::True | Formula::False => formula.clone(),
        Formula::Le(a, b) => Formula::le(st(a), st(b)),
        Formula::Lt(a, b) => Formula::lt(st(a), st(b)),
        Formula::Ge(a, b) => Formula::ge(st(a), st(b)),
        Formula::Gt(a, b) => Formula::gt(st(a), st(b)),
        Formula::Eq(a, b) => Formula::eq(st(a), st(b)),
        Formula::Not(inner) => Formula::not(sf(inner)),
        Formula::And(parts) => Formula::and_all(parts.iter().map(sf).collect::<Vec<_>>()),
        Formula::Or(parts) => Formula::or_all(parts.iter().map(sf).collect::<Vec<_>>()),
        Formula::Implies(lhs, rhs) => Formula::implies(sf(lhs), sf(rhs)),
        Formula::Var(_) | Formula::MemoryEq(_, _) => formula.clone(),
    }
}

fn substitute_term_vars_to_terms(
    term: &Term,
    subst: &std::collections::BTreeMap<String, Term>,
) -> Term {
    match term {
        Term::Var(v) => subst.get(v.name()).cloned().unwrap_or_else(|| term.clone()),
        Term::Int(_) | Term::Real(_) => term.clone(),
        Term::BoolToInt(inner) => Term::bool_to_int(substitute_formula_vars_to_terms(inner, subst)),
        Term::Select(memory, idx) => Term::select(
            (**memory).clone(),
            substitute_term_vars_to_terms(idx, subst),
        ),
        Term::Add(a, b) => Term::add(
            substitute_term_vars_to_terms(a, subst),
            substitute_term_vars_to_terms(b, subst),
        ),
        Term::Sub(a, b) => Term::sub(
            substitute_term_vars_to_terms(a, subst),
            substitute_term_vars_to_terms(b, subst),
        ),
        Term::Mul(a, b) => Term::mul(
            substitute_term_vars_to_terms(a, subst),
            substitute_term_vars_to_terms(b, subst),
        ),
        Term::Div(a, b) => Term::div(
            substitute_term_vars_to_terms(a, subst),
            substitute_term_vars_to_terms(b, subst),
        ),
        Term::Rem(a, b) => Term::rem(
            substitute_term_vars_to_terms(a, subst),
            substitute_term_vars_to_terms(b, subst),
        ),
        Term::Neg(inner) => Term::neg(substitute_term_vars_to_terms(inner, subst)),
    }
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
/// `check_loop_invariant_verbose` three-way test (initiation, inductiveness, exit
/// closure).  After each rejection the failure witness is absorbed into
/// [`IceFeedback`] so subsequent candidates can be pre-screened cheaply.
///
/// The grammar is unconstrained — no fixed per-tier caps.  The per-loop `timeout`
/// is the only budget limit.
///
/// # Candidate tiers (tried in order)
///
/// Assertion-derived tiers come FIRST: the safety property the user wrote is
/// the most direct candidate for the loop invariant.  Tiers 1–3 are bounded by
/// `|atoms|` (typically ≤ 10), so they finish in milliseconds before any
/// expensive combinatorial search.
///
/// **Tier 1 — assertion-derived atoms**: exact negations of the violation formula
/// conjuncts.  Encodes the safety property the assertion expresses.  For an
/// assertion `a >= b`, this tries `a >= b` as the invariant directly.
///
/// **Tier 2 — counter-init assertion disjunctions**: `counter_init || negation_atom`.
/// The simplest counter-escape shape.  Works when the loop is guaranteed to
/// execute at least once.  When the loop bound may be zero, exit closure
/// correctly rejects this shape (the loop body never ran, so the assertion
/// property isn't established) — Tier 3 handles that case.
///
/// **Tier 3 — predicate-atom assertion disjunctions**: `pred_atom || negation_atom`.
/// The critical shape for programs like `array-1` where the loop bound may
/// vacuously be zero.  Pairs the loop continuation guard `j < SIZE` (mined as
/// a predicate atom from CFG edge guards) with the safety condition:
/// `(j < SIZE) || (array[0] >= menor)`.  Exit closure passes because
/// `j < SIZE` at exit is false, forcing the safety atom to hold.
///
/// **Tier 4 — predicate atoms**: atomic comparisons mined directly from the
/// loop's CFG edge guards and `Assume` / `Predicate-Assign` effects.
///
/// **Tier 5 — predicate conjunctions**: pairwise conjunctions of predicate atoms.
///
/// **Tier 6 — counter-init predicate disjunctions**: `counter_init || pred_atom`
/// with full exit closure.
///
/// **Tier 7 — counter-init combinatorial disjunctions**: `counter_init || combo_atom`
/// with full exit closure.  Finds cross-region relational invariants that aren't
/// reachable via the exact assertion negation atoms.
///
/// **Tier 8 — combinatorial atoms**: all pairwise comparisons over the loop's
/// vocabulary terms (scalars and `select(Var, idx)` reads).  Filtered by
/// positive-consistency.
///
/// **Tier 9 — combinatorial conjunctions**: pairwise conjunctions of combinatorial
/// atoms.
///
/// **Tier 10 — ICE disjunctions**: `pos_atom || safety_atom` guided by negative ICE
/// examples.
///
/// **Tier 11 — pairwise combinatorial disjunctions**: fallback.
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

    // ── Immutable preheader facts ─────────────────────────────────────────────
    // A subset of counter_inits whose region is never written in the loop body.
    // These facts are inductive (the body cannot change them), so we may safely
    // conjoin them with any candidate to gain the SMT solver more information
    // at the exit-closure check.  Example for `array-1`: the preheader stores
    // `SIZE = 1` to a region that the body never touches; conjoining
    // `(SIZE == 1)` makes `(j == 0) || (array[0] >= menor)` discharge exit
    // closure (the SAT case `j=0, SIZE=0` is ruled out by `SIZE == 1`).
    let body_written_regions: std::collections::BTreeSet<String> = info
        .body
        .iter()
        .flat_map(|&node_id| cfg.node(node_id).into_iter())
        .flat_map(|node| node.transfer.effects.iter())
        .filter_map(|e| match e {
            TransferEffect::MemoryStore { region, .. } => Some(region.clone()),
            TransferEffect::HavocRegions { regions } => regions.iter().cloned().next(),
            _ => None,
        })
        .collect();
    let immutable_inits: Vec<Formula> = store_facts
        .iter()
        .filter(|((region, offset), value)| {
            *offset == 0 && matches!(value, Term::Int(_)) && !body_written_regions.contains(region)
        })
        .map(|((region, offset), value)| {
            Formula::eq(
                Term::select(Memory::var(region.clone()), Term::int(*offset)),
                value.clone(),
            )
        })
        .collect();
    let immutable_conj: Option<Formula> = if immutable_inits.is_empty() {
        None
    } else {
        Some(Formula::and_all(immutable_inits.clone()))
    };

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

    // Tier 1: assertion-derived atoms (exact negations of violation conjuncts).
    // The most direct candidate for the invariant: the safety property the
    // assertion itself expresses.  For an assertion `a >= b`, this tries
    // `a >= b` as the invariant.  When the property holds at the loop header
    // (e.g. `i <= n`-style monotone properties), this single-candidate tier
    // discharges the assertion in O(1) candidates.
    if !negation_atoms.is_empty() {
        tier!(
            "assert-atoms",
            negation_atoms.clone(),
            assertion_postconditions
        );
    }

    // Tier 2: counter-init assertion disjunctions: (counter_init) || negation_atom.
    // The simplest counter-escape shape.  Works when the loop is guaranteed to
    // execute at least once (so j==0 at exit is impossible).  When the loop
    // bound may be zero (e.g. SIZE=0), exit closure correctly rejects this
    // shape because `j==0 ∧ j>=SIZE` is feasible with SIZE=0 — the loop body
    // never ran, so the assertion property isn't established.  Tier 3 handles
    // that case with the loop continuation guard.
    if !counter_inits.is_empty() && !negation_atoms.is_empty() {
        let mut counter_assert_disj: Vec<Formula> = Vec::new();
        for ci in &counter_inits {
            for atom in &negation_atoms {
                counter_assert_disj.push(Formula::or(ci.clone(), atom.clone()));
            }
        }
        tier!(
            "counter-assert-disj",
            counter_assert_disj,
            assertion_postconditions
        );
    }

    // Tier 2b: counter-assert-disj strengthened with immutable preheader facts.
    // Conjoins `counter_init || negation_atom` with all preheader facts whose
    // region is never written in the loop body.  This is needed for programs
    // where the assertion's safety depends on a preheader fact that the
    // verifier's exit-closure check cannot see by itself (e.g. `array-1`'s
    // `SIZE = 1` rules out the spurious `SIZE = 0 ∧ j = 0` model).
    if !counter_inits.is_empty() && !negation_atoms.is_empty() {
        if let Some(ref imm) = immutable_conj {
            let mut counter_assert_disj_imm: Vec<Formula> = Vec::new();
            for ci in &counter_inits {
                for atom in &negation_atoms {
                    let disj = Formula::or(ci.clone(), atom.clone());
                    counter_assert_disj_imm.push(Formula::and(disj, imm.clone()));
                }
            }
            tier!(
                "counter-assert-disj+imm",
                counter_assert_disj_imm,
                assertion_postconditions
            );
        }
    }

    // Tier 3: predicate-atom assertion disjunctions: pred_atom || negation_atom.
    // Crucial shape: pairs the loop continuation guard `j < SIZE` (which lives in
    // pred_atoms as a CFG edge guard / Predicate-Assign effect) with the safety
    // condition.  For `array-1`, the candidate `(j < SIZE) || (array[0] >= menor)`
    // discharges exit closure cleanly even when SIZE could be 0:
    //   • Initiation: at j=0 with SIZE bound, `j < SIZE` is true (or array
    //     property holds trivially).
    //   • Exit closure: at j >= SIZE, the first disjunct is false, so the
    //     safety atom must hold — matching the violation's negation.
    // Bounded by |pred_atoms| × |negation_atoms| — typically 8 × 1 atoms.
    if !pred_atoms.is_empty() && !negation_atoms.is_empty() {
        let mut pred_assert_disj: Vec<Formula> = Vec::new();
        for p in &pred_atoms {
            for atom in &negation_atoms {
                pred_assert_disj.push(Formula::or(p.clone(), atom.clone()));
            }
        }
        tier!(
            "pred-assert-disj",
            pred_assert_disj,
            assertion_postconditions
        );
    }

    // Tier 4: predicate atoms from code (no positive-consistency filtering)
    tier!("pred-atoms", pred_atoms.clone(), assertion_postconditions);

    // Tier 5: pairwise conjunctions of predicate atoms
    {
        let pred_refs: Vec<&Formula> = pred_atoms.iter().collect();
        let mut conj = Vec::new();
        append_pairwise_conjunctions(&mut conj, &pred_refs);
        tier!("pred-conj", conj, assertion_postconditions);
    }

    // Tier 6: counter-init predicate disjunctions: (counter_init) || pred_atom.
    // Exit closure is checked with the real assertion postconditions.
    if !counter_inits.is_empty() {
        let mut counter_pred_disj: Vec<Formula> = Vec::new();
        for ci in &counter_inits {
            for atom in &pred_atoms {
                counter_pred_disj.push(Formula::or(ci.clone(), atom.clone()));
            }
        }
        tier!(
            "counter-pred-disj",
            counter_pred_disj,
            assertion_postconditions
        );
    }

    // Tier 7: counter-init combinatorial disjunctions: (counter_init) || atom.
    // Finds cross-region relational invariants not reachable via assertion
    // negation atoms alone.  Includes ALL combo atoms for full coverage.
    if !counter_inits.is_empty() {
        let mut counter_combo_disj: Vec<Formula> = Vec::new();
        for ci in &counter_inits {
            for atom in &combo_atoms {
                counter_combo_disj.push(Formula::or(ci.clone(), atom.clone()));
            }
        }
        tier!(
            "counter-combo-disj",
            counter_combo_disj,
            assertion_postconditions
        );
    }

    // Tier 8: positive-consistent combinatorial atoms
    tier!(
        "combo-atoms",
        pos_consistent.clone(),
        assertion_postconditions
    );

    // Tier 9: pairwise conjunctions of combinatorial atoms
    {
        let pos_refs: Vec<&Formula> = pos_consistent.iter().collect();
        let mut conj = Vec::new();
        append_pairwise_conjunctions(&mut conj, &pos_refs);
        tier!("combo-conj", conj, assertion_postconditions);
    }

    // Tier 10: ICE-guided disjunctions
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

    // Tier 11: pairwise disjunctions of combinatorial atoms (fallback)
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
