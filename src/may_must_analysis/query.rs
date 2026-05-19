//! Query types for the demand-driven SMASH refactor.
//!
//! Per `design_notes/QUERY_REFACTOR.md`, the unit of work is no longer an
//! `AssertionSite` analysed in isolation, but a Hoare-style query
//! `⟨pre ⇒ proc post⟩`.  Top-level assertions become initial queries with
//! `post = ¬obligation`; call sites generate sub-queries with caller-derived
//! pre and post.  Multiple contextual summaries per procedure are produced
//! from completed query results and reused via subsumption.
//!
//! This module defines the data shapes — no scheduler logic yet (that lives
//! in `scheduler.rs`).  Subsumption helpers operate purely on formulas via
//! the [`Oracle`], so they are unit-testable without any CFG.
//!
//! # Subsumption asymmetry (must read)
//!
//! The direction of implications differs between NotMay and Must:
//!
//! - **NotMaySummary covers query** iff `q.pre ⇒ s.pre  ∧  q.post ⇒ s.post`.
//!   The summary proves "from `s.pre`, `s.post` is unreachable"; the query
//!   asks "from `q.pre`, can `q.post` reach?".  If `q.pre` is in `s.pre`'s
//!   range and `q.post` is in `s.post`'s range, the answer is no.
//!
//! - **MustSummary covers query** iff `s.pre ⇒ q.pre  ∧  s.post ⇒ q.post`.
//!   The summary witnesses "from `s.pre` we can reach `s.post`"; if the
//!   summary's pre is contained in the query's pre, and the summary's post
//!   is contained in the query's post, the same witness applies.

#![allow(dead_code)]

use crate::common::abstract_cfg::substitute_var_in_formula;
use crate::common::formula::{Formula, Memory, SmtModel, Term, Var};
use crate::common::oracle::{Oracle, OracleError, Validity};
use crate::may_must_analysis::summaries::{MaySummary, NotMaySummary, ProcedureName};
use std::collections::{BTreeMap, BTreeSet};

/// A demand-driven query asking one Hoare-style question of one procedure.
///
/// Semantics: "Assuming `pre` holds at the entry of `procedure`, is some
/// state in `post` reachable at its exit (or violation site)?"
///
/// Both analysis directions (backward NOT-MAY, forward MUST) race to
/// discharge a single query.  The first decisive result wins; the other
/// direction may still contribute to summaries.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Query {
    /// Procedure being analysed.
    pub procedure: ProcedureName,
    /// Caller-derived precondition at the procedure entry, expressed over
    /// procedure-interface variables (formals, externally-visible regions,
    /// globals).
    pub pre: Formula,
    /// Caller-derived "bad" postcondition.  For top-level assertion
    /// queries this is `¬obligation`.  For call-site queries it is the
    /// caller's projected post-state.
    pub post: Formula,
}

impl Query {
    pub fn new(procedure: impl Into<ProcedureName>, pre: Formula, post: Formula) -> Self {
        Self {
            procedure: procedure.into(),
            pre,
            post,
        }
    }
}

/// Stable identifier for a query within a single `Scheduler` run.
///
/// Assigned at enqueue time.  Two queries that are textually identical but
/// enqueued separately receive different ids; the scheduler's subsumption
/// check decides whether to share a result.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct QueryId(pub usize);

/// The decisive result a query produces, plus the summary it contributes
/// to the contextual table.
#[derive(Clone, Debug)]
pub enum QueryResult {
    /// `post` is provably NOT reachable from `pre` in this procedure.
    NotReachable { summary: NotMaySummary },

    /// A concrete execution from a state satisfying `pre` reaches a state
    /// satisfying `post`.  Sound only when produced by the forward-MUST
    /// direction (backward-on-acyclic, native or BMC-unrolled).
    Reachable {
        /// Projected MUST summary (concrete witness in procedure-interface
        /// variables).  Distinct from `MaySummary` — see the type
        /// documentation in `summaries.rs`.
        summary: ContextualMustSummary,
        witness: Option<SmtModel>,
    },

    /// Neither direction reached a decisive verdict.
    Unknown,
}

/// True under-approximate MUST summary derived from a forward-MUST query
/// result.  Distinct from `MaySummary` (which is over-approximate and
/// historically misnamed `MustSummary`).  See
/// `design_notes/QUERY_REFACTOR.md` §3 for the rationale.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ContextualMustSummary {
    /// Concrete pre-state from which the witness was derived, projected
    /// to procedure-interface variables.
    pub precondition: Formula,
    /// Concrete post-state the witness reaches, also projected.
    pub postcondition: Formula,
}

/// An in-progress query and its dependents.
///
/// Recursion is detected via subsumption against active queries: if a new
/// query is subsumed by an in-progress one, we register a dependency
/// rather than re-entering the same analysis.
#[derive(Clone, Debug)]
pub struct InProgressQuery {
    pub id: QueryId,
    pub query: Query,
    /// Queries currently blocked on this one finishing.
    pub dependents: Vec<QueryId>,
    pub placeholder: PlaceholderKind,
}

/// What an in-progress query contributes to its own dependents while it
/// has no result yet.
///
/// The choice is direction-specific:
///
/// - `NotMayOptimistic`: assume the query will succeed (call edge is
///   safe).  Sound only if the eventual result is `NotReachable`; if
///   `Reachable` is produced instead, dependents must be re-checked.
///
/// - `MustOptimistic`: assume the query will not produce a witness (no
///   contribution to forward must_reach).  Sound only if the eventual
///   result is `NotReachable` or `Unknown`; a `Reachable` outcome forces
///   re-check of dependents.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PlaceholderKind {
    NotMayOptimistic,
    MustOptimistic,
}

// ── Subsumption ──────────────────────────────────────────────────────────

/// Result of a subsumption check.  Cheaper than a full oracle implication —
/// the helpers below short-circuit on structural equality and on trivial
/// `True` / `False` cases before invoking the SMT solver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Subsumption {
    /// Definitely covers.
    Covers,
    /// Definitely does not cover.
    DoesNotCover,
    /// Oracle returned Unknown; safe default: treat as not covering.
    OracleUnknown,
}

impl Subsumption {
    pub fn is_covering(self) -> bool {
        matches!(self, Subsumption::Covers)
    }
}

/// Does `NotMaySummary { pre_s, post_s }` cover `query`?
///
/// Returns `Covers` iff `q.pre ⇒ pre_s ∧ q.post ⇒ post_s`.  See the
/// module-level documentation for the direction asymmetry.
pub fn notmay_covers(
    summary: &NotMaySummary,
    query: &Query,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    let pre_ok = implies_with_shortcuts(&query.pre, &summary.precondition, oracle)?;
    if !matches!(pre_ok, Subsumption::Covers) {
        return Ok(pre_ok);
    }
    implies_with_shortcuts(&query.post, &summary.postcondition, oracle)
}

/// Does `MustSummary { pre_s, post_s }` cover `query`?
///
/// Returns `Covers` iff `pre_s ⇒ q.pre ∧ post_s ⇒ q.post`.
pub fn must_covers(
    summary: &ContextualMustSummary,
    query: &Query,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    let pre_ok = implies_with_shortcuts(&summary.precondition, &query.pre, oracle)?;
    if !matches!(pre_ok, Subsumption::Covers) {
        return Ok(pre_ok);
    }
    implies_with_shortcuts(&summary.postcondition, &query.post, oracle)
}

/// Implication check with cheap shortcuts before invoking the oracle.
///
/// Order: structural equality, `lhs == False`, `rhs == True`, then SMT.
fn implies_with_shortcuts(
    lhs: &Formula,
    rhs: &Formula,
    oracle: &Oracle,
) -> Result<Subsumption, OracleError> {
    if lhs == rhs {
        return Ok(Subsumption::Covers);
    }
    if matches!(lhs, Formula::False) {
        return Ok(Subsumption::Covers); // ex falso quodlibet
    }
    if matches!(rhs, Formula::True) {
        return Ok(Subsumption::Covers); // anything implies True
    }
    match oracle.implies(lhs, rhs)? {
        Validity::Valid => Ok(Subsumption::Covers),
        Validity::Invalid => Ok(Subsumption::DoesNotCover),
        Validity::Unknown => Ok(Subsumption::OracleUnknown),
    }
}

// ── Contextual summary table ────────────────────────────────────────────

/// Per-(procedure, query-post) loop invariant cache key.  See
/// `design_notes/LOOPS.md` §2 for why invariants are keyed by query post.
///
/// `None` indicates a post-independent invariant (produced by the pre-pass
/// before any assertion context is known).
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum QueryPostFingerprint {
    /// Post-independent invariant — applies to every query on this procedure.
    None,
    /// Canonical fingerprint of `Query.post` for cache keying.  The first
    /// cut uses `Debug` formatting; a richer canonicalisation can replace
    /// it later without changing semantics.
    Hash(String),
}

impl QueryPostFingerprint {
    pub fn of_post(post: &Formula) -> Self {
        QueryPostFingerprint::Hash(format!("{post:?}"))
    }
}

/// Contextual summary table: multiple `NotMaySummary` and contextual
/// `MustSummary` entries per procedure, plus loop invariants keyed by
/// `(procedure, fingerprint)`.
///
/// Coexists with the current `SummaryTables` during the refactor.  The
/// existing types (`MaySummary` for forward MAY summaries, `NotMaySummary`)
/// stay as the over-approximate side; the new `ContextualMustSummary` is
/// the under-approximate side.
#[derive(Clone, Debug, Default)]
pub struct ContextualSummaryTable {
    /// Contextual not-may summaries (over-approximate; safety).
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    /// Contextual must summaries (under-approximate; concrete witness).
    pub must: BTreeMap<ProcedureName, Vec<ContextualMustSummary>>,
    /// Over-approximate forward-may summaries (renamed from the old
    /// MustSummary in v0.15.0).  Consumed by `forward_may_usesummary` to
    /// widen `reach` at call sites.
    pub may: BTreeMap<ProcedureName, Vec<MaySummary>>,
    /// Loop invariants keyed by `(procedure, query-post fingerprint)`.
    pub loop_invariants: BTreeMap<
        (ProcedureName, QueryPostFingerprint),
        Vec<(crate::common::abstract_cfg::CfgNodeId, Formula)>,
    >,
}

impl ContextualSummaryTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn notmay(&self, procedure: &str) -> &[NotMaySummary] {
        self.notmay
            .get(procedure)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    pub fn must(&self, procedure: &str) -> &[ContextualMustSummary] {
        self.must
            .get(procedure)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    pub fn may(&self, procedure: &str) -> &[MaySummary] {
        self.may.get(procedure).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Adds a `NotMaySummary` with merge-with-subsumption semantics
    /// (`MERGE_MAY_SUMMARY` from the paper).  Returns `true` if the new
    /// summary was kept; `false` if an existing summary already covered it
    /// (in which case the new one is discarded).
    pub fn merge_notmay(
        &mut self,
        procedure: impl Into<ProcedureName>,
        new_summary: NotMaySummary,
        oracle: &Oracle,
    ) -> Result<bool, OracleError> {
        let name = procedure.into();
        let entries = self.notmay.entry(name).or_default();
        // Is there an existing summary that already covers `new_summary`?
        // i.e. is there `s_old` such that `s_old` covers the query
        // `{pre: new.pre, post: new.post}`?
        let new_as_query = Query {
            procedure: String::new(), // procedure name unused in subsumption
            pre: new_summary.precondition.clone(),
            post: new_summary.postcondition.clone(),
        };
        for existing in entries.iter() {
            if matches!(
                notmay_covers(existing, &new_as_query, oracle)?,
                Subsumption::Covers
            ) {
                return Ok(false);
            }
        }
        // Remove any entries that the new summary subsumes.
        let mut kept = Vec::with_capacity(entries.len() + 1);
        for existing in entries.drain(..) {
            let existing_as_query = Query {
                procedure: String::new(),
                pre: existing.precondition.clone(),
                post: existing.postcondition.clone(),
            };
            if !matches!(
                notmay_covers(&new_summary, &existing_as_query, oracle)?,
                Subsumption::Covers
            ) {
                kept.push(existing);
            }
        }
        kept.push(new_summary);
        *entries = kept;
        Ok(true)
    }

    /// Analogous merge for `ContextualMustSummary` (`MERGE_MUST_SUMMARY`).
    pub fn merge_must(
        &mut self,
        procedure: impl Into<ProcedureName>,
        new_summary: ContextualMustSummary,
        oracle: &Oracle,
    ) -> Result<bool, OracleError> {
        let name = procedure.into();
        let entries = self.must.entry(name).or_default();
        let new_as_query = Query {
            procedure: String::new(),
            pre: new_summary.precondition.clone(),
            post: new_summary.postcondition.clone(),
        };
        for existing in entries.iter() {
            if matches!(
                must_covers(existing, &new_as_query, oracle)?,
                Subsumption::Covers
            ) {
                return Ok(false);
            }
        }
        let mut kept = Vec::with_capacity(entries.len() + 1);
        for existing in entries.drain(..) {
            let existing_as_query = Query {
                procedure: String::new(),
                pre: existing.precondition.clone(),
                post: existing.postcondition.clone(),
            };
            if !matches!(
                must_covers(&new_summary, &existing_as_query, oracle)?,
                Subsumption::Covers
            ) {
                kept.push(existing);
            }
        }
        kept.push(new_summary);
        *entries = kept;
        Ok(true)
    }

    /// Find a `NotMaySummary` covering `query`.  Returns the first match;
    /// callers may want to prefer "tightest" matches but for correctness
    /// any covering summary is sound.
    pub fn lookup_notmay_covering(
        &self,
        query: &Query,
        oracle: &Oracle,
    ) -> Result<Option<&NotMaySummary>, OracleError> {
        for summary in self.notmay(&query.procedure) {
            if matches!(notmay_covers(summary, query, oracle)?, Subsumption::Covers) {
                return Ok(Some(summary));
            }
        }
        Ok(None)
    }

    /// Find a `ContextualMustSummary` covering `query`.
    pub fn lookup_must_covering(
        &self,
        query: &Query,
        oracle: &Oracle,
    ) -> Result<Option<&ContextualMustSummary>, OracleError> {
        for summary in self.must(&query.procedure) {
            if matches!(must_covers(summary, query, oracle)?, Subsumption::Covers) {
                return Ok(Some(summary));
            }
        }
        Ok(None)
    }
}

// ── Unit tests ──────────────────────────────────────────────────────────

// ── Projection to procedure interface ────────────────────────────────────

/// Identifies the procedure-interface boundary used by `project_to_interface`.
///
/// **What counts as "interface"** (and survives projection):
/// - Formal parameters (callers can name them by passing actuals).
/// - The return value `{procedure}$__retval` (renamed to the caller's
///   call-result variable when the summary is applied).
/// - All memory regions, by current policy.  This preserves heap/stack
///   content and globals verbatim — see `design_notes/QUERY_REFACTOR.md`
///   §5.  An escape analysis can be added later to additionally drop
///   regions provably not referenced by any caller; doing so is
///   precision-improving, not soundness-affecting.
///
/// **What gets eliminated:**
/// - Local SSA scalar variables `{procedure}$%N` other than formals.
///   We substitute via captured equalities `v == e` where `e` mentions
///   only interface symbols; if substitution can't reach all locals,
///   the projection fails and no summary is emitted (sound: callers
///   simply re-spawn the query).
pub struct ProcedureInterface {
    /// Procedure being projected.
    pub procedure: ProcedureName,
    /// SSA names of formal parameters (e.g. `["P$%0", "P$%1"]`).  These are
    /// the *only* `P$%*` names that survive projection; everything else with
    /// that prefix is treated as a local to eliminate.
    pub formals: BTreeSet<String>,
}

impl ProcedureInterface {
    /// Build an interface descriptor.  Formal parameters must be supplied
    /// explicitly — there is no syntactic way to distinguish a formal from
    /// a local SSA register (both look like `P$%N`).
    pub fn new(
        procedure: impl Into<ProcedureName>,
        formals: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            procedure: procedure.into(),
            formals: formals.into_iter().collect(),
        }
    }

    /// Returns `true` if `name` is an interface scalar variable.
    ///
    /// Interface scalars: formals, the synthetic retval, and *any* variable
    /// that doesn't look like a procedure-local (so external SMT-level
    /// quantifiers, globals reduced to scalars, etc. are preserved).
    pub fn is_interface_scalar(&self, name: &str) -> bool {
        if self.formals.contains(name) {
            return true;
        }
        let retval = format!("{}$__retval", self.procedure);
        if name == retval {
            return true;
        }
        // Anything starting with `{procedure}$%` and not in formals is a
        // local SSA register — NOT interface.
        let local_prefix = format!("{}$%", self.procedure);
        if name.starts_with(&local_prefix) {
            return false;
        }
        // Anything starting with `{procedure}$stack` or `{procedure}$call`
        // is a local prefix for region/temp names; treat as non-interface
        // for scalars but the *memory regions* are preserved separately.
        // (Region preservation lives in the projector; this method only
        // judges scalar interface membership.)
        let stack_prefix = format!("{}$stack", self.procedure);
        let call_prefix = format!("{}$call", self.procedure);
        if name.starts_with(&stack_prefix) || name.starts_with(&call_prefix) {
            // These are region names that may show up syntactically as
            // bare vars in some contexts; we defer to the memory branch.
            // Treat them as interface here so they don't trigger scalar
            // elimination — the projector only removes `P$%*` scalars.
            return true;
        }
        // Anything else (globals, `__ext_*`, foreign module symbols) is
        // interface by default.
        true
    }
}

/// Project `formula` so it mentions only interface scalars (per
/// [`ProcedureInterface::is_interface_scalar`]).  All memory `select` /
/// `store` chains over any region are preserved verbatim — including
/// procedure-local stack regions, by the current policy.
///
/// Returns:
/// - `Some(projected)` if every non-interface scalar was eliminated by
///   substitution of an `Eq(local, expr)` equality, where `expr` mentions
///   only interface things.
/// - `None` if any non-interface scalar survives substitution.  This means
///   the summary cannot be safely emitted; callers must re-analyse the
///   procedure under the caller's specific context.
///
/// # Soundness
///
/// Substitution `local := expr` is **semantically equivalent** when `local`
/// was defined by `local == expr` in the formula being projected (which is
/// the standard SSA shape produced by the adapter).  No widening occurs:
/// the resulting summary has the *same* set of models, restricted to the
/// projection of the interface variables.  This is the only safe path —
/// dropping conjuncts to "eliminate" stuck locals would widen the formula,
/// which is unsound for both NotMay (broader pre claims unproven safety)
/// and Must (broader pre claims unwitnessed reachability).
///
/// # Debug-watchpoint
///
/// When projection returns `None`, the offending non-interface scalars
/// are logged on target `"projection"` at info level.  These are
/// candidate places to investigate for precision loss (e.g., a phi-node
/// whose value couldn't be tied to interface inputs, or a conditional
/// store whose unevaluated branch left a `select(_, branch_local)`).
pub fn project_to_interface(formula: &Formula, interface: &ProcedureInterface) -> Option<Formula> {
    // Collect substitution candidates: equalities `Eq(Var(local), expr)`
    // or `Eq(expr, Var(local))` where local is a non-interface scalar.
    let mut substitutions: BTreeMap<String, Term> = BTreeMap::new();
    collect_local_definitions(formula, interface, &mut substitutions);

    // Resolve chained substitutions to a fixpoint.  E.g. if we have
    // `%15 -> %13 < %14`, `%13 -> select(stack2, 0)`, `%14 -> select(stack1, 0)`,
    // resolve `%15` to `select(stack2, 0) < select(stack1, 0)`.
    let resolved = resolve_substitution_chain(substitutions);

    // Apply substitutions throughout the formula.
    let mut projected = formula.clone();
    for (name, replacement) in &resolved {
        // `substitute_var_in_formula` handles all formula/term variants.
        // We construct a Var with Int sort by default; the underlying
        // substitution is sort-agnostic for our purposes (it only matches
        // by name).  See note in abstract_cfg.rs.
        let target_var = Var::new(name.clone(), guess_sort_of(replacement));
        projected = substitute_var_in_formula(&target_var, replacement, &projected);
    }

    // Verify no non-interface scalars remain.
    let remaining = find_non_interface_scalars(&projected, interface);
    if !remaining.is_empty() {
        log::info!(
            target: "projection",
            "project_to_interface({}): could not eliminate {:?} — discarding summary. \
             Debug-watchpoint: these locals were not bound by an Eq(local, interface-only-expr) \
             conjunct in the formula being projected.",
            interface.procedure,
            remaining,
        );
        return None;
    }

    Some(projected)
}

/// Walk `formula` collecting `Eq(Var(local), expr)` equalities where
/// `local` is a non-interface scalar.  Used by `project_to_interface` to
/// build the substitution map.
///
/// We collect equalities from positive positions only (inside conjunctions
/// and the top-level structure).  Equalities buried inside negations,
/// disjunctions, or implications are NOT treated as definitions — they
/// may not hold on every model.
fn collect_local_definitions(
    formula: &Formula,
    interface: &ProcedureInterface,
    out: &mut BTreeMap<String, Term>,
) {
    match formula {
        Formula::Eq(lhs, rhs) => {
            // Try both directions: local == expr  or  expr == local.
            if let Some((name, replacement)) = local_equality_pair(lhs, rhs, interface) {
                // First-write-wins.  If we already substituted this name,
                // keep the earlier binding (in SSA each name has at most
                // one definition anyway).
                out.entry(name).or_insert(replacement);
            } else if let Some((name, replacement)) = local_equality_pair(rhs, lhs, interface) {
                out.entry(name).or_insert(replacement);
            }
        }
        Formula::And(parts) => {
            for p in parts {
                collect_local_definitions(p, interface, out);
            }
        }
        // Conservative: don't peer into negations, disjunctions, implications.
        _ => {}
    }
}

/// If `lhs` is `Var(local-non-interface-scalar)`, return the pair
/// `(local_name, rhs)`.  Otherwise return `None`.
///
/// We do NOT require `rhs` to mention only interface things here — the
/// transitive resolution in [`resolve_substitution_chain`] handles
/// chains like `%3 == %2 + 1, %2 == p$%0 * 2`.  Collecting every local
/// equality regardless of RHS purity lets the resolver substitute
/// `%2 → p$%0 * 2` into `%3`'s RHS during fixpoint iteration.
fn local_equality_pair(
    lhs: &Term,
    rhs: &Term,
    interface: &ProcedureInterface,
) -> Option<(String, Term)> {
    let Term::Var(var) = lhs else {
        return None;
    };
    if interface.is_interface_scalar(var.name()) {
        return None;
    }
    Some((var.name().to_string(), rhs.clone()))
}

/// Returns `true` if `term` references any non-interface scalar.
fn term_mentions_non_interface_scalar(term: &Term, interface: &ProcedureInterface) -> bool {
    match term {
        Term::Var(v) => !interface.is_interface_scalar(v.name()),
        Term::Int(_) | Term::Real(_) => false,
        Term::BoolToInt(inner) => formula_mentions_non_interface_scalar(inner, interface),
        Term::Select(_mem, idx) => term_mentions_non_interface_scalar(idx, interface),
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            term_mentions_non_interface_scalar(a, interface)
                || term_mentions_non_interface_scalar(b, interface)
        }
        Term::Neg(inner) => term_mentions_non_interface_scalar(inner, interface),
    }
}

/// Returns `true` if `formula` references any non-interface scalar.
fn formula_mentions_non_interface_scalar(
    formula: &Formula,
    interface: &ProcedureInterface,
) -> bool {
    match formula {
        Formula::True | Formula::False => false,
        Formula::Var(v) => !interface.is_interface_scalar(v.name()),
        Formula::Not(inner) => formula_mentions_non_interface_scalar(inner, interface),
        Formula::And(parts) | Formula::Or(parts) => parts
            .iter()
            .any(|p| formula_mentions_non_interface_scalar(p, interface)),
        Formula::Implies(lhs, rhs) => {
            formula_mentions_non_interface_scalar(lhs, interface)
                || formula_mentions_non_interface_scalar(rhs, interface)
        }
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => {
            term_mentions_non_interface_scalar(a, interface)
                || term_mentions_non_interface_scalar(b, interface)
        }
        Formula::MemoryEq(a, b) => {
            memory_mentions_non_interface_scalar(a, interface)
                || memory_mentions_non_interface_scalar(b, interface)
        }
    }
}

fn memory_mentions_non_interface_scalar(memory: &Memory, interface: &ProcedureInterface) -> bool {
    match memory {
        Memory::Var(_) => false,
        Memory::Store(mem, idx, val) => {
            memory_mentions_non_interface_scalar(mem, interface)
                || term_mentions_non_interface_scalar(idx, interface)
                || term_mentions_non_interface_scalar(val, interface)
        }
    }
}

/// Resolve chained substitutions to a fixpoint.  Returns a new map where
/// every replacement term mentions only interface scalars (or the
/// substitution failed and the unresolved entries are still present).
fn resolve_substitution_chain(mut subst: BTreeMap<String, Term>) -> BTreeMap<String, Term> {
    // Bounded iteration — chains are short in practice (SSA register
    // dependency depth).  8 iterations is plenty; a hard cap prevents
    // infinite loops if the map contains a cycle (which SSA never does
    // but defensive code is cheap).
    for _ in 0..8 {
        let snapshot = subst.clone();
        let mut changed = false;
        for (_, value) in subst.iter_mut() {
            let new_value = apply_subst_to_term(value, &snapshot);
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

fn apply_subst_to_term(term: &Term, subst: &BTreeMap<String, Term>) -> Term {
    match term {
        Term::Var(v) => subst.get(v.name()).cloned().unwrap_or_else(|| term.clone()),
        Term::Int(_) | Term::Real(_) => term.clone(),
        Term::BoolToInt(inner) => Term::bool_to_int(apply_subst_to_formula(inner, subst)),
        Term::Select(mem, idx) => Term::select((**mem).clone(), apply_subst_to_term(idx, subst)),
        Term::Add(a, b) => Term::add(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst)),
        Term::Sub(a, b) => Term::sub(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst)),
        Term::Mul(a, b) => Term::mul(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst)),
        Term::Div(a, b) => Term::div(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst)),
        Term::Rem(a, b) => Term::rem(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst)),
        Term::Neg(inner) => Term::neg(apply_subst_to_term(inner, subst)),
    }
}

fn apply_subst_to_formula(formula: &Formula, subst: &BTreeMap<String, Term>) -> Formula {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) | Formula::MemoryEq(_, _) => {
            formula.clone()
        }
        Formula::Not(inner) => Formula::not(apply_subst_to_formula(inner, subst)),
        Formula::And(parts) => Formula::and_all(
            parts
                .iter()
                .map(|p| apply_subst_to_formula(p, subst))
                .collect::<Vec<_>>(),
        ),
        Formula::Or(parts) => Formula::or_all(
            parts
                .iter()
                .map(|p| apply_subst_to_formula(p, subst))
                .collect::<Vec<_>>(),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            apply_subst_to_formula(lhs, subst),
            apply_subst_to_formula(rhs, subst),
        ),
        Formula::Eq(a, b) => {
            Formula::eq(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst))
        }
        Formula::Lt(a, b) => {
            Formula::lt(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst))
        }
        Formula::Le(a, b) => {
            Formula::le(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst))
        }
        Formula::Gt(a, b) => {
            Formula::gt(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst))
        }
        Formula::Ge(a, b) => {
            Formula::ge(apply_subst_to_term(a, subst), apply_subst_to_term(b, subst))
        }
    }
}

/// Crude sort inference for substitution.  `substitute_var_in_formula`
/// matches by name; the sort attached to the target `Var` is unused by
/// the substitution itself but kept for type-consistency.
fn guess_sort_of(term: &Term) -> crate::common::formula::Sort {
    match term {
        Term::Real(_) => crate::common::formula::Sort::Real,
        // BoolToInt produces an Int; everything else we use is Int-sorted.
        _ => crate::common::formula::Sort::Int,
    }
}

/// Collect names of non-interface scalars remaining in `formula`.
fn find_non_interface_scalars(
    formula: &Formula,
    interface: &ProcedureInterface,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    walk_formula_collect_non_interface(formula, interface, &mut out);
    out
}

fn walk_formula_collect_non_interface(
    formula: &Formula,
    interface: &ProcedureInterface,
    out: &mut BTreeSet<String>,
) {
    match formula {
        Formula::True | Formula::False => {}
        Formula::Var(v) => {
            if !interface.is_interface_scalar(v.name()) {
                out.insert(v.name().to_string());
            }
        }
        Formula::Not(inner) => walk_formula_collect_non_interface(inner, interface, out),
        Formula::And(parts) | Formula::Or(parts) => {
            for p in parts {
                walk_formula_collect_non_interface(p, interface, out);
            }
        }
        Formula::Implies(lhs, rhs) => {
            walk_formula_collect_non_interface(lhs, interface, out);
            walk_formula_collect_non_interface(rhs, interface, out);
        }
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => {
            walk_term_collect_non_interface(a, interface, out);
            walk_term_collect_non_interface(b, interface, out);
        }
        Formula::MemoryEq(a, b) => {
            walk_memory_collect_non_interface(a, interface, out);
            walk_memory_collect_non_interface(b, interface, out);
        }
    }
}

fn walk_term_collect_non_interface(
    term: &Term,
    interface: &ProcedureInterface,
    out: &mut BTreeSet<String>,
) {
    match term {
        Term::Var(v) => {
            if !interface.is_interface_scalar(v.name()) {
                out.insert(v.name().to_string());
            }
        }
        Term::Int(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => walk_formula_collect_non_interface(inner, interface, out),
        Term::Select(_mem, idx) => walk_term_collect_non_interface(idx, interface, out),
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) | Term::Div(a, b) | Term::Rem(a, b) => {
            walk_term_collect_non_interface(a, interface, out);
            walk_term_collect_non_interface(b, interface, out);
        }
        Term::Neg(inner) => walk_term_collect_non_interface(inner, interface, out),
    }
}

fn walk_memory_collect_non_interface(
    memory: &Memory,
    interface: &ProcedureInterface,
    out: &mut BTreeSet<String>,
) {
    match memory {
        Memory::Var(_) => {}
        Memory::Store(mem, idx, val) => {
            walk_memory_collect_non_interface(mem, interface, out);
            walk_term_collect_non_interface(idx, interface, out);
            walk_term_collect_non_interface(val, interface, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::formula::{Sort, Term, Var};

    fn bool_var(name: &str) -> Formula {
        Formula::Var(Var::new(name, Sort::Bool))
    }

    fn int_le(a: &str, b: i64) -> Formula {
        Formula::le(Term::Var(Var::new(a, Sort::Int)), Term::int(b))
    }

    #[test]
    fn structural_equality_is_covering() {
        let oracle = Oracle::new();
        let f = bool_var("p");
        assert!(matches!(
            implies_with_shortcuts(&f, &f, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn anything_implies_true() {
        let oracle = Oracle::new();
        let f = int_le("x", 5);
        assert!(matches!(
            implies_with_shortcuts(&f, &Formula::True, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn false_implies_anything() {
        let oracle = Oracle::new();
        let f = int_le("x", 5);
        assert!(matches!(
            implies_with_shortcuts(&Formula::False, &f, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn notmay_covers_uses_query_implies_summary() {
        // Summary: from `x <= 10`, post `x <= 20` is unreachable.
        // Query: from `x <= 5`, is `x <= 15` reachable?
        // Subsumption check: x<=5 ⇒ x<=10  AND  x<=15 ⇒ x<=20  → Covers.
        let oracle = Oracle::new();
        let summary = NotMaySummary {
            precondition: int_le("x", 10),
            postcondition: int_le("x", 20),
        };
        let query = Query::new("p", int_le("x", 5), int_le("x", 15));
        assert!(matches!(
            notmay_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn notmay_covers_rejects_when_query_pre_too_weak() {
        // Summary needs x <= 10 at pre; query offers x <= 20 — too weak.
        let oracle = Oracle::new();
        let summary = NotMaySummary {
            precondition: int_le("x", 10),
            postcondition: int_le("x", 20),
        };
        let query = Query::new("p", int_le("x", 20), int_le("x", 15));
        assert!(!matches!(
            notmay_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn must_covers_uses_summary_implies_query() {
        // MustSummary: witness from `x <= 5` reaches `x <= 15`.
        // Query: from `x <= 10`, can `x <= 20` reach?
        // Subsumption: x<=5 ⇒ x<=10  AND  x<=15 ⇒ x<=20  → Covers.
        let oracle = Oracle::new();
        let summary = ContextualMustSummary {
            precondition: int_le("x", 5),
            postcondition: int_le("x", 15),
        };
        let query = Query::new("p", int_le("x", 10), int_le("x", 20));
        assert!(matches!(
            must_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn must_covers_rejects_when_summary_pre_too_loose() {
        // MustSummary witnesses from `x <= 20`; query restricts to `x <= 5`.
        let oracle = Oracle::new();
        let summary = ContextualMustSummary {
            precondition: int_le("x", 20),
            postcondition: int_le("x", 15),
        };
        let query = Query::new("p", int_le("x", 5), int_le("x", 30));
        assert!(!matches!(
            must_covers(&summary, &query, &oracle).unwrap(),
            Subsumption::Covers
        ));
    }

    #[test]
    fn merge_notmay_discards_subsumed_addition() {
        // A NotMay summary `{pre_s, post_s}` is **stronger / more general**
        // when `pre_s` is weaker (broader pre-range) AND `post_s` is weaker
        // (broader bad-post coverage).  Existing `{x<=10, x<=20}` subsumes
        // a stricter new `{x<=5, x<=15}`:
        //   new.pre  (x<=5)  ⇒ existing.pre  (x<=10)   ✓
        //   new.post (x<=15) ⇒ existing.post (x<=20)   ✓
        // → covered, discard the new one.
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        let kept = tbl
            .merge_notmay(
                "p",
                NotMaySummary {
                    precondition: int_le("x", 5),
                    postcondition: int_le("x", 15),
                },
                &oracle,
            )
            .unwrap();
        assert!(!kept, "subsumed summary should be discarded");
        assert_eq!(tbl.notmay("p").len(), 1);
    }

    #[test]
    fn merge_notmay_removes_subsumed_existing() {
        // Inverse: insert the stricter summary first, then a broader one.
        // The broader subsumes the stricter, so the stricter is removed.
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 5),
                postcondition: int_le("x", 15),
            },
            &oracle,
        )
        .unwrap();
        let kept = tbl
            .merge_notmay(
                "p",
                NotMaySummary {
                    precondition: int_le("x", 10),
                    postcondition: int_le("x", 20),
                },
                &oracle,
            )
            .unwrap();
        assert!(kept, "broader summary should be kept");
        assert_eq!(
            tbl.notmay("p").len(),
            1,
            "broader summary should replace stricter one"
        );
    }

    #[test]
    fn lookup_notmay_finds_covering_summary() {
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        let query = Query::new("p", int_le("x", 5), int_le("x", 15));
        let found = tbl.lookup_notmay_covering(&query, &oracle).unwrap();
        assert!(found.is_some());
    }

    #[test]
    fn lookup_notmay_misses_when_no_summary_covers() {
        let oracle = Oracle::new();
        let mut tbl = ContextualSummaryTable::new();
        tbl.merge_notmay(
            "p",
            NotMaySummary {
                precondition: int_le("x", 10),
                postcondition: int_le("x", 20),
            },
            &oracle,
        )
        .unwrap();
        // Query precondition is weaker than summary's — not covered.
        let query = Query::new("p", int_le("x", 100), int_le("x", 15));
        let found = tbl.lookup_notmay_covering(&query, &oracle).unwrap();
        assert!(found.is_none());
    }

    #[test]
    fn query_post_fingerprint_is_stable() {
        let f1 = int_le("x", 10);
        let f2 = int_le("x", 10);
        assert_eq!(
            QueryPostFingerprint::of_post(&f1),
            QueryPostFingerprint::of_post(&f2)
        );
        let f3 = int_le("x", 20);
        assert_ne!(
            QueryPostFingerprint::of_post(&f1),
            QueryPostFingerprint::of_post(&f3)
        );
    }

    // ── Projection ─────────────────────────────────────────────────────

    fn int_var(name: &str) -> Term {
        Term::Var(Var::new(name, Sort::Int))
    }

    fn iface_with_no_formals(procedure: &str) -> ProcedureInterface {
        ProcedureInterface::new(procedure, std::iter::empty())
    }

    #[test]
    fn projection_keeps_formals_and_retval() {
        let iface = ProcedureInterface::new("p", vec!["p$%0".to_string(), "p$%1".to_string()]);
        // (p$%0 == p$%1) ∧ (p$__retval == p$%0)  — every var is interface.
        let formula = Formula::and(
            Formula::eq(int_var("p$%0"), int_var("p$%1")),
            Formula::eq(int_var("p$__retval"), int_var("p$%0")),
        );
        let projected = project_to_interface(&formula, &iface).expect("should succeed");
        // Result must mention only interface vars.  No further restriction —
        // the formula is unchanged because every variable was interface.
        assert!(find_non_interface_scalars(&projected, &iface).is_empty());
    }

    #[test]
    fn projection_substitutes_local_via_equality() {
        // Procedure `p` has one formal `p$%0` and a local `p$%1` defined
        // as `p$%1 == p$%0 + 1`.  Summary post `p$%1 > 5`.
        // Projection should substitute `p$%1` and yield `p$%0 + 1 > 5`.
        let iface = ProcedureInterface::new("p", vec!["p$%0".to_string()]);
        let formula = Formula::and(
            Formula::eq(int_var("p$%1"), Term::add(int_var("p$%0"), Term::int(1))),
            Formula::gt(int_var("p$%1"), Term::int(5)),
        );
        let projected = project_to_interface(&formula, &iface).expect("should succeed");
        assert!(
            find_non_interface_scalars(&projected, &iface).is_empty(),
            "no local should remain after substitution"
        );
    }

    #[test]
    fn projection_substitutes_chained_locals() {
        // %3 == %2 + 1, %2 == p$%0 * 2, post (%3 > 0).
        // After resolve_substitution_chain: %3 → (p$%0 * 2) + 1.
        let iface = ProcedureInterface::new("p", vec!["p$%0".to_string()]);
        let formula = Formula::and_all(vec![
            Formula::eq(int_var("p$%3"), Term::add(int_var("p$%2"), Term::int(1))),
            Formula::eq(int_var("p$%2"), Term::mul(int_var("p$%0"), Term::int(2))),
            Formula::gt(int_var("p$%3"), Term::int(0)),
        ]);
        let projected = project_to_interface(&formula, &iface).expect("should succeed");
        assert!(find_non_interface_scalars(&projected, &iface).is_empty());
    }

    #[test]
    fn projection_fails_when_local_has_no_definition() {
        // Local `p$%5` appears in a comparison but has no `Eq` definition.
        // Projection must return None.
        let iface = iface_with_no_formals("p");
        let formula = Formula::gt(int_var("p$%5"), Term::int(0));
        let projected = project_to_interface(&formula, &iface);
        assert!(
            projected.is_none(),
            "must discard summary when local can't be eliminated"
        );
    }

    #[test]
    fn projection_preserves_select_over_memory_region() {
        // `select(global$g, 0) > 0`  — `global$g` is a memory region, not a
        // scalar.  Projection must preserve verbatim regardless of formals.
        let iface = iface_with_no_formals("p");
        let formula = Formula::gt(
            Term::select(Memory::var("global$g"), Term::int(0)),
            Term::int(0),
        );
        let projected = project_to_interface(&formula, &iface).expect("should succeed");
        // Must still mention `global$g` after projection.
        assert_eq!(format!("{projected:?}"), format!("{formula:?}"));
    }

    #[test]
    fn projection_preserves_local_stack_region() {
        // Per current policy (preserve all regions), `select(p$stack0, 5) ==
        // 7` survives projection even though `p$stack0` is a local region.
        // Escape analysis (future work) can additionally drop this when
        // proven non-escaping.
        let iface = iface_with_no_formals("p");
        let formula = Formula::eq(
            Term::select(Memory::var("p$stack0"), Term::int(5)),
            Term::int(7),
        );
        let projected = project_to_interface(&formula, &iface).expect("should succeed");
        assert_eq!(format!("{projected:?}"), format!("{formula:?}"));
    }

    #[test]
    fn projection_doesnt_collect_from_under_negation() {
        // `¬(p$%1 == 5)` should NOT be treated as a definition of p$%1.
        // After projection, p$%1 is not eliminated; result is None.
        let iface = iface_with_no_formals("p");
        let formula = Formula::and(
            Formula::not(Formula::eq(int_var("p$%1"), Term::int(5))),
            Formula::gt(int_var("p$%1"), Term::int(0)),
        );
        let projected = project_to_interface(&formula, &iface);
        assert!(
            projected.is_none(),
            "equality under negation is not a definition"
        );
    }
}
