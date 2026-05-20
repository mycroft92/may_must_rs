# Query-Driven SMASH Refactor — Design

This document specifies the architectural rework called for by
[`../Rearch.md`](../Rearch.md): replacing the current bottom-up
per-assertion driver with a demand-driven worklist of interprocedural
queries, matching *Compositional May-Must Program Analysis* (Godefroid,
Nori, Rajamani, Tetali, PLDI 2010).

Companion documents:

- [`SMASH_FORWARD_MUST.md`](SMASH_FORWARD_MUST.md) — directional mapping
  (forward MUST = backward NOT-MAY on acyclic / BMC-unrolled CFG).
- [`LOOPS.md`](LOOPS.md) — how loop invariants interact with the query model.

**Goal:** complete equivalence with the paper, with ACHAR loop-invariant
synthesis as the only intentional addon.  Correctness comes first;
performance optimisations (such as keeping the existing eager
`compute_return_summary`) only land where they are *semantically
equivalent* to the paper's contextual summaries.

---

## 1. The query — unit of work

A **query** asks one Hoare-style question of one procedure:

> "Assuming `pre` holds at the entry of procedure `P`, is some state in
>  `post` reachable at the exit (or violation site) of `P`?"

```rust
pub struct Query {
    /// Procedure being analyzed.
    pub procedure: ProcedureName,
    /// Caller-derived precondition at the procedure entry.
    /// Formulas are over the **procedure interface variables**:
    /// formal parameters, externally visible memory regions, and
    /// (where relevant) globals.
    pub pre: Formula,
    /// Caller-derived "bad" postcondition.  For top-level assertion
    /// queries this is `¬obligation`.  For call-site queries it is the
    /// caller's projected post-state.
    pub post: Formula,
}
```

### What's NOT in the query

- No assertion-site identifier.  Assertions become initial queries with
  `post = ¬obligation`; once turned into a query, the assertion is
  irrelevant.
- No CFG handle.  The procedure name uniquely identifies the CFG; the
  scheduler looks it up.
- No direction tag.  Both directions (backward NOT-MAY, forward MUST)
  attempt to discharge every query.

### Top-level queries

For every assertion `assert(O)` at site `s` inside procedure `P`:

```
Query {
    procedure: P,
    pre: True,                                   // no caller constraints at top level
    post: WP(s.node.transfer, ¬O),               // violation pre-state of s
}
```

The WP through `s.node.transfer` is the same seed
`backward.rs::run_backward` uses today.

---

## 2. The result — what a query produces

```rust
pub enum QueryResult {
    /// `post` is NOT reachable from `pre` in this procedure.  Carries a
    /// projected `NotMaySummary` that future queries on this procedure
    /// may reuse.
    NotReachable { summary: NotMaySummary },

    /// A concrete execution from a state satisfying `pre` reaches a
    /// state satisfying `post`.  Carries a projected `MustSummary` (the
    /// concrete witness, in procedure-interface variables) and the
    /// underlying SMT model when available.
    Reachable {
        summary: MustSummary,
        witness: Option<SmtModel>,
    },

    /// The analysis could not decide either way (oracle Unknown,
    /// invariant synthesis failed, BMC budget exhausted, ...).
    Unknown,
}
```

A single query produces **at most one** `QueryResult`.  Both directions
race to discharge it; the first decisive one wins.

---

## 3. The summary table — many summaries per procedure

Today `summaries::SummaryTables` holds one `Vec<NotMaySummary>` and one
`Vec<MaySummary>` per procedure, deduplicated structurally.  The
refactor changes:

```rust
pub struct ContextualSummaryTable {
    /// Multiple contextual NotMaySummaries per procedure.  Each is
    /// keyed by the projected pre/post it was derived for.
    pub notmay: BTreeMap<ProcedureName, Vec<NotMaySummary>>,
    /// Multiple contextual MustSummaries per procedure.
    pub must: BTreeMap<ProcedureName, Vec<MustSummary>>,
    /// Loop invariants (unchanged from current SummaryTables).
    pub loop_invariants: BTreeMap<ProcedureName, Vec<(CfgNodeId, Formula)>>,
}
```

The existing `MaySummary` (renamed from `MustSummary` in v0.15.0)
remains as the over-approximate **forward-may** summary that the rules
engine consumes via `forward_may_usesummary`.  The new `MustSummary`
type below is the under-approximate paper-MUST summary.

```rust
pub struct MustSummary {
    /// Procedure-interface formula characterising the concrete
    /// pre-state from which the witness was found.
    pub precondition: Formula,
    /// Procedure-interface formula characterising the post-state the
    /// witness reaches.
    pub postcondition: Formula,
}
```

`NotMaySummary` is unchanged in shape; only the consumer needs to
honour `precondition` instead of assuming it is `True`.

---

## 4. Subsumption — when does one summary cover a query?

This is the core correctness condition.  Direction of implications is
asymmetric between NotMay and Must.

### NotMay subsumption

A `NotMaySummary { pre_s, post_s }` covers query `Q { pre_q, post_q }`
iff:

```
oracle.implies(pre_q, pre_s) == Valid    AND
oracle.implies(post_q, post_s) == Valid
```

Intuition: the summary proves "from `pre_s`, `post_s` is unreachable".
If the query's pre is *stronger* (in `pre_s`'s range) and the query's
post is *included* in `post_s`'s range, then the query's post is also
unreachable from the query's pre.  Verdict: `NotReachable`.

### Must subsumption

A `MustSummary { pre_s, post_s }` covers query `Q { pre_q, post_q }`
iff:

```
oracle.implies(pre_s, pre_q) == Valid    AND
oracle.implies(post_s, post_q) == Valid
```

Intuition: the summary witnesses "from some `pre_s` we can reach some
`post_s`".  If `pre_s` is contained in the query's pre and `post_s` is
contained in the query's post, then the witness applies to the query.
Verdict: `Reachable`.

### MERGE_MAY_SUMMARY / MERGE_MUST_SUMMARY

When `CREATE_*_SUMMARY` produces a new summary `S` for procedure `P`:

1. If any existing summary `S'` already subsumes `S` (using the same
   subsumption test as a query against `S'`), discard `S`.
2. Find existing summaries that are subsumed by `S`; remove them.
3. Insert `S`.

This keeps the table size bounded by the number of *non-subsumed*
contexts seen so far.

### Performance note

Pure SMT subsumption is expensive.  Cheaper paths to try first:

- **Structural equality** of formulas (zero SMT calls).  Covers identity
  reuse of summaries — likely the common case.
- **Syntactic implication** for atomic comparisons (e.g. `x > 5` ⇒
  `x > 0`).  Avoids SMT for simple monotone strengthening.

Fall back to the oracle only when neither shortcut applies.

---

## 5. Call handling — match summary or spawn sub-query

At a call edge `caller → callee` while analyzing caller query `Q_c`:

```
on call to `callee` with actuals `args` at call site `s`:
    caller_pre  = forward MAY state reaching `s`  (or `True`)
    caller_post = backward NOT-MAY state at `s` after the call
                   (what the caller wants to be true after return)

    callee_pre  = project_caller_to_callee(caller_pre,  args, formals)
    callee_post = project_caller_to_callee(caller_post, ret, ...)

    if exists `S` in tables.notmay[callee] subsuming Query{callee, callee_pre, callee_post}:
        apply NotMay summary to caller side (block edge or strengthen state)

    elif exists `S` in tables.must[callee] subsuming Query{callee, callee_pre, callee_post}:
        propagate Must witness into caller side; caller is also Reachable

    elif Query{callee, callee_pre, callee_post} is already in-progress:
        register `Q_c` as a dependent; defer call effect to optimistic placeholder
        (NotMay-optimistic = block edge; Must-optimistic = no contribution)

    else:
        spawn Query{callee, callee_pre, callee_post}
        register `Q_c` as a dependent
        defer call effect to optimistic placeholder
```

When the spawned callee query completes, its summary is added to the
table and all dependents are re-woken.

### Projection (caller variables ↔ callee variables)

The adapter already has the renaming machinery
(`adapter.rs:1217+`) for inlining `ReturnSummary`s.  The query refactor
re-purposes it:

- **Caller → callee** (when spawning a sub-query): rename caller actuals
  to callee formals; rename caller external regions passed by pointer
  to the callee's `__ext_N` region names.
- **Callee → caller** (when applying a returned summary): inverse
  renaming, plus existential elimination of callee-only locals if any
  appear in the projected summary.

Existential elimination is best-effort.  If a callee local cannot be
eliminated (e.g. occurs non-trivially in the summary postcondition), we
either widen to `True` for that conjunct (over-approximation, safe for
NotMay) or discard the summary (safe for Must).

---

## 6. CREATE_MUSTSUMMARY / CREATE_NOTMAYSUMMARY

When a query Q on procedure P completes with verdict V:

### V = Verified (backward NOT-MAY proves Q.post unreachable from Q.pre)

```
notmay_pre_state = engine.summary(entry).state         // WP propagated to entry
projected_pre    = project_to_interface(Q.pre, P)
projected_post   = project_to_interface(notmay_pre_state, P)
summary          = NotMaySummary {
    precondition:  projected_pre,
    postcondition: projected_post,                      // i.e. Q.post unreachable
}
MERGE_MAY_SUMMARY(P, summary)                          // additive into tables.notmay
```

### V = BugFound (concrete witness from forward MUST / BMC)

```
projected_pre  = project_to_interface(witness_entry_state, P)
projected_post = project_to_interface(witness_assertion_state, P)
summary        = MustSummary {
    precondition:  projected_pre,
    postcondition: projected_post,                      // i.e. concrete reach of bad post
}
MERGE_MUST_SUMMARY(P, summary)
```

### V = Unknown

No summary added; the query's dependents stay blocked or fall back to
their optimistic placeholders.

### Projection details

`project_to_interface(formula, procedure)`:

1. Identify procedure-interface variables: formal parameters, return
   value (`P$__retval`), externally visible regions (`P$__ext_N`),
   globals.
2. For each variable in `formula` not on the interface, attempt to
   eliminate it:
   - If it appears only in equalities `x == e` where `e` mentions only
     interface variables, substitute and drop.
   - Otherwise existentially quantify.  SMT-side `(exists ((x Int)) f)`
     is supported but may be expensive; treat as fallback.
3. Optionally simplify with the oracle (constant folding, trivial
   tautology removal).

The result is a formula over only procedure-interface variables, safe
to feed back to callers.

---

## 7. In-progress query tracking — recursion

```rust
pub struct InProgressQuery {
    pub query: Query,
    /// Queries currently blocked waiting for this one to finish.
    pub dependents: Vec<QueryId>,
    /// Optimistic placeholder verdict applied at call sites while this
    /// query is in flight.  Defaults vary by direction; see below.
    pub placeholder: PlaceholderKind,
}

pub enum PlaceholderKind {
    /// For NotMay: assume the call is safe (block the edge).  If the
    /// recursive query eventually proves NotReachable, the assumption
    /// is justified.  If not, the result is Unknown and the optimistic
    /// assumption is retracted.
    NotMayOptimistic,
    /// For Must: assume the call has no witnessable behaviour (no
    /// contribution to forward must_reach).
    MustOptimistic,
}
```

### Detecting recursion via subsumption

When the scheduler is about to spawn `Q_new`:

```
for each Q_in_progress with same procedure:
    if Q_in_progress subsumes Q_new:
        # Q_new is already covered by the active query.
        # Apply Q_in_progress's optimistic placeholder; record dependency.
        return Deferred(Q_in_progress.id)
```

Two queries on the same procedure: `Q' = {pre', post'}` subsumes
`Q = {pre, post}` iff `pre ⇒ pre'` AND `post ⇒ post'`.  Same subsumption
test as for completed NotMaySummary, applied between live queries.

### Worklist fixpoint over recursive cycles

When all queries in a recursive cycle have completed with optimistic
placeholders applied, the scheduler must verify that the placeholders
were sound:

1. Collect every dependent on every query in the cycle.
2. For each, re-run with the *actual* summaries (not placeholders).
3. If the re-run produces the same verdict, accept it.
4. If it changes (e.g. a recursive NotMay assumption is broken), demote
   the query to Unknown.

This is the paper's iterative refinement step; computationally bounded
by the number of distinct query contexts × the depth of mutual
recursion.

---

## 8. Worklist scheduler

```rust
pub struct Scheduler {
    pub pending: VecDeque<QueryId>,
    pub in_progress: HashMap<QueryId, InProgressQuery>,
    pub completed: HashMap<QueryId, QueryResult>,
    pub tables: ContextualSummaryTable,
    pub graphs: HashMap<ProcedureName, AbstractCfg>,
}

impl Scheduler {
    pub fn analyze_module(top_queries: Vec<Query>, graphs: ...) -> ModuleReport {
        for q in top_queries { self.enqueue(q); }
        while let Some(qid) = self.pending.pop_front() {
            self.dispatch(qid)?;
        }
        self.collect_results()
    }

    fn dispatch(&mut self, qid: QueryId) {
        let q = self.in_progress[&qid].query.clone();

        // Subsumption check against completed summaries.
        if let Some(result) = self.lookup_summary(&q) {
            self.complete(qid, result);
            return;
        }

        // Subsumption check against in-progress queries.
        if let Some(active) = self.find_active_covering(&q) {
            self.add_dependent(active, qid);
            return;
        }

        // Genuinely new query — run it.
        let result = self.analyze_query(&q)?;
        self.complete(qid, result);
    }

    fn analyze_query(&mut self, q: &Query) -> QueryResult {
        // Run intra-procedural analyses with q.pre and q.post as seeds.
        // - backward NOT-MAY: seed state[exit] with q.post; check
        //   `state[entry] ∧ q.pre` UNSAT → Verified.
        // - forward MUST (via backward-on-acyclic / BMC-unrolled):
        //   seed reach[entry] with q.pre; check witness at q.post.
        // At each call edge inside the procedure, consult tables or
        // spawn sub-queries; defer until they complete.
        ...
    }

    fn complete(&mut self, qid: QueryId, result: QueryResult) {
        // Add summary to tables (with MERGE_*).
        // Re-enqueue dependents.
    }
}
```

---

## 9. Mapping to existing code

| Component to add | Where |
|---|---|
| `Query`, `QueryResult`, `QueryId`, `InProgressQuery` | New `src/may_must_analysis/query.rs` |
| `ContextualSummaryTable` | Extend `summaries.rs`, retaining current types for back-compat |
| `Scheduler` | New `src/may_must_analysis/scheduler.rs` (or grow `smash.rs`) |
| Subsumption helpers (`implies` shortcuts) | `oracle.rs` (extend) and `query.rs` (high-level) |
| Projection to interface | Reuse `adapter.rs::ext_region_*` + new `project_to_interface` in `query.rs` |

| Component to demote / change | Where | Change |
|---|---|---|
| `analyze_module_with_llm` | `driver.rs:200` | Becomes a thin wrapper that builds top-level queries and calls `Scheduler::analyze_module` |
| `compute_return_summary` | `adapter.rs:1651` | Stays as optimization; when it produces a summary equivalent to `MustSummary(True, post)`, register it in the contextual table |
| `must_post_usesummary` (now `forward_may_usesummary`) | `rules.rs:368` | Honour `precondition` via implication check instead of assuming `True` |
| Loop-invariant caching | `summaries::SummaryTables::loop_invariants` | Move into `ContextualSummaryTable`; keyed by (procedure, query.post) since invariants depend on the assertion context.  See `LOOPS.md`. |

---

## 10. Implementation order

1. **Types** (`query.rs`): `Query`, `QueryResult`, `QueryId`,
   `InProgressQuery`, `ContextualSummaryTable`.  Add unit tests for the
   subsumption predicate.
2. **Projection helper** (`query.rs::project_to_interface`):
   pure, easily unit-tested.
3. **Scheduler skeleton** (`scheduler.rs`): worklist over a single
   procedure with no calls.  Wraps existing `run_backward` /
   `bmc_check`.  Produces results for top-level queries.
4. **Driver bridge**: `analyze_module_with_llm` builds top-level
   queries and delegates to `Scheduler::analyze_module`.  Verify all
   119 tests still pass.
5. **Contextual summary creation**: implement
   `CREATE_NOTMAYSUMMARY` and `CREATE_MUSTSUMMARY` at query
   completion.  Initially keep the existing `ReturnSummary` path as
   well (both coexist).
6. **Call handling**: replace the call's `Call` transfer effect with a
   scheduler-mediated lookup.  Where the existing eager
   `ReturnSummary` inlining was semantically `MustSummary(True, R)`,
   keep it as a shortcut after registering in the table.
7. **Subsumption-aware reuse**: `forward_may_usesummary` and the new
   `notmay_pre_usesummary_contextual` check the implication on `pre`.
   `MERGE_*_SUMMARY` replaces structural dedup.
8. **In-progress tracking & recursion**: in-progress map, dependency
   wake-ups, optimistic placeholders, iterative refinement on cycle
   completion.  Demote the current CHC path.
9. **Loop invariants in the query model**: see `LOOPS.md`.

Every step ends with `cargo test` green.  No commit lands until 119
tests pass.

---

## 11. Correctness checks

For each implementation step, the unit tests must include:

- **Subsumption asymmetry**: NotMay covers iff `q.pre ⇒ s.pre ∧ q.post ⇒ s.post`; Must covers iff `s.pre ⇒ q.pre ∧ s.post ⇒ q.post`.
- **Projection eliminates non-interface variables**: `project_to_interface(f, P).free_vars ⊆ interface(P)`.
- **Merge preserves invariant**: after `MERGE_*`, no two summaries in
  the table subsume each other.
- **Recursion convergence**: a contrived recursive program with mutual
  calls should terminate with the same verdict as a hand-derived
  expected outcome.
- **Equivalence to today** on the existing 119 test cases (no
  regression on assertion verdicts).
