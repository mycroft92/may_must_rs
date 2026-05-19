 The gap is architectural, not a small rule bug. You do not need to
  throw away the Formula/CFG representation, but you do need to
  replace the current bottom-up generic summaries + per-assertion
  local run design with the paper’s demand-driven bidirectional query
  engine.

  In one line: change the unit of work from “analyze this procedure/
  assertion with current tables” to “solve query ⟨pre ⇒ proc post⟩,
  reusing or spawning contextual subqueries at calls”.

  Conceptual Changes

  - Introduce an explicit interprocedural query object. The paper’s
    core unit is ⟨pre ⇒ procedure post⟩, not AssertionSite. Top-level
    assertions become queries with post = ¬assertion; call sites
    generate new callee queries with caller-derived pre and post.
  - Replace the current whole-module driver in driver.rs:154 with a
    demand-driven worklist of active queries. The paper starts from
    the top-level query and only analyzes callees when a call edge
    needs them.
  - Run both directions per query. The current engine in
    backward.rs:156 and backward.rs:550 is assertion-centric; it
    needs to become query-centric, with query pre seeding the forward
    must side and query post seeding the backward not-may side.
  - Make unresolved calls opaque and query-mediated. Today calls are
    effectively Nop in transfer semantics in abstract_cfg.rs:591, and
    generic return summaries are eagerly inlined into the CFG in
    adapter.rs:1194. For paper parity, call handling must move out of
    adaptation and into the query scheduler: use a matching summary
    if one applies, otherwise spawn a callee query.
  - Replace generic ReturnSummary as the main summary abstraction.
    The paper’s reusable facts are contextual MustSummary(pre, post)
    and NotMaySummary(pre, post), potentially many per procedure. The
    one-summary-per-function registry in adapter.rs:87 is not enough.
  - Implement real CREATE_MUSTSUMMARY and CREATE_NOTMAYSUMMARY from
    query results. Right now the comment in driver.rs:239 says this
    happens, but the per-procedure path in driver.rs:404 never adds
    must/not-may summaries; it only caches loop invariants at
    driver.rs:430.
  - Make summary reuse genuinely contextual. MUST_POST_USESUMMARY
    currently assumes precondition = True in rules.rs:368. For paper
    parity, reuse must check summary applicability against the
    current query context on both the pre and post sides.
  - Add summary merge/subsumption, not just exact dedup. The paper
    has MERGE_MAY_SUMMARY and MERGE_MUST_SUMMARY; current tables in
    summaries.rs:9 only dedup identical entries and do not manage
    subsumption or “this query is already covered”.
  - Preserve query-local evidence, not just “blocked edge” bits. The
    paper’s N_e is over pre/post regions and is what
    CREATE_NOTMAYSUMMARY consumes. Current blocked_edges in
    rules.rs:55 only records edge ids, which is not enough to
    reconstruct the contextual not-may summary that was learned.

  - Project summaries to the procedure interface. When you
  create a
    summary, you need to quantify away callee locals and keep
  only
    formal parameters, return value, and externally visible
  memory.
    Existing renaming/substitution utilities around
  adapter.rs:1217
    are useful, but they need to serve query translation and
  summary
    projection, not eager obligation injection.
  - Add in-progress query tracking and query subsumption for
    recursion. The paper explicitly requires checking whether a
  new
    query is already covered by an active one. The current
  recursive
    path in driver.rs:198 is CHC-based, which is a different
    algorithm, not the paper’s recursive query management.
  - Demote the current bottom-up compute_return_summary path in
    adapter.rs:1651 to an optimization, not the core algorithm.
  It is
    not the same thing as the paper’s demand-driven must/not-may
    summary discovery.
  - Keep the current loop machinery as an internal procedure
  analyzer
    if you want. The urgent mismatch is interprocedural
  orchestration
    and summary semantics, not loop invariant generation.

  If you want, I can turn this into a staged refactor plan next:
  types first (Query, QueryResult, SummaryKey, InProgressQuery),
  then
  driver/worklist, then call handling, then summary creation/
  reuse.
