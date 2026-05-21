# SMT Layer

Two files; no other module adds raw solver calls.

## solver.rs

Lowers `Formula` and `Term` values to Z3 AST nodes via the Z3 C API. Manages
Z3 contexts and scopes. All Z3 handles are lifetime-scoped to `SmtScope`.

Key entry points:
- `SmtScope::check_sat()` — returns `Sat`, `Unsat`, or `Unknown`
- `SmtScope::get_model()` — extracts an `SmtModel` after a SAT result
- `SmtScope::assert(formula)` — adds a formula to the current scope

## oracle.rs

Policy layer over `solver.rs`. Three query shapes used by the analysis:

| Method | SMT query | Used for |
|---|---|---|
| `check_infeasible(f)` | `f` UNSAT? | `reach ∧ state` at entry → Verified |
| `check_feasible_with_model(f)` | `f` SAT? + model | `reach ∧ state` → BugFound |
| `implies(pre, post)` | `pre → post` valid? | invariant inductiveness |

`oracle.rs` also holds the `NodeSummary`-aware `check_node_infeasible` and
`check_node_feasible` helpers that the rule engine uses.

Do not add raw Z3 calls outside this module.
