//! Symbolic vocabulary for the may/must assertion checker.
//!
//! This module defines the core formula language that every analysis pass
//! speaks: sorts, variables, arithmetic terms, memory expressions, and
//! first-order Boolean formulas. All SMT queries ultimately reduce to values
//! from this module before being lowered to Z3 in [`crate::smt::solver`].
//!
//! # Design principles
//!
//! * **No solver coupling** — types here are pure Rust data structures with no
//!   Z3 handles. Conversion to solver objects happens exclusively in
//!   `smt/solver.rs`.
//! * **Flat n-ary `And`/`Or`** — conjunctions and disjunctions use `Vec`
//!   rather than binary trees so that `simplify` can flatten nested clauses
//!   in one pass and so that the solver can pass them as multi-argument
//!   `and`/`or` calls without extra wrapping.
//! * **Eager but cheap simplification** — `Formula::and`, `or`, and `implies`
//!   call `simplify` at construction time. This keeps formulas compact during
//!   WP propagation without requiring a separate normalization phase.
//! * **Memory is a separate layer** — array-of-integers memory is modelled
//!   with a dedicated [`Memory`] type rather than encoding it as an integer
//!   term, keeping the sort system simple and matching Z3's `Array Int Int`.

#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use thiserror::Error;

/// The three value domains supported by the formula language.
///
/// All variables, terms, and sub-expressions carry an explicit sort. The
/// type-checker in [`Term::sort`] and [`Formula::validate`] uses these to
/// reject ill-sorted expressions before they reach the solver.
///
/// `Bool` is only valid as a formula position or as the argument of
/// [`Term::BoolToInt`]; it cannot appear as a numeric operand.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    /// Boolean — valid in formula positions and as the source sort of `BoolToInt`.
    Bool,
    /// Unbounded mathematical integer — the default sort for program scalars.
    Int,
    /// Exact rational (used for loop-invariant coefficients and Z3 model values).
    Real,
}

/// A concrete value extracted from an SMT model (a satisfying assignment).
///
/// After a SAT query the solver returns a model mapping variables to
/// `ModelValue`s. These are used only for diagnostics and counterexample
/// display; they never feed back into analysis logic.
///
/// `ArrayDefault` represents a constant array `(as const (Array Int Int) v)`
/// — the simplest model Z3 produces for unconstrained memory regions.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ModelValue {
    /// A concrete integer value.
    Int(i64),
    /// A concrete Boolean value.
    Bool(bool),
    /// A concrete rational value (appears for `Real`-sorted variables).
    Real(Rational),
    /// A constant array whose every cell holds the wrapped default value.
    ArrayDefault(Box<ModelValue>),
}

impl fmt::Display for ModelValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModelValue::Int(value) => write!(f, "{value}"),
            ModelValue::Bool(value) => write!(f, "{value}"),
            ModelValue::Real(value) => write!(f, "{value}"),
            ModelValue::ArrayDefault(value) => write!(f, "((as const (Array Int Int)) {value})"),
        }
    }
}

/// A full satisfying assignment returned by the SMT solver.
///
/// Scalar entries bind program variables to their concrete values. Memory
/// entries bind region names (e.g. `stack0`, `fn$__ext_0`) to array
/// constants. The display format is valid SMT-LIB2 so the model can be
/// pasted directly into an interactive solver session for debugging.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SmtModel {
    /// Scalar variable bindings (Bool, Int, or Real).
    pub scalar: Vec<(Var, ModelValue)>,
    /// Memory region bindings (`Array Int Int` arrays).
    pub memory: Vec<(String, ModelValue)>,
}

impl SmtModel {
    pub fn is_empty(&self) -> bool {
        self.scalar.is_empty() && self.memory.is_empty()
    }
}

impl fmt::Display for SmtModel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (var, value) in &self.scalar {
            writeln!(f, "(define-fun {} () {} {})", var.name(), var.sort(), value)?;
        }
        for (name, value) in &self.memory {
            writeln!(f, "(define-fun {name} () (Array Int Int) {value})")?;
        }
        Ok(())
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
        }
    }
}

/// An exact rational number stored in reduced form with a positive denominator.
///
/// Used for loop-invariant template coefficients and for `Real`-sorted model
/// values returned by Z3. The denominator is always positive after
/// construction; negation is carried in the numerator. The value is kept in
/// lowest terms via GCD reduction in [`Rational::new`] so that equality and
/// ordering are unambiguous.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "rational denominator cannot be zero");
        let mut num = num;
        let mut den = den;
        if den < 0 {
            num = -num;
            den = -den;
        }
        let g = gcd(num, den);
        Self {
            num: num / g,
            den: den / g,
        }
    }

    pub fn integer(value: i64) -> Self {
        Self::new(value, 1)
    }

    pub fn numerator(&self) -> i64 {
        self.num
    }

    pub fn denominator(&self) -> i64 {
        self.den
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.num * other.den).cmp(&(other.num * self.den))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

/// A named, sorted symbolic variable.
///
/// Variables are the leaves of both [`Term`] and [`Formula`] expressions.
/// The sort is carried intrinsically so that type errors can be caught
/// during formula construction rather than only at solver time.
///
/// Names follow the LLVM IR naming convention (`%0`, `%ret`, `fn$__ext_0`,
/// etc.) after the lowering in `adapter.rs`. The name alone does not
/// determine uniqueness — two variables with the same name but different
/// sorts are distinct and represent genuinely different things.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Var {
    name: String,
    sort: Sort,
}

impl Var {
    pub fn new(name: impl Into<String>, sort: Sort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    pub fn bool(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Bool)
    }

    pub fn int(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Int)
    }

    pub fn real(name: impl Into<String>) -> Self {
        Self::new(name, Sort::Real)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// An array-of-integers memory expression (SMT `Array Int Int`).
///
/// Memory is modelled as a flat, named, integer-indexed array. Multiple
/// disjoint regions (e.g. `stack0`, `fn$__ext_0`) are represented as
/// separate `Memory::Var` roots; they never alias unless the analysis
/// explicitly equates them.
///
/// Both the index and value sorts of a `Store` must be `Int` — this is
/// checked by [`Memory::validate`].
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Memory {
    /// A named memory region — the base variable of an SMT `Array Int Int`.
    Var(String),
    /// A functional update: `(store mem idx val)` — produces a new array
    /// identical to `mem` except that cell `idx` now holds `val`. Used to
    /// encode store instructions without mutation.
    Store(Box<Memory>, Box<Term>, Box<Term>),
}

impl Memory {
    pub fn var(name: impl Into<String>) -> Self {
        Memory::Var(name.into())
    }

    pub fn store(memory: Memory, index: Term, value: Term) -> Self {
        Memory::Store(Box::new(memory), Box::new(index), Box::new(value))
    }

    pub fn validate(&self) -> Result<(), FormulaError> {
        validate_memory(self)
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Memory::Var(name) => write!(f, "{name}"),
            Memory::Store(mem, idx, val) => write!(f, "(store {mem} {idx} {val})"),
        }
    }
}

/// An arithmetic or memory-read expression that evaluates to a numeric value.
///
/// `Term`s are used wherever the analysis needs a numeric quantity: as the
/// right-hand side of an assignment, as an index into memory, or as an operand
/// of a comparison inside a [`Formula`].
///
/// The sort of a `Term` can always be computed from its structure — see
/// [`Term::sort`] — and arithmetic operations require both sides to share a
/// sort (Int or Real; never Bool).
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    /// A named variable (must have `Sort::Int` or `Sort::Real`).
    Var(Var),
    /// A literal integer constant.
    Int(i64),
    /// A literal rational constant (used in Real-sorted arithmetic).
    Real(Rational),
    /// Coerces a Boolean formula to an integer (0 or 1). Useful for encoding
    /// indicator variables from conditional branches into arithmetic contexts.
    BoolToInt(Box<Formula>),
    /// Array read: `(select mem idx)` — reads cell `idx` of region `mem`.
    /// Both the index and the resulting value have sort `Int`.
    Select(Box<Memory>, Box<Term>),
    /// Integer/real addition.
    Add(Box<Term>, Box<Term>),
    /// Integer/real subtraction.
    Sub(Box<Term>, Box<Term>),
    /// Integer/real multiplication.
    Mul(Box<Term>, Box<Term>),
    /// Integer/real division (truncating for integers, exact for reals).
    Div(Box<Term>, Box<Term>),
    /// Integer remainder. Operands must be `Int`-sorted.
    Rem(Box<Term>, Box<Term>),
    /// Arithmetic negation.
    Neg(Box<Term>),
}

impl Term {
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Term::Var(Var::new(name, sort))
    }

    pub fn int(value: i64) -> Self {
        Term::Int(value)
    }

    pub fn real(value: Rational) -> Self {
        Term::Real(value)
    }

    pub fn bool_to_int(value: Formula) -> Self {
        Term::BoolToInt(Box::new(value))
    }

    pub fn select(memory: Memory, index: Term) -> Self {
        Term::Select(Box::new(memory), Box::new(index))
    }

    pub fn add(lhs: Term, rhs: Term) -> Self {
        Term::Add(Box::new(lhs), Box::new(rhs))
    }

    pub fn sub(lhs: Term, rhs: Term) -> Self {
        Term::Sub(Box::new(lhs), Box::new(rhs))
    }

    pub fn mul(lhs: Term, rhs: Term) -> Self {
        Term::Mul(Box::new(lhs), Box::new(rhs))
    }

    pub fn div(lhs: Term, rhs: Term) -> Self {
        Term::Div(Box::new(lhs), Box::new(rhs))
    }

    pub fn rem(lhs: Term, rhs: Term) -> Self {
        Term::Rem(Box::new(lhs), Box::new(rhs))
    }

    pub fn neg(inner: Term) -> Self {
        Term::Neg(Box::new(inner))
    }

    /// Evaluate this term to a constant integer if every sub-term is a literal.
    /// Returns `None` for any term that contains variables, memory selects, or
    /// boolean coercions.  Useful for constant-folding GEP offsets.
    pub fn try_as_constant_int(&self) -> Option<i64> {
        match self {
            Term::Int(n) => Some(*n),
            Term::Add(l, r) => Some(l.try_as_constant_int()? + r.try_as_constant_int()?),
            Term::Sub(l, r) => Some(l.try_as_constant_int()? - r.try_as_constant_int()?),
            Term::Mul(l, r) => Some(l.try_as_constant_int()? * r.try_as_constant_int()?),
            Term::Div(l, r) => {
                let d = r.try_as_constant_int()?;
                if d == 0 {
                    return None;
                }
                Some(l.try_as_constant_int()? / d)
            }
            Term::Rem(l, r) => {
                let d = r.try_as_constant_int()?;
                if d == 0 {
                    return None;
                }
                Some(l.try_as_constant_int()? % d)
            }
            Term::Neg(inner) => Some(-inner.try_as_constant_int()?),
            _ => None,
        }
    }

    pub fn sort(&self) -> Result<Sort, FormulaError> {
        match self {
            Term::Var(var) => Ok(var.sort()),
            Term::Int(_) => Ok(Sort::Int),
            Term::Real(_) => Ok(Sort::Real),
            Term::BoolToInt(value) => {
                value.validate()?;
                Ok(Sort::Int)
            }
            Term::Select(_, index) => {
                let index_sort = index.sort()?;
                if index_sort != Sort::Int {
                    return Err(FormulaError::ExpectedIntegerSort { found: index_sort });
                }
                Ok(Sort::Int)
            }
            Term::Add(lhs, rhs)
            | Term::Sub(lhs, rhs)
            | Term::Mul(lhs, rhs)
            | Term::Div(lhs, rhs)
            | Term::Rem(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    return Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    });
                }
                if lhs_sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(lhs_sort)
            }
            Term::Neg(inner) => {
                let sort = inner.sort()?;
                if sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(sort)
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(var) => write!(f, "{var}"),
            Term::Int(value) => write!(f, "{value}"),
            Term::Real(value) => write!(f, "{value}"),
            Term::BoolToInt(value) => write!(f, "bool_to_int({value})"),
            Term::Select(memory, index) => write!(f, "(select {memory} {index})"),
            Term::Add(lhs, rhs) => write!(f, "({lhs} + {rhs})"),
            Term::Sub(lhs, rhs) => write!(f, "({lhs} - {rhs})"),
            Term::Mul(lhs, rhs) => write!(f, "({lhs} * {rhs})"),
            Term::Div(lhs, rhs) => write!(f, "({lhs} / {rhs})"),
            Term::Rem(lhs, rhs) => write!(f, "({lhs} % {rhs})"),
            Term::Neg(inner) => write!(f, "(-{inner})"),
        }
    }
}

/// A first-order Boolean formula over scalar variables and memory.
///
/// Formulas appear in three roles in the analysis:
/// 1. **Reach predicates** — overapproximations of reachable states (forward
///    direction). Loop invariants are injected here at loop headers.
/// 2. **State predicates** — the WP of `NOT obligation`, propagated backward
///    through the CFG to capture violation conditions.
/// 3. **Guards and obligations** — edge guards and `Obligation` effects
///    inside [`TransferFn`](crate::common::abstract_cfg::TransferFn).
///
/// The `And` and `Or` variants are n-ary (backed by a `Vec`) rather than
/// binary so that `simplify` can flatten nested conjunctions or disjunctions
/// cheaply and the solver can receive them as variadic calls. Constructors
/// like [`Formula::and`] and [`Formula::or`] always call `simplify`, so
/// `And([])` (vacuous true) and `Or([])` (vacuous false) only appear
/// transiently inside `simplify` itself.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Formula {
    /// The tautology — absorber for conjunction, identity for disjunction.
    True,
    /// The contradiction — identity for conjunction, absorber for disjunction.
    False,
    /// A Boolean-sorted variable (sort must be `Sort::Bool`; checked by `validate`).
    Var(Var),
    /// Logical negation.
    Not(Box<Formula>),
    /// N-ary conjunction. Empty = `True`; singleton is simplified away by constructors.
    And(Vec<Formula>),
    /// N-ary disjunction. Empty = `False`; singleton is simplified away by constructors.
    Or(Vec<Formula>),
    /// Material implication `lhs => rhs`.
    Implies(Box<Formula>, Box<Formula>),
    /// Numeric (or memory-indirect) equality of two same-sorted terms.
    /// `Bool`-sorted `Eq` is rejected by `validate` — use `Var` or `Implies` instead.
    Eq(Term, Term),
    /// Array equality between two memory expressions (`mem1 == mem2`).
    MemoryEq(Memory, Memory),
    /// Strict numeric less-than.
    Lt(Term, Term),
    /// Numeric less-than-or-equal.
    Le(Term, Term),
    /// Strict numeric greater-than.
    Gt(Term, Term),
    /// Numeric greater-than-or-equal.
    Ge(Term, Term),
}

impl Formula {
    pub fn bool_var(name: impl Into<String>) -> Self {
        Formula::Var(Var::bool(name))
    }

    pub fn not(inner: Formula) -> Self {
        Formula::Not(Box::new(inner))
    }

    pub fn and(lhs: Formula, rhs: Formula) -> Self {
        Formula::And(vec![lhs, rhs]).simplify()
    }

    pub fn and_many(items: impl IntoIterator<Item = Formula>) -> Self {
        Formula::And(items.into_iter().collect()).simplify()
    }

    pub fn and_all(items: impl IntoIterator<Item = Formula>) -> Self {
        Self::and_many(items)
    }

    pub fn or(lhs: Formula, rhs: Formula) -> Self {
        Formula::Or(vec![lhs, rhs]).simplify()
    }

    pub fn or_many(items: impl IntoIterator<Item = Formula>) -> Self {
        Formula::Or(items.into_iter().collect()).simplify()
    }

    pub fn or_all(items: impl IntoIterator<Item = Formula>) -> Self {
        Self::or_many(items)
    }

    pub fn implies(lhs: Formula, rhs: Formula) -> Self {
        Formula::Implies(Box::new(lhs), Box::new(rhs)).simplify()
    }

    pub fn iff(lhs: Formula, rhs: Formula) -> Self {
        Formula::and(
            Formula::implies(lhs.clone(), rhs.clone()),
            Formula::implies(rhs, lhs),
        )
    }

    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Formula::Eq(lhs, rhs)
    }

    pub fn memory_eq(lhs: Memory, rhs: Memory) -> Self {
        Formula::MemoryEq(lhs, rhs)
    }

    pub fn lt(lhs: Term, rhs: Term) -> Self {
        Formula::Lt(lhs, rhs)
    }

    pub fn le(lhs: Term, rhs: Term) -> Self {
        Formula::Le(lhs, rhs)
    }

    pub fn gt(lhs: Term, rhs: Term) -> Self {
        Formula::Gt(lhs, rhs)
    }

    pub fn ge(lhs: Term, rhs: Term) -> Self {
        Formula::Ge(lhs, rhs)
    }

    pub fn validate(&self) -> Result<(), FormulaError> {
        match self {
            Formula::True | Formula::False => Ok(()),
            Formula::Var(var) => {
                if var.sort() != Sort::Bool {
                    Err(FormulaError::ExpectedBooleanSort { found: var.sort() })
                } else {
                    Ok(())
                }
            }
            Formula::Not(inner) => inner.validate(),
            Formula::And(items) | Formula::Or(items) => {
                for item in items {
                    item.validate()?;
                }
                Ok(())
            }
            Formula::Implies(lhs, rhs) => {
                lhs.validate()?;
                rhs.validate()?;
                Ok(())
            }
            Formula::Eq(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    })
                } else if lhs_sort == Sort::Bool {
                    Err(FormulaError::ExpectedNumericSort { found: Sort::Bool })
                } else {
                    Ok(())
                }
            }
            Formula::MemoryEq(lhs, rhs) => {
                validate_memory(lhs)?;
                validate_memory(rhs)?;
                Ok(())
            }
            Formula::Lt(lhs, rhs)
            | Formula::Le(lhs, rhs)
            | Formula::Gt(lhs, rhs)
            | Formula::Ge(lhs, rhs) => {
                let lhs_sort = lhs.sort()?;
                let rhs_sort = rhs.sort()?;
                if lhs_sort != rhs_sort {
                    return Err(FormulaError::MixedSorts {
                        left: lhs_sort,
                        right: rhs_sort,
                    });
                }
                if lhs_sort == Sort::Bool {
                    return Err(FormulaError::ExpectedNumericSort { found: Sort::Bool });
                }
                Ok(())
            }
        }
    }

    pub fn substitute(&self, mapping: HashMap<Var, Var>) -> Formula {
        substitute_formula_vars(self, &mapping)
    }

    fn simplify(self) -> Self {
        match self {
            Formula::And(items) => {
                let mut flat = Vec::new();
                for item in items {
                    match item {
                        Formula::True => {}
                        Formula::False => return Formula::False,
                        Formula::And(inner) => {
                            for item in inner {
                                if !flat.contains(&item) {
                                    flat.push(item);
                                }
                            }
                        }
                        other => {
                            if !flat.contains(&other) {
                                flat.push(other);
                            }
                        }
                    }
                }
                if flat.is_empty() {
                    Formula::True
                } else if flat.len() == 1 {
                    flat.into_iter().next().unwrap()
                } else {
                    Formula::And(flat)
                }
            }
            Formula::Or(items) => {
                let mut flat = Vec::new();
                for item in items {
                    match item {
                        Formula::False => {}
                        Formula::True => return Formula::True,
                        Formula::Or(inner) => {
                            for item in inner {
                                if !flat.contains(&item) {
                                    flat.push(item);
                                }
                            }
                        }
                        other => {
                            if !flat.contains(&other) {
                                flat.push(other);
                            }
                        }
                    }
                }
                if flat.is_empty() {
                    Formula::False
                } else if flat.len() == 1 {
                    flat.into_iter().next().unwrap()
                } else {
                    Formula::Or(flat)
                }
            }
            Formula::Implies(lhs, rhs) => {
                if matches!(*lhs, Formula::False) || matches!(*rhs, Formula::True) {
                    Formula::True
                } else if matches!(*lhs, Formula::True) {
                    *rhs
                } else {
                    Formula::Implies(lhs, rhs)
                }
            }
            other => other,
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Var(var) => write!(f, "{var}"),
            Formula::Not(inner) => write!(f, "(!{inner})"),
            Formula::And(items) => write_joined(f, " && ", items),
            Formula::Or(items) => write_joined(f, " || ", items),
            Formula::Implies(lhs, rhs) => write!(f, "({lhs} => {rhs})"),
            Formula::Eq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
            Formula::MemoryEq(lhs, rhs) => write!(f, "({lhs} == {rhs})"),
            Formula::Lt(lhs, rhs) => write!(f, "({lhs} < {rhs})"),
            Formula::Le(lhs, rhs) => write!(f, "({lhs} <= {rhs})"),
            Formula::Gt(lhs, rhs) => write!(f, "({lhs} > {rhs})"),
            Formula::Ge(lhs, rhs) => write!(f, "({lhs} >= {rhs})"),
        }
    }
}

// ---------------------------------------------------------------------------
// Human-readable display with source variable name substitution
// ---------------------------------------------------------------------------
//
// These methods substitute abstract region names (e.g. `main$stack0`) with
// source variable names from LLVM debug info (e.g. `array`) so that
// invariants, candidates, and reach/state formulas can be inspected more
// easily during development.  The `names` map is produced by the adapter from
// `#dbg_declare` records; it is empty when compiled without `-g`.

impl Memory {
    pub fn pretty(&self, names: &HashMap<String, String>) -> String {
        match self {
            Memory::Var(region) => names.get(region).cloned().unwrap_or_else(|| region.clone()),
            Memory::Store(mem, idx, val) => {
                format!(
                    "(store {} {} {})",
                    mem.pretty(names),
                    idx.pretty(names),
                    val.pretty(names)
                )
            }
        }
    }
}

impl Term {
    pub fn pretty(&self, names: &HashMap<String, String>) -> String {
        match self {
            Term::Select(memory, index) => match memory.as_ref() {
                Memory::Var(region) => {
                    let src = names.get(region).map(|s| s.as_str()).unwrap_or(region);
                    format!("{src}[{}]", index.pretty(names))
                }
                other => format!("(select {} {})", other.pretty(names), index.pretty(names)),
            },
            Term::Var(var) => {
                // Strip function-name prefix (e.g. `main$%j` → `j`).
                let n = &var.name;
                if let Some(pos) = n.rfind("$%") {
                    n[pos + 2..].to_string()
                } else if let Some(pos) = n.rfind('$') {
                    n[pos + 1..].to_string()
                } else {
                    n.clone()
                }
            }
            Term::Int(v) => v.to_string(),
            Term::Real(v) => v.to_string(),
            Term::BoolToInt(f) => format!("bool_to_int({})", f.pretty(names)),
            Term::Add(l, r) => format!("({} + {})", l.pretty(names), r.pretty(names)),
            Term::Sub(l, r) => format!("({} - {})", l.pretty(names), r.pretty(names)),
            Term::Mul(l, r) => format!("({} * {})", l.pretty(names), r.pretty(names)),
            Term::Div(l, r) => format!("({} / {})", l.pretty(names), r.pretty(names)),
            Term::Rem(l, r) => format!("({} % {})", l.pretty(names), r.pretty(names)),
            Term::Neg(inner) => format!("(-{})", inner.pretty(names)),
        }
    }
}

impl Formula {
    pub fn pretty(&self, names: &HashMap<String, String>) -> String {
        match self {
            Formula::True => "true".to_string(),
            Formula::False => "false".to_string(),
            Formula::Var(var) => var.name.clone(),
            Formula::Not(inner) => format!("(!{})", inner.pretty(names)),
            Formula::And(items) => {
                let parts: Vec<_> = items.iter().map(|f| f.pretty(names)).collect();
                format!("({})", parts.join(" && "))
            }
            Formula::Or(items) => {
                let parts: Vec<_> = items.iter().map(|f| f.pretty(names)).collect();
                format!("({})", parts.join(" || "))
            }
            Formula::Implies(l, r) => format!("({} => {})", l.pretty(names), r.pretty(names)),
            Formula::Eq(l, r) => format!("({} == {})", l.pretty(names), r.pretty(names)),
            Formula::MemoryEq(l, r) => {
                format!("({} == {})", l.pretty(names), r.pretty(names))
            }
            Formula::Lt(l, r) => format!("({} < {})", l.pretty(names), r.pretty(names)),
            Formula::Le(l, r) => format!("({} <= {})", l.pretty(names), r.pretty(names)),
            Formula::Gt(l, r) => format!("({} > {})", l.pretty(names), r.pretty(names)),
            Formula::Ge(l, r) => format!("({} >= {})", l.pretty(names), r.pretty(names)),
        }
    }
}

fn validate_memory(memory: &Memory) -> Result<(), FormulaError> {
    match memory {
        Memory::Var(_) => Ok(()),
        Memory::Store(inner, index, value) => {
            validate_memory(inner)?;
            let index_sort = index.sort()?;
            let value_sort = value.sort()?;
            if index_sort != Sort::Int {
                return Err(FormulaError::ExpectedIntegerSort { found: index_sort });
            }
            if value_sort != Sort::Int {
                return Err(FormulaError::ExpectedIntegerSort { found: value_sort });
            }
            Ok(())
        }
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    let mut a = a.abs();
    let mut b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 {
        1
    } else {
        a
    }
}

fn write_joined(f: &mut fmt::Formatter<'_>, sep: &str, items: &[Formula]) -> fmt::Result {
    write!(f, "(")?;
    for (idx, item) in items.iter().enumerate() {
        if idx > 0 {
            write!(f, "{sep}")?;
        }
        write!(f, "{item}")?;
    }
    write!(f, ")")
}

fn substitute_formula_vars(formula: &Formula, mapping: &HashMap<Var, Var>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(mapping.get(var).cloned().unwrap_or_else(|| var.clone())),
        Formula::Not(inner) => Formula::not(substitute_formula_vars(inner, mapping)),
        Formula::And(items) => Formula::and_all(
            items
                .iter()
                .map(|item| substitute_formula_vars(item, mapping)),
        ),
        Formula::Or(items) => Formula::or_all(
            items
                .iter()
                .map(|item| substitute_formula_vars(item, mapping)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_formula_vars(lhs, mapping),
            substitute_formula_vars(rhs, mapping),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_memory_vars(lhs, mapping),
            substitute_memory_vars(rhs, mapping),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
    }
}

fn substitute_term_vars(term: &Term, mapping: &HashMap<Var, Var>) -> Term {
    match term {
        Term::Var(var) => Term::Var(mapping.get(var).cloned().unwrap_or_else(|| var.clone())),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(inner) => Term::bool_to_int(substitute_formula_vars(inner, mapping)),
        Term::Select(memory, index) => Term::select(
            substitute_memory_vars(memory, mapping),
            substitute_term_vars(index, mapping),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Term::Rem(lhs, rhs) => Term::rem(
            substitute_term_vars(lhs, mapping),
            substitute_term_vars(rhs, mapping),
        ),
        Term::Neg(inner) => Term::neg(substitute_term_vars(inner, mapping)),
    }
}

fn substitute_memory_vars(memory: &Memory, mapping: &HashMap<Var, Var>) -> Memory {
    match memory {
        Memory::Var(name) => Memory::var(name),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_memory_vars(inner, mapping),
            substitute_term_vars(index, mapping),
            substitute_term_vars(value, mapping),
        ),
    }
}

/// Collect all integer literal indices used in `(select mem idx)` expressions
/// inside `formula`, deduplicated and sorted.
///
/// Used during quantifier-free array reasoning to enumerate the concrete
/// offsets that must be "instantiated" when checking memory-related invariants.
/// Non-literal index expressions are silently skipped — only `Term::Int`
/// constants are returned.
pub fn collect_select_indices(formula: &Formula) -> Vec<i64> {
    let mut indices = Vec::new();
    collect_select_indices_formula(formula, &mut indices);
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn collect_select_indices_formula(formula: &Formula, indices: &mut Vec<i64>) {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => {}
        Formula::Not(inner) => collect_select_indices_formula(inner, indices),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_select_indices_formula(item, indices);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_select_indices_formula(lhs, indices);
            collect_select_indices_formula(rhs, indices);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_select_indices_term(lhs, indices);
            collect_select_indices_term(rhs, indices);
        }
        Formula::MemoryEq(lhs, rhs) => {
            collect_select_indices_memory(lhs, indices);
            collect_select_indices_memory(rhs, indices);
        }
    }
}

fn collect_select_indices_term(term: &Term, indices: &mut Vec<i64>) {
    match term {
        Term::Var(_) | Term::Int(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_select_indices_formula(inner, indices),
        Term::Select(memory, index) => {
            collect_select_indices_memory(memory, indices);
            if let Term::Int(value) = index.as_ref() {
                indices.push(*value);
            }
            collect_select_indices_term(index, indices);
        }
        Term::Add(lhs, rhs)
        | Term::Sub(lhs, rhs)
        | Term::Mul(lhs, rhs)
        | Term::Div(lhs, rhs)
        | Term::Rem(lhs, rhs) => {
            collect_select_indices_term(lhs, indices);
            collect_select_indices_term(rhs, indices);
        }
        Term::Neg(inner) => collect_select_indices_term(inner, indices),
    }
}

fn collect_select_indices_memory(memory: &Memory, indices: &mut Vec<i64>) {
    match memory {
        Memory::Var(_) => {}
        Memory::Store(inner, index, value) => {
            collect_select_indices_memory(inner, indices);
            collect_select_indices_term(index, indices);
            collect_select_indices_term(value, indices);
        }
    }
}

/// Collect all memory region names (`Memory::Var`) referenced anywhere in `formula`.
///
/// Used by the loop-relevance pre-filter in `precomputed_satisfy_exit_closure` to
/// decide whether a loop's writes can affect the exit postcondition without running
/// the full exit-closure SMT query.
pub fn collect_memory_region_names(formula: &Formula) -> std::collections::BTreeSet<String> {
    let mut names = std::collections::BTreeSet::new();
    collect_region_names_formula(formula, &mut names);
    names
}

fn collect_region_names_formula(formula: &Formula, out: &mut std::collections::BTreeSet<String>) {
    match formula {
        Formula::True | Formula::False | Formula::Var(_) => {}
        Formula::Not(inner) => collect_region_names_formula(inner, out),
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_region_names_formula(item, out);
            }
        }
        Formula::Implies(lhs, rhs) => {
            collect_region_names_formula(lhs, out);
            collect_region_names_formula(rhs, out);
        }
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => {
            collect_region_names_term(lhs, out);
            collect_region_names_term(rhs, out);
        }
        Formula::MemoryEq(lhs, rhs) => {
            collect_region_names_memory(lhs, out);
            collect_region_names_memory(rhs, out);
        }
    }
}

fn collect_region_names_term(term: &Term, out: &mut std::collections::BTreeSet<String>) {
    match term {
        Term::Var(_) | Term::Int(_) | Term::Real(_) => {}
        Term::BoolToInt(inner) => collect_region_names_formula(inner, out),
        Term::Select(memory, index) => {
            collect_region_names_memory(memory, out);
            collect_region_names_term(index, out);
        }
        Term::Add(lhs, rhs)
        | Term::Sub(lhs, rhs)
        | Term::Mul(lhs, rhs)
        | Term::Div(lhs, rhs)
        | Term::Rem(lhs, rhs) => {
            collect_region_names_term(lhs, out);
            collect_region_names_term(rhs, out);
        }
        Term::Neg(inner) => collect_region_names_term(inner, out),
    }
}

fn collect_region_names_memory(memory: &Memory, out: &mut std::collections::BTreeSet<String>) {
    match memory {
        Memory::Var(name) => {
            out.insert(name.clone());
        }
        Memory::Store(inner, index, value) => {
            collect_region_names_memory(inner, out);
            collect_region_names_term(index, out);
            collect_region_names_term(value, out);
        }
    }
}

/// Errors produced by formula sort-checking ([`Formula::validate`], [`Term::sort`]).
///
/// These errors indicate a programming mistake in formula construction — they
/// should not arise at runtime on well-typed LLVM IR after lowering.
#[derive(Debug, Error, Clone, Eq, PartialEq)]
pub enum FormulaError {
    #[error("expected Boolean sort, found {found}")]
    ExpectedBooleanSort { found: Sort },
    #[error("expected numeric sort, found {found}")]
    ExpectedNumericSort { found: Sort },
    #[error("expected integer sort, found {found}")]
    ExpectedIntegerSort { found: Sort },
    #[error("mixed sorts: {left} vs {right}")]
    MixedSorts { left: Sort, right: Sort },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rational_is_reduced() {
        let value = Rational::new(6, 8);
        assert_eq!(value.numerator(), 3);
        assert_eq!(value.denominator(), 4);
    }

    #[test]
    fn boolean_var_validation_rejects_non_bool() {
        let formula = Formula::Var(Var::int("x"));
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::ExpectedBooleanSort { .. })
        ));
    }

    #[test]
    fn numeric_equality_requires_matching_sorts() {
        let formula = Formula::eq(Term::int(1), Term::real(Rational::integer(1)));
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::MixedSorts { .. })
        ));
    }

    #[test]
    fn logical_simplification_shortcuts() {
        let formula = Formula::and(Formula::True, Formula::bool_var("p"));
        assert_eq!(formula, Formula::bool_var("p"));
    }

    #[test]
    fn memory_store_requires_integer_index_and_value() {
        let formula = Formula::memory_eq(
            Memory::store(
                Memory::var("m"),
                Term::real(Rational::new(1, 2)),
                Term::int(3),
            ),
            Memory::var("m"),
        );
        assert!(matches!(
            formula.validate(),
            Err(FormulaError::ExpectedIntegerSort { .. })
        ));
    }

    #[test]
    fn display_is_stable() {
        let formula = Formula::implies(
            Formula::bool_var("a"),
            Formula::eq(Term::var("x", Sort::Int), Term::int(4)),
        );
        assert_eq!(formula.to_string(), "(a => (x == 4))");
    }

    #[test]
    fn bool_to_int_is_integer_sorted() {
        assert_eq!(
            Term::bool_to_int(Formula::bool_var("b")).sort(),
            Ok(Sort::Int)
        );
    }
}
