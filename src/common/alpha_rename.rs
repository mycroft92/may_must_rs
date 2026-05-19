//! Alpha-renaming for formulas, terms, memory, and transfer effects.
//!
//! Every pass that copies or reinterprets symbolic names goes through this
//! module so the renaming logic is defined exactly once.
//!
//! # Two-closure design
//!
//! All entry points take two rename closures:
//!
//! - `var_rename: impl Fn(&str) -> String` — applied to scalar [`Var`] names
//!   (SSA values, local temporaries, return-value synthetics).
//! - `region_rename: impl Fn(&str) -> String` — applied to [`Memory::Var`]
//!   region names (stack regions, external regions, globals, heap sites).
//!
//! Callers choose how to treat each kind:
//!
//! | Use case | `var_rename` | `region_rename` |
//! |---|---|---|
//! | Call-summary application (`adapter.rs`) | map `callee$x` → `caller$x` | map `callee$__ext_N` → caller region |
//! | BMC iteration copy (`bmc.rs`) | append `_bmcN` suffix | identity (regions are shared state) |
//!
//! # Transfer effects
//!
//! [`rename_effect`] and [`rename_transfer_fn`] cover [`TransferEffect`] and
//! [`TransferFn`].  Only the semantically meaningful variants are renamed;
//! pointer-book-keeping effects (Alloca, GetElementPtr, Pointer*, etc.) are
//! copied verbatim because they are transparent to WP after adapter resolution.

#![allow(dead_code)]

use crate::common::abstract_cfg::{AssignValue, TransferEffect, TransferFn};
use crate::common::formula::{Formula, Memory, Term, Var};

// ---------------------------------------------------------------------------
// Core formula / term / memory
// ---------------------------------------------------------------------------

/// Rename all scalar [`Var`] and memory region names in a [`Formula`].
pub fn rename_formula<VR, MR>(f: &Formula, var_rename: VR, region_rename: MR) -> Formula
where
    VR: Fn(&str) -> String + Copy,
    MR: Fn(&str) -> String + Copy,
{
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(v) => Formula::Var(Var::new(var_rename(v.name()), v.sort())),
        Formula::Not(inner) => {
            Formula::Not(Box::new(rename_formula(inner, var_rename, region_rename)))
        }
        Formula::And(clauses) => Formula::And(
            clauses
                .iter()
                .map(|c| rename_formula(c, var_rename, region_rename))
                .collect(),
        ),
        Formula::Or(clauses) => Formula::Or(
            clauses
                .iter()
                .map(|c| rename_formula(c, var_rename, region_rename))
                .collect(),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(rename_formula(a, var_rename, region_rename)),
            Box::new(rename_formula(b, var_rename, region_rename)),
        ),
        Formula::Eq(a, b) => Formula::Eq(
            rename_term(a, var_rename, region_rename),
            rename_term(b, var_rename, region_rename),
        ),
        Formula::MemoryEq(a, b) => Formula::MemoryEq(
            rename_memory(a, var_rename, region_rename),
            rename_memory(b, var_rename, region_rename),
        ),
        Formula::Lt(a, b) => Formula::Lt(
            rename_term(a, var_rename, region_rename),
            rename_term(b, var_rename, region_rename),
        ),
        Formula::Le(a, b) => Formula::Le(
            rename_term(a, var_rename, region_rename),
            rename_term(b, var_rename, region_rename),
        ),
        Formula::Gt(a, b) => Formula::Gt(
            rename_term(a, var_rename, region_rename),
            rename_term(b, var_rename, region_rename),
        ),
        Formula::Ge(a, b) => Formula::Ge(
            rename_term(a, var_rename, region_rename),
            rename_term(b, var_rename, region_rename),
        ),
    }
}

/// Rename all scalar [`Var`] and memory region names in a [`Term`].
pub fn rename_term<VR, MR>(t: &Term, var_rename: VR, region_rename: MR) -> Term
where
    VR: Fn(&str) -> String + Copy,
    MR: Fn(&str) -> String + Copy,
{
    match t {
        Term::Var(v) => Term::Var(Var::new(var_rename(v.name()), v.sort())),
        Term::Int(i) => Term::Int(*i),
        Term::Real(r) => Term::Real(*r),
        Term::BoolToInt(f) => {
            Term::BoolToInt(Box::new(rename_formula(f, var_rename, region_rename)))
        }
        Term::Select(mem, idx) => Term::Select(
            Box::new(rename_memory(mem, var_rename, region_rename)),
            Box::new(rename_term(idx, var_rename, region_rename)),
        ),
        Term::Add(a, b) => Term::Add(
            Box::new(rename_term(a, var_rename, region_rename)),
            Box::new(rename_term(b, var_rename, region_rename)),
        ),
        Term::Sub(a, b) => Term::Sub(
            Box::new(rename_term(a, var_rename, region_rename)),
            Box::new(rename_term(b, var_rename, region_rename)),
        ),
        Term::Mul(a, b) => Term::Mul(
            Box::new(rename_term(a, var_rename, region_rename)),
            Box::new(rename_term(b, var_rename, region_rename)),
        ),
        Term::Div(a, b) => Term::Div(
            Box::new(rename_term(a, var_rename, region_rename)),
            Box::new(rename_term(b, var_rename, region_rename)),
        ),
        Term::Rem(a, b) => Term::Rem(
            Box::new(rename_term(a, var_rename, region_rename)),
            Box::new(rename_term(b, var_rename, region_rename)),
        ),
        Term::Neg(a) => Term::Neg(Box::new(rename_term(a, var_rename, region_rename))),
    }
}

/// Rename the base region name and any scalar vars inside index/value terms.
pub fn rename_memory<VR, MR>(m: &Memory, var_rename: VR, region_rename: MR) -> Memory
where
    VR: Fn(&str) -> String + Copy,
    MR: Fn(&str) -> String + Copy,
{
    match m {
        Memory::Var(name) => Memory::Var(region_rename(name)),
        Memory::Store(base, idx, val) => Memory::Store(
            Box::new(rename_memory(base, var_rename, region_rename)),
            Box::new(rename_term(idx, var_rename, region_rename)),
            Box::new(rename_term(val, var_rename, region_rename)),
        ),
    }
}

// ---------------------------------------------------------------------------
// Transfer effects
// ---------------------------------------------------------------------------

/// Rename scalar vars and memory regions in a single [`TransferEffect`].
///
/// Only semantically meaningful effects are renamed.  Pointer book-keeping
/// variants (Alloca, GetElementPtr, Pointer*, Nop, etc.) are copied verbatim
/// because they are transparent to WP after adapter resolution.
pub fn rename_effect<VR, MR>(
    effect: &TransferEffect,
    var_rename: VR,
    region_rename: MR,
) -> TransferEffect
where
    VR: Fn(&str) -> String + Copy,
    MR: Fn(&str) -> String + Copy,
{
    match effect {
        TransferEffect::Assign { target, value } => TransferEffect::Assign {
            target: Var::new(var_rename(target.name()), target.sort()),
            value: match value {
                AssignValue::Term(t) => {
                    AssignValue::Term(rename_term(t, var_rename, region_rename))
                }
                AssignValue::Predicate(f) => {
                    AssignValue::Predicate(rename_formula(f, var_rename, region_rename))
                }
            },
        },
        TransferEffect::MemoryStore {
            region,
            offset,
            value,
        } => TransferEffect::MemoryStore {
            region: region_rename(region),
            offset: rename_term(offset, var_rename, region_rename),
            value: rename_term(value, var_rename, region_rename),
        },
        TransferEffect::Assume(f) => {
            TransferEffect::Assume(rename_formula(f, var_rename, region_rename))
        }
        TransferEffect::TypeBound(f) => {
            TransferEffect::TypeBound(rename_formula(f, var_rename, region_rename))
        }
        TransferEffect::Obligation(f) => {
            TransferEffect::Obligation(rename_formula(f, var_rename, region_rename))
        }
        other => other.clone(),
    }
}

/// Rename every effect in a [`TransferFn`].
pub fn rename_transfer_fn<VR, MR>(tf: &TransferFn, var_rename: VR, region_rename: MR) -> TransferFn
where
    VR: Fn(&str) -> String + Copy,
    MR: Fn(&str) -> String + Copy,
{
    TransferFn {
        effects: tf
            .effects
            .iter()
            .map(|e| rename_effect(e, var_rename, region_rename))
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Convenience wrappers
// ---------------------------------------------------------------------------

/// Apply the same renaming function to both scalar vars and region names.
/// Used by call-summary application where all names share the same mapping.
pub fn rename_formula_uniform<R>(f: &Formula, rename: R) -> Formula
where
    R: Fn(&str) -> String + Copy,
{
    rename_formula(f, rename, rename)
}
