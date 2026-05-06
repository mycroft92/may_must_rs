#![allow(dead_code)]

//! Assertion frontend utilities.
//!
//! Parsing and frontend sort recovery stay outside `analysis` so syntax and
//! user-facing assertion concerns do not leak into the paper-core modules.
//! `translation.rs` is the bridge from this frontend world into
//! `analysis::formula`.

pub mod exp {
    pub use crate::expressions::exp::*;
}

pub mod translation;
