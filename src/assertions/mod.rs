#![allow(dead_code)]

//! Assertion frontend utilities.
//!
//! Parsing stays outside `analysis` so sort inference and syntax concerns do
//! not leak into the paper-core modules.

pub mod exp {
    pub use crate::expressions::exp::*;
}

pub mod translation;
