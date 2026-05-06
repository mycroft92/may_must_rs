#![allow(dead_code)]

//! SMT helpers.
//!
//! The public split is intentionally narrow: `solver.rs` owns the raw Z3
//! lowering of `analysis::formula` values, while solver policy stays in
//! `analysis::oracle`. That separation mirrors the overall repo design:
//! representation and search stay in `analysis`, raw backend mechanics stay in
//! `smt`.

pub mod solver;
