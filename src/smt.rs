//! SMT helpers.
//!
//! The public split is intentional: solver mechanics live in `Z3Interface`,
//! while analysis-owned symbol caches live in `SmtEncodingContext`.

pub mod solver;
