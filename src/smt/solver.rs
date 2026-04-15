//! Thin wrapper around the `z3` crate.
//!
//! Current status in this repository:
//!
//! - `Z3Interface` owns only the solver and low-level Z3 operations.
//! - `SmtEncodingContext` owns analysis-level symbols and caches Z3 variables.
//! - The SMASH prototype in `analysis::may_must` does not yet invoke this
//!   wrapper when deciding summaries, path feasibility, or predicate
//!   implication. Those decisions are currently concrete/syntactic.
//! - The existing calls to this wrapper are unit tests in this file. They show
//!   the intended call pattern: create `SmtEncodingContext`, create analysis
//!   symbols, assert constraints through the embedded solver, call `check`,
//!   then optionally read model values for the context-owned symbols.
//!
//! Paper mapping: Section 5.1 says the original SMASH implementation stores
//! predicates in Z3 and uses theorem-prover queries for satisfiability and
//! validity over linear arithmetic and uninterpreted functions. This file is
//! the local hook for that future integration. Solver mechanics stay here;
//! symbol identity should stay with the analysis encoding layer.

use std::collections::HashMap;
use z3::ast::{Array, Bool, Int, Real, BV};
use z3::{Model, RecFuncDecl, SatResult, Solver, Sort, Symbol};

pub struct Z3Interface {
    pub solver: Solver,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SymbolId {
    name: String,
}

impl SymbolId {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }

    pub fn as_str(&self) -> &str {
        &self.name
    }
}

impl From<&str> for SymbolId {
    fn from(value: &str) -> Self {
        SymbolId::new(value)
    }
}

impl From<String> for SymbolId {
    fn from(value: String) -> Self {
        SymbolId::new(value)
    }
}

pub struct SmtEncodingContext {
    pub z3: Z3Interface,
    pub int_vars: HashMap<String, Int>,
    pub bool_vars: HashMap<String, Bool>,
    pub real_vars: HashMap<String, Real>,
    pub bv_vars: HashMap<String, BV>,
    pub array_vars: HashMap<String, Array>,
    pub uninterpreted_funcs: HashMap<String, RecFuncDecl>,
    pub sorts: HashMap<String, Sort>,
}

impl Z3Interface {
    /// Create a new thin solver interface.
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
        }
    }

    /// Add a constraint to the solver.
    pub fn assert(&mut self, constraint: &Bool) {
        self.solver.assert(constraint);
    }

    /// Check satisfiability.
    pub fn check(&self) -> z3::SatResult {
        self.solver.check()
    }

    /// Get the model if satisfiable.
    pub fn get_model(&self) -> Option<Model> {
        self.solver.get_model()
    }

    /// Push a new assertion scope.
    pub fn push(&mut self) {
        self.solver.push();
    }

    /// Pop assertion scopes.
    pub fn pop(&mut self, n: u32) {
        self.solver.pop(n);
    }

    /// Reset the solver.
    pub fn reset(&mut self) {
        self.solver.reset();
    }

    /// Get the solver.
    pub fn solver(&self) -> &Solver {
        &self.solver
    }

    /// Get mutable solver reference.
    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }

    /// Create an integer constant.
    pub fn int_const(&self, value: i64) -> Int {
        Int::from_i64(value)
    }

    /// Create a boolean constant.
    pub fn bool_const(&self, value: bool) -> Bool {
        Bool::from_bool(value)
    }

    /// Create a real constant from numerator and denominator.
    pub fn real_const(&self, num: i32, den: i32) -> Real {
        Real::from_rational(num.into(), den.into())
    }

    /// Create a bitvector constant.
    pub fn bv_const(&self, value: i64, size: u32) -> BV {
        BV::from_i64(value, size)
    }

    /// Get integer sort.
    pub fn int_sort(&self) -> Sort {
        Sort::int()
    }

    /// Get boolean sort.
    pub fn bool_sort(&self) -> Sort {
        Sort::bool()
    }

    /// Get real sort.
    pub fn real_sort(&self) -> Sort {
        Sort::real()
    }

    /// Get bitvector sort.
    pub fn bv_sort(&self, size: u32) -> Sort {
        Sort::bitvector(size)
    }

    /// Get array sort.
    pub fn array_sort(&self, domain: &Sort, range: &Sort) -> Sort {
        Sort::array(domain, range)
    }
}

impl Default for Z3Interface {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtEncodingContext {
    /// Create a query/path/summary encoding context.
    ///
    /// This is the layer that owns analysis symbol identity. Future SMASH
    /// integration should create one of these for a query or path and use
    /// `SymbolId`s that encode function, pre/post phase, and versioning.
    pub fn new() -> Self {
        Self {
            z3: Z3Interface::new(),
            int_vars: HashMap::new(),
            bool_vars: HashMap::new(),
            real_vars: HashMap::new(),
            bv_vars: HashMap::new(),
            array_vars: HashMap::new(),
            uninterpreted_funcs: HashMap::new(),
            sorts: HashMap::new(),
        }
    }

    /// Get or create an integer variable owned by this encoding context.
    pub fn int_var(&mut self, symbol: impl Into<SymbolId>) -> Int {
        let symbol = symbol.into();
        let name = symbol.as_str();
        if let Some(var) = self.int_vars.get(name) {
            var.clone()
        } else {
            let var = Int::new_const(name);
            self.int_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh integer variable with a context-local unique name.
    pub fn fresh_int_var(&mut self, prefix: &str) -> Int {
        let name = format!("{}_{}", prefix, self.int_vars.len());
        self.int_var(name)
    }

    /// Get or create a boolean variable owned by this encoding context.
    pub fn bool_var(&mut self, symbol: impl Into<SymbolId>) -> Bool {
        let symbol = symbol.into();
        let name = symbol.as_str();
        if let Some(var) = self.bool_vars.get(name) {
            var.clone()
        } else {
            let var = Bool::new_const(name);
            self.bool_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh boolean variable with a context-local unique name.
    pub fn fresh_bool_var(&mut self, prefix: &str) -> Bool {
        let name = format!("{}_{}", prefix, self.bool_vars.len());
        self.bool_var(name)
    }

    /// Get or create a real variable owned by this encoding context.
    pub fn real_var(&mut self, symbol: impl Into<SymbolId>) -> Real {
        let symbol = symbol.into();
        let name = symbol.as_str();
        if let Some(var) = self.real_vars.get(name) {
            var.clone()
        } else {
            let var = Real::new_const(name);
            self.real_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh real variable with a context-local unique name.
    pub fn fresh_real_var(&mut self, prefix: &str) -> Real {
        let name = format!("{}_{}", prefix, self.real_vars.len());
        self.real_var(name)
    }

    /// Get or create a bitvector variable owned by this encoding context.
    pub fn bv_var(&mut self, symbol: impl Into<SymbolId>, size: u32) -> BV {
        let symbol = symbol.into();
        let name = symbol.as_str();
        let key = format!("{}_{}", name, size);
        if let Some(var) = self.bv_vars.get(&key) {
            var.clone()
        } else {
            let var = BV::new_const(name, size);
            self.bv_vars.insert(key, var.clone());
            var
        }
    }

    /// Create a fresh bitvector variable with a context-local unique name.
    pub fn fresh_bv_var(&mut self, prefix: &str, size: u32) -> BV {
        let name = format!("{}_{}", prefix, self.bv_vars.len());
        self.bv_var(name, size)
    }

    /// Get or create an array variable owned by this encoding context.
    pub fn array_var(&mut self, symbol: impl Into<SymbolId>, domain: &Sort, range: &Sort) -> Array {
        let symbol = symbol.into();
        let name = symbol.as_str();
        let key = format!("{}_{:?}_{:?}", name, domain, range);
        if let Some(var) = self.array_vars.get(&key) {
            var.clone()
        } else {
            let var = Array::new_const(name, domain, range);
            self.array_vars.insert(key, var.clone());
            var
        }
    }

    /// Create a fresh array variable with a context-local unique name.
    pub fn fresh_array_var(&mut self, prefix: &str, domain: &Sort, range: &Sort) -> Array {
        let name = format!("{}_{}", prefix, self.array_vars.len());
        self.array_var(name, domain, range)
    }

    /// Create an integer constant.
    pub fn int_const(&self, value: i64) -> Int {
        self.z3.int_const(value)
    }

    /// Create a boolean constant.
    pub fn bool_const(&self, value: bool) -> Bool {
        self.z3.bool_const(value)
    }

    /// Create a real constant from numerator and denominator.
    pub fn real_const(&self, num: i32, den: i32) -> Real {
        self.z3.real_const(num, den)
    }

    /// Create a bitvector constant.
    pub fn bv_const(&self, value: i64, size: u32) -> BV {
        self.z3.bv_const(value, size)
    }

    /// Create or get an uninterpreted sort owned by this encoding context.
    pub fn uninterpreted_sort(&mut self, name: &str) -> Sort {
        if let Some(sort) = self.sorts.get(name) {
            sort.clone()
        } else {
            let sort = Sort::uninterpreted(Symbol::String(name.to_string()));
            self.sorts.insert(name.to_string(), sort.clone());
            sort
        }
    }

    /// Create or get an uninterpreted function owned by this encoding context.
    pub fn uninterpreted_func<'r>(
        &'r mut self,
        name: &str,
        domain: &[&Sort],
        range: &Sort,
    ) -> &'r RecFuncDecl {
        if !self.uninterpreted_funcs.contains_key(name) {
            let func = RecFuncDecl::new(name, domain, range);
            self.uninterpreted_funcs.insert(name.to_string(), func);
        }
        self.uninterpreted_funcs.get(name).unwrap()
    }

    /// Add a constraint to the embedded solver.
    pub fn assert(&mut self, constraint: &Bool) {
        self.z3.assert(constraint);
    }

    /// Check satisfiability.
    pub fn check(&self) -> z3::SatResult {
        self.z3.check()
    }

    /// Get the model if satisfiable.
    pub fn get_model(&self) -> Option<Model> {
        self.z3.get_model()
    }

    /// Push a new assertion scope.
    pub fn push(&mut self) {
        self.z3.push();
    }

    /// Pop assertion scopes.
    pub fn pop(&mut self, n: u32) {
        self.z3.pop(n);
    }

    /// Reset the embedded solver.
    pub fn reset(&mut self) {
        self.z3.reset();
    }

    /// Get the embedded solver.
    pub fn solver(&self) -> &Solver {
        self.z3.solver()
    }

    /// Get mutable embedded solver reference.
    pub fn solver_mut(&mut self) -> &mut Solver {
        self.z3.solver_mut()
    }

    /// Get integer sort.
    pub fn int_sort(&self) -> Sort {
        self.z3.int_sort()
    }

    /// Get boolean sort.
    pub fn bool_sort(&self) -> Sort {
        self.z3.bool_sort()
    }

    /// Get real sort.
    pub fn real_sort(&self) -> Sort {
        self.z3.real_sort()
    }

    /// Get bitvector sort.
    pub fn bv_sort(&self, size: u32) -> Sort {
        self.z3.bv_sort(size)
    }

    /// Get array sort.
    pub fn array_sort(&self, domain: &Sort, range: &Sort) -> Sort {
        self.z3.array_sort(domain, range)
    }

    /// Evaluate every variable owned by this encoding context in the current
    /// model. This intentionally lives here rather than in `Z3Interface`
    /// because only the encoding context knows which symbols matter.
    pub fn get_model_values(&mut self) -> Option<HashMap<String, String>> {
        if self.z3.check() != SatResult::Sat {
            return None;
        }

        let model = self.z3.get_model()?;
        let mut values = HashMap::new();

        // Evaluate all int variables
        for (name, var) in &self.int_vars {
            if let Some(value) = model.eval(var, true) {
                if let Some(int_val) = value.as_i64() {
                    values.insert(name.clone(), int_val.to_string());
                } else {
                    values.insert(name.clone(), value.to_string());
                }
            }
        }

        // Evaluate all bool variables
        for (name, var) in &self.bool_vars {
            if let Some(value) = model.eval(var, true) {
                if let Some(bool_val) = value.as_bool() {
                    values.insert(name.clone(), bool_val.to_string());
                } else {
                    values.insert(name.clone(), value.to_string());
                }
            }
        }

        // Evaluate all real variables
        for (name, var) in &self.real_vars {
            if let Some(value) = model.eval(var, true) {
                if let Some((num, den)) = value.as_rational() {
                    if den == 1 {
                        values.insert(name.clone(), num.to_string());
                    } else {
                        values.insert(name.clone(), format!("{}/{}", num, den));
                    }
                } else {
                    values.insert(name.clone(), value.to_string());
                }
            }
        }

        // Evaluate all bitvector variables
        for (name, var) in &self.bv_vars {
            if let Some(value) = model.eval(var, true) {
                values.insert(name.clone(), value.to_string());
            }
        }

        // Evaluate all array variables
        for (name, var) in &self.array_vars {
            if let Some(value) = model.eval(var, true) {
                values.insert(name.clone(), value.to_string());
            }
        }

        Some(values)
    }
}

impl Default for SmtEncodingContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_usage() {
        let mut z3 = SmtEncodingContext::new();

        let x = z3.int_var("x");
        let y = z3.int_var("y");
        let two = z3.int_const(2);

        z3.assert(&x.eq(&two));
        z3.assert(&y.gt(&x));

        assert_eq!(z3.check(), z3::SatResult::Sat);

        if let Some(model) = z3.get_model() {
            println!("Model: {}", model);
        }
    }

    #[test]
    fn test_bool_vars() {
        let mut z3 = SmtEncodingContext::new();

        let a = z3.bool_var("a");
        let b = z3.bool_var("b");

        z3.assert(&a);
        z3.assert(&b.not());

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }

    #[test]
    fn test_real_vars() {
        let mut z3 = SmtEncodingContext::new();

        let x = z3.real_var("x");
        let half = z3.real_const(1, 2);

        z3.assert(&x.gt(&half));

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }

    #[test]
    fn test_bitvectors() {
        let mut z3 = SmtEncodingContext::new();

        let x = z3.bv_var("x", 8);
        let y = z3.bv_var("y", 8);
        let ten = z3.bv_const(10, 8);

        z3.assert(&x.bvadd(&y).eq(&ten));
        z3.assert(&x.bvugt(&y));

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }

    #[test]
    fn test_arrays() {
        let mut z3 = SmtEncodingContext::new();

        let int_sort = z3.int_sort();
        let arr = z3.array_var("arr", &int_sort, &int_sort);
        let i = z3.int_var("i");
        let zero = z3.int_const(0);

        z3.assert(&arr.select(&i).eq(&zero));

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }
}
