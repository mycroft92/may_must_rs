use std::collections::HashMap;
use z3::ast::{Ast, Bool, Int, Real};
use z3::{FuncDecl, Model, SatResult, Solver, Sort, Symbol};

pub struct Z3Interface {
    pub solver: Solver,
    // Track created symbols for reuse
    pub int_vars: HashMap<String, Int>,
    pub bool_vars: HashMap<String, Bool>,
    pub real_vars: HashMap<String, Real>,
    pub uninterpreted_funcs: HashMap<String, FuncDecl>,
    pub sorts: HashMap<String, Sort>,
}

impl Z3Interface {
    /// Create a new Z3Interface with default configuration
    pub fn new() -> Self {
        let solver = Solver::new();
        Self {
            solver,
            int_vars: HashMap::new(),
            bool_vars: HashMap::new(),
            real_vars: HashMap::new(),
            uninterpreted_funcs: HashMap::new(),
            sorts: HashMap::new(),
        }
    }

    /// Get or create an integer variable
    pub fn int_var(&mut self, name: &str) -> Int {
        if let Some(var) = self.int_vars.get(name) {
            var.clone()
        } else {
            let var = Int::new_const(name);
            self.int_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh integer variable with unique name
    pub fn fresh_int_var(&mut self, prefix: &str) -> Int {
        let name = format!("{}_{}", prefix, self.int_vars.len());
        self.int_var(&name)
    }

    /// Get or create a boolean variable
    pub fn bool_var(&mut self, name: &str) -> Bool {
        if let Some(var) = self.bool_vars.get(name) {
            var.clone()
        } else {
            let var = Bool::new_const(name);
            self.bool_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh boolean variable with unique name
    pub fn fresh_bool_var(&mut self, prefix: &str) -> Bool {
        let name = format!("{}_{}", prefix, self.bool_vars.len());
        self.bool_var(&name)
    }

    /// Get or create a real (float) variable
    pub fn real_var(&mut self, name: &str) -> Real {
        if let Some(var) = self.real_vars.get(name) {
            var.clone()
        } else {
            let var = Real::new_const(name);
            self.real_vars.insert(name.to_string(), var.clone());
            var
        }
    }

    /// Create a fresh real variable with unique name
    pub fn fresh_real_var(&mut self, prefix: &str) -> Real {
        let name = format!("{}_{}", prefix, self.real_vars.len());
        self.real_var(&name)
    }

    /// Create an integer constant
    pub fn int_const(&self, value: i64) -> Int {
        Int::from_i64(value)
    }

    /// Create a boolean constant
    pub fn bool_const(&self, value: bool) -> Bool {
        Bool::from_bool(value)
    }

    /// Create a real constant from numerator and denominator
    pub fn real_const(&self, num: i32, den: i32) -> Real {
        Real::from_rational(num.into(), den.into())
    }

    /// Create or get an uninterpreted sort
    pub fn uninterpreted_sort(&mut self, name: &str) -> Sort {
        if let Some(sort) = self.sorts.get(name) {
            sort.clone()
        } else {
            let sort = Sort::uninterpreted(Symbol::from(name));
            self.sorts.insert(name.to_string(), sort.clone());
            sort
        }
    }

    /// Create an uninterpreted function
    pub fn uninterpreted_func<'r>(
        &'r mut self,
        name: &str,
        domain: &[&Sort],
        range: &Sort,
    ) -> &'r FuncDecl {
        if !self.uninterpreted_funcs.contains_key(name) {
            let func = FuncDecl::new(name, domain, range);
            self.uninterpreted_funcs.insert(name.to_string(), func);
        }
        self.uninterpreted_funcs.get(name).unwrap()
    }

    /// Add a constraint to the solver
    pub fn assert(&mut self, constraint: &Bool) {
        self.solver.assert(constraint);
    }

    /// Check satisfiability
    pub fn check(&self) -> z3::SatResult {
        self.solver.check()
    }

    /// Get the model if satisfiable
    pub fn get_model(&self) -> Option<Model> {
        self.solver.get_model()
    }

    /// Push a new assertion scope
    pub fn push(&mut self) {
        self.solver.push();
    }

    /// Pop an assertion scope
    pub fn pop(&mut self, n: u32) {
        self.solver.pop(n);
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.solver.reset();
    }

    /// Get the solver
    pub fn solver(&self) -> &Solver {
        &self.solver
    }

    /// Get mutable solver reference
    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }

    /// Get integer sort
    pub fn int_sort(&self) -> Sort {
        Sort::int()
    }

    /// Get boolean sort
    pub fn bool_sort(&self) -> Sort {
        Sort::bool()
    }

    /// Get real sort
    pub fn real_sort(&self) -> Sort {
        Sort::real()
    }

    pub fn get_model_values(&mut self) -> Option<HashMap<String, String>> {
        if self.solver.check() != SatResult::Sat {
            return None;
        }

        let model = self.solver.get_model()?;
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

        Some(values)
    }
}

impl Default for Z3Interface {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_usage() {
        let mut z3 = Z3Interface::new();

        let x = z3.int_var("x");
        let y = z3.int_var("y");
        let two = z3.int_const(2);

        z3.assert(&x._eq(&two));
        z3.assert(&y.gt(&x));

        assert_eq!(z3.check(), z3::SatResult::Sat);

        if let Some(model) = z3.get_model() {
            println!("Model: {}", model);
        }
    }

    #[test]
    fn test_bool_vars() {
        let mut z3 = Z3Interface::new();

        let a = z3.bool_var("a");
        let b = z3.bool_var("b");

        z3.assert(&a);
        z3.assert(&b.not());

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }

    #[test]
    fn test_real_vars() {
        let mut z3 = Z3Interface::new();

        let x = z3.real_var("x");
        let half = z3.real_const(1, 2);

        z3.assert(&x.gt(&half));

        assert_eq!(z3.check(), z3::SatResult::Sat);
    }
}
