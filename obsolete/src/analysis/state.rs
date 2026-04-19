//! Relational state-to-SMT encoding.
//!
//! This module is intentionally not an LLVM transfer-function module. It only
//! provides the symbolic state vocabulary that transfer functions will use:
//! one SMT symbol per immutable LLVM SSA value, versioned memory arrays,
//! accumulated path assumptions, and explicit procedure-summary boundary
//! symbols.

use crate::smt::solver::{SmtEncodingContext, SymbolId};
use z3::ast::{Array, Bool, Int};
use z3::{SatResult, Solver, Sort};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SummaryPhase {
    Pre,
    Post,
}

impl SummaryPhase {
    fn as_str(self) -> &'static str {
        match self {
            SummaryPhase::Pre => "pre",
            SummaryPhase::Post => "post",
        }
    }
}

/// Encoding context for one function path, block, or summary instantiation.
///
/// The current model is deliberately hybrid:
/// - SSA values are single-assignment symbols.
/// - Memory is versioned as `mem_0`, `mem_1`, ...
/// - Path constraints are asserted into the embedded SMT solver.
/// - Summary variables use explicit pre/post boundary names.
pub struct StateEncoding {
    function: String,
    current_memory_version: usize,
    path_conditions: Vec<Bool>,
    pub smt: SmtEncodingContext,
}

impl StateEncoding {
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            current_memory_version: 0,
            path_conditions: Vec::new(),
            smt: SmtEncodingContext::new(),
        }
    }

    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn current_memory_version(&self) -> usize {
        self.current_memory_version
    }

    /// Create or fetch the SMT integer symbol for an LLVM SSA value.
    pub fn ssa_int(&mut self, name: &str) -> Int {
        self.smt.int_var(self.ssa_symbol("int", name))
    }

    /// Create or fetch the SMT Boolean symbol for an LLVM SSA value.
    pub fn ssa_bool(&mut self, name: &str) -> Bool {
        self.smt.bool_var(self.ssa_symbol("bool", name))
    }

    /// Bind an SSA integer value to an expression.
    ///
    /// This is how a future transfer function would encode an instruction like
    /// `%3 = add i32 %1, %2`: create `%3`, then assert `%3 = %1 + %2`.
    pub fn bind_ssa_int(&mut self, name: &str, expr: &Int) -> Int {
        let value = self.ssa_int(name);
        self.assert(&value.eq(expr));
        value
    }

    /// Bind an SSA Boolean value to an expression.
    pub fn bind_ssa_bool(&mut self, name: &str, expr: &Bool) -> Bool {
        let value = self.ssa_bool(name);
        self.assert(&value.eq(expr));
        value
    }

    /// Create or fetch a memory array for a specific version.
    ///
    /// The first model uses integer addresses and integer values. A later
    /// memory model can replace this with object/offset addresses or bitvector
    /// byte-addressed memory without changing transfer-module ownership.
    pub fn memory_at(&mut self, version: usize) -> Array {
        let int_sort = self.smt.int_sort();
        self.smt
            .array_var(self.memory_symbol(version), &int_sort, &int_sort)
    }

    pub fn current_memory(&mut self) -> Array {
        self.memory_at(self.current_memory_version)
    }

    /// Encode a store into the current memory version and advance memory.
    ///
    /// Adds the relational constraint:
    ///
    /// ```text
    /// mem_next = store(mem_current, ptr, value)
    /// ```
    pub fn store_current_memory(&mut self, ptr: &Int, value: &Int) -> Array {
        let current = self.current_memory();
        let next_version = self.current_memory_version + 1;
        let next = self.memory_at(next_version);
        let stored = current.store(ptr, value);

        self.assert(&next.eq(&stored));
        self.current_memory_version = next_version;
        next
    }

    /// Read an integer from the current memory version.
    ///
    /// This does not create a new memory version. A transfer function can bind
    /// the returned expression to an SSA value.
    pub fn load_current_memory_int(&mut self, ptr: &Int) -> Int {
        self.current_memory()
            .select(ptr)
            .as_int()
            .expect("state memory is Int -> Int, so select must be Int")
    }

    /// Add a path assumption and assert it into the embedded solver.
    pub fn assume(&mut self, condition: &Bool) {
        self.path_conditions.push(condition.clone());
        self.assert(condition);
    }

    pub fn path_condition(&self) -> Bool {
        if self.path_conditions.is_empty() {
            Bool::from_bool(true)
        } else {
            let refs = self.path_conditions.iter().collect::<Vec<_>>();
            Bool::and(&refs)
        }
    }

    pub fn summary_param_int(&mut self, phase: SummaryPhase, index: usize) -> Int {
        self.smt
            .int_var(self.summary_symbol("param_int", phase, &index.to_string()))
    }

    pub fn summary_return_int(&mut self, phase: SummaryPhase) -> Int {
        self.smt
            .int_var(self.summary_symbol("ret_int", phase, "value"))
    }

    pub fn summary_memory(&mut self, phase: SummaryPhase) -> Array {
        let int_sort = self.smt.int_sort();
        self.smt.array_var(
            self.summary_symbol("mem", phase, "value"),
            &int_sort,
            &int_sort,
        )
    }

    pub fn int_const(&self, value: i64) -> Int {
        self.smt.int_const(value)
    }

    pub fn bool_const(&self, value: bool) -> Bool {
        self.smt.bool_const(value)
    }

    pub fn int_sort(&self) -> Sort {
        self.smt.int_sort()
    }

    pub fn assert(&mut self, condition: &Bool) {
        self.smt.assert(condition);
    }

    pub fn check(&self) -> SatResult {
        self.smt.check()
    }

    pub fn solver(&self) -> &Solver {
        self.smt.solver()
    }

    pub fn solver_mut(&mut self) -> &mut Solver {
        self.smt.solver_mut()
    }

    pub fn push(&mut self) {
        self.smt.push();
    }

    pub fn pop(&mut self, n: u32) {
        self.smt.pop(n);
    }

    fn ssa_symbol(&self, sort: &str, name: &str) -> SymbolId {
        SymbolId::new(format!(
            "{}::ssa::{sort}::{}",
            sanitize(&self.function),
            sanitize(name)
        ))
    }

    fn memory_symbol(&self, version: usize) -> SymbolId {
        SymbolId::new(format!("{}::mem::{version}", sanitize(&self.function)))
    }

    fn summary_symbol(&self, kind: &str, phase: SummaryPhase, name: &str) -> SymbolId {
        SymbolId::new(format!(
            "{}::summary::{}::{kind}::{}",
            sanitize(&self.function),
            phase.as_str(),
            sanitize(name)
        ))
    }
}

impl Default for StateEncoding {
    fn default() -> Self {
        Self::new("function")
    }
}

fn sanitize(value: &str) -> String {
    let mut result = value
        .trim_start_matches('%')
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect::<String>();

    if result.is_empty() {
        result.push('_');
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ssa_values_compose_by_shared_symbols() {
        let mut state = StateEncoding::new("main");

        let one = state.int_const(1);
        let two = state.int_const(2);
        let ten = state.int_const(10);

        let v1 = state.bind_ssa_int("%1", &one);
        let v2 = state.bind_ssa_int("%2", &two);
        let v3_expr = Int::add(&[&v1, &v2]);
        let v3 = state.bind_ssa_int("%3", &v3_expr);
        let v4_expr = Int::mul(&[&v3, &ten]);
        let v4 = state.bind_ssa_int("%4", &v4_expr);

        state.push();
        state.assert(&v4.eq(&state.int_const(30)).not());
        assert_eq!(state.check(), SatResult::Unsat);
        state.pop(1);
    }

    #[test]
    fn memory_versions_compose_store_then_load() {
        let mut state = StateEncoding::new("main");

        let ptr = state.bind_ssa_int("%p", &state.int_const(42));
        let value = state.int_const(7);
        assert_eq!(state.current_memory_version(), 0);

        state.store_current_memory(&ptr, &value);
        assert_eq!(state.current_memory_version(), 1);

        let loaded = state.load_current_memory_int(&ptr);
        let loaded_ssa = state.bind_ssa_int("%loaded", &loaded);

        state.push();
        state.assert(&loaded_ssa.eq(&value).not());
        assert_eq!(state.check(), SatResult::Unsat);
        state.pop(1);
    }

    #[test]
    fn path_conditions_are_solver_constraints() {
        let mut state = StateEncoding::new("main");

        let x = state.ssa_int("%x");
        let zero = state.int_const(0);
        state.assume(&x.gt(&zero));

        state.push();
        state.assert(&x.le(&zero));
        assert_eq!(state.check(), SatResult::Unsat);
        state.pop(1);
    }

    #[test]
    fn summary_boundary_symbols_are_distinct_from_path_symbols() {
        let mut state = StateEncoding::new("foo");

        let path_x = state.ssa_int("%x");
        let pre_param = state.summary_param_int(SummaryPhase::Pre, 0);
        let post_ret = state.summary_return_int(SummaryPhase::Post);

        state.assert(&pre_param.gt(&state.int_const(0)));
        state.assert(&post_ret.eq(&Int::add(&[&pre_param, &state.int_const(1)])));

        state.push();
        state.assert(&path_x.eq(&pre_param));
        assert_eq!(state.check(), SatResult::Sat);
        state.pop(1);

        state.push();
        state.assert(&post_ret.le(&pre_param));
        assert_eq!(state.check(), SatResult::Unsat);
        state.pop(1);
    }
}
