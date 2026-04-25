//! Minimal intraprocedural driver for the current milestone.
//!
//! This driver is intentionally narrow. It handles one lowered procedure at a
//! time, explores acyclic branch paths, applies normalized transfer effects,
//! and uses the SMT oracle to decide whether embedded `may_assert` obligations
//! are feasible.
//!
//! It is not yet the full paper scheduler:
//!
//! - no loop handling beyond rejecting cyclic paths
//! - no interprocedural summaries
//! - no automatic `β` / `θ` generation for the named rule layer
//!
//! The purpose is to wire the existing lowering/oracle/transfer pieces into one
//! honest end-to-end slice for straightline and branchy single-procedure code.

use crate::analysis::cfg::CfgNodeId;
use crate::analysis::formula::Formula;
use crate::analysis::llvm_adapter::{adapt_function_graph, AdaptedProcedure, AdapterError};
use crate::analysis::oracle::{Feasibility, Oracle, OracleError};
use crate::analysis::rules::QueryJudgement;
use crate::analysis::state::NodeState;
use crate::analysis::transfer::{apply_effects, TransferError};
use crate::llvm_utils::program_graph::FunctionGraph;
use std::collections::BTreeSet;
use thiserror::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimpleProcedureReport {
    pub procedure: String,
    pub judgement: QueryJudgement,
    pub explored_paths: usize,
    pub pruned_paths: usize,
    pub checked_obligations: usize,
    pub feasible_obligations: usize,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum DriverError {
    #[error(transparent)]
    Adapter(#[from] AdapterError),
    #[error(transparent)]
    Oracle(#[from] OracleError),
    #[error(transparent)]
    Transfer(#[from] TransferError),
    #[error("driver requires an acyclic procedure but found a cycle through {node:?}")]
    LoopUnsupported { node: CfgNodeId },
    #[error("unknown CFG node {node:?}")]
    UnknownNode { node: CfgNodeId },
    #[error("missing CFG edge {edge}")]
    MissingEdge { edge: usize },
}

pub fn analyze_function_graph_simple(
    graph: &FunctionGraph,
) -> Result<SimpleProcedureReport, DriverError> {
    let adapted = adapt_function_graph(graph)?;
    analyze_adapted_procedure_simple(&graph.name, &adapted)
}

pub fn analyze_adapted_procedure_simple(
    procedure: &str,
    adapted: &AdaptedProcedure,
) -> Result<SimpleProcedureReport, DriverError> {
    let oracle = Oracle::new();
    let mut explorer = SimpleExplorer::new(procedure, adapted, &oracle);
    explorer.explore_entry()?;
    Ok(explorer.finish())
}

struct SimpleExplorer<'a> {
    procedure: &'a str,
    adapted: &'a AdaptedProcedure,
    oracle: &'a Oracle,
    explored_paths: usize,
    pruned_paths: usize,
    checked_obligations: usize,
    feasible_obligations: usize,
    unknown_seen: bool,
}

impl<'a> SimpleExplorer<'a> {
    fn new(procedure: &'a str, adapted: &'a AdaptedProcedure, oracle: &'a Oracle) -> Self {
        Self {
            procedure,
            adapted,
            oracle,
            explored_paths: 0,
            pruned_paths: 0,
            checked_obligations: 0,
            feasible_obligations: 0,
            unknown_seen: false,
        }
    }

    fn finish(self) -> SimpleProcedureReport {
        let judgement = if self.feasible_obligations > 0 {
            QueryJudgement::Yes
        } else if self.unknown_seen {
            QueryJudgement::Unknown
        } else {
            QueryJudgement::No
        };
        SimpleProcedureReport {
            procedure: self.procedure.to_string(),
            judgement,
            explored_paths: self.explored_paths,
            pruned_paths: self.pruned_paths,
            checked_obligations: self.checked_obligations,
            feasible_obligations: self.feasible_obligations,
        }
    }

    fn explore_entry(&mut self) -> Result<(), DriverError> {
        let entry = self.adapted.cfg.entry();
        let mut active = BTreeSet::new();
        self.explore_node(entry, NodeState::entry(), &mut active)
    }

    fn explore_node(
        &mut self,
        node: CfgNodeId,
        mut state: NodeState,
        active: &mut BTreeSet<CfgNodeId>,
    ) -> Result<(), DriverError> {
        if !active.insert(node) {
            return Err(DriverError::LoopUnsupported { node });
        }

        if let Some(effects) = self.adapted.node_effects.get(&node) {
            apply_effects(&mut state, effects)?;
        }

        match self.oracle.state_feasibility(&state)? {
            Feasibility::Feasible => {}
            Feasibility::Infeasible => {
                self.pruned_paths += 1;
                active.remove(&node);
                return Ok(());
            }
            Feasibility::Unknown => {
                self.unknown_seen = true;
                active.remove(&node);
                return Ok(());
            }
        }

        self.check_obligations(&mut state)?;
        if self.feasible_obligations > 0 {
            active.remove(&node);
            return Ok(());
        }

        let outgoing = self
            .adapted
            .cfg
            .outgoing_edges(node)
            .map_err(|_| DriverError::UnknownNode { node })?;
        if outgoing.is_empty() {
            self.explored_paths += 1;
            active.remove(&node);
            return Ok(());
        }

        for edge_id in outgoing {
            if self.feasible_obligations > 0 {
                break;
            }
            let edge = self
                .adapted
                .cfg
                .edge(edge_id)
                .ok_or(DriverError::MissingEdge { edge: edge_id.0 })?;
            let mut next_state = state.clone();
            next_state.path_summary_mut().refine(edge.relation.clone());
            if let Some(effects) = self.adapted.edge_effects.get(&edge_id) {
                apply_effects(&mut next_state, effects)?;
            }

            match self.oracle.state_feasibility(&next_state)? {
                Feasibility::Feasible => {
                    self.explore_node(edge.target, next_state, active)?;
                }
                Feasibility::Infeasible => {
                    self.pruned_paths += 1;
                }
                Feasibility::Unknown => {
                    self.unknown_seen = true;
                }
            }
        }

        active.remove(&node);
        Ok(())
    }

    fn check_obligations(&mut self, state: &mut NodeState) -> Result<(), DriverError> {
        let obligations = state.obligations().formulas().to_vec();
        if obligations.is_empty() {
            return Ok(());
        }

        let path_formula = state.feasibility_formula();
        for obligation in obligations {
            self.checked_obligations += 1;
            match self
                .oracle
                .feasibility(&Formula::and(path_formula.clone(), obligation))?
            {
                Feasibility::Feasible => {
                    self.feasible_obligations += 1;
                }
                Feasibility::Infeasible => {}
                Feasibility::Unknown => {
                    self.unknown_seen = true;
                }
            }
        }
        state.clear_obligations();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llvm_utils::llvm_wrap::{initialize_target, Context};
    use crate::llvm_utils::program_graph::generate_program_graph;

    fn analyze_first(ir: &str) -> SimpleProcedureReport {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "driver_test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        analyze_function_graph_simple(&graphs[0]).unwrap()
    }

    #[test]
    fn straight_line_assert_is_reported_safe() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define i32 @main() {
                entry:
                    %x = add i32 2, 3
                    %ok = icmp eq i32 %x, 5
                    call void @may_assert(i1 %ok)
                    ret i32 %x
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
        assert_eq!(report.checked_obligations, 1);
    }

    #[test]
    fn branch_pruned_assertions_are_reported_safe() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %then_ok = icmp sgt i32 %x, 0
                    call void @may_assert(i1 %then_ok)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::No);
        assert_eq!(report.feasible_obligations, 0);
        assert_eq!(report.checked_obligations, 2);
        assert_eq!(report.explored_paths, 2);
    }

    #[test]
    fn branch_can_report_an_unsafe_obligation() {
        let report = analyze_first(
            r#"
                declare void @may_assert(i1)

                define void @main(i32 %x) {
                entry:
                    %cond = icmp sgt i32 %x, 0
                    br i1 %cond, label %then, label %else
                then:
                    %bad = icmp slt i32 %x, 0
                    call void @may_assert(i1 %bad)
                    br label %exit
                else:
                    call void @may_assert(i1 true)
                    br label %exit
                exit:
                    ret void
                }
            "#,
        );
        assert_eq!(report.judgement, QueryJudgement::Yes);
        assert_eq!(report.feasible_obligations, 1);
    }
}
