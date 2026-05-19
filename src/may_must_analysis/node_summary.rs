//! Per-node summary pairs for the bidirectional may/must analysis.
//!
//! Each CFG node carries two orthogonal pieces of information:
//!
//! - `reach`: a **forward** overapproximation of the states in which this node
//!   is reachable (the *must-reach* component).
//! - `state`: a **backward** underapproximation of the states that can lead to
//!   an assertion violation (the *not-may* component, i.e. the WP of `NOT
//!   obligation` propagated from the assertion site).
//!
//! Verification succeeds when `reach ∧ state` is unsatisfiable at the
//! procedure entry: either the node is never reached, or no reachable state
//! satisfies the violation precondition.

use crate::common::abstract_cfg::CfgNodeId;
use crate::common::formula::Formula;

/// The bidirectional summary attached to a single CFG node.
///
/// Invariant: both fields are closed formulas over the symbolic state at the
/// point the node is *entered*.  They are updated monotonically (via
/// [`join_reach`] / [`join_state`]) until a fixpoint is reached.
///
/// [`join_reach`]: NodeSummary::join_reach
/// [`join_state`]: NodeSummary::join_state
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSummary {
    /// The CFG node this summary belongs to.
    pub node: CfgNodeId,

    /// **Forward MAY (SP, over-approximation).** A formula whose models
    /// over-approximate the set of entry states from which this node is
    /// reachable.  Starts as `False` (unreachable) and grows under
    /// disjunction as forward propagation adds new reachability paths.  Loop
    /// headers receive injected loop invariants to accelerate convergence.
    ///
    /// SMASH-paper term: **MAY**.  Used to prune backward NOT-MAY propagation
    /// via [`crate::may_must_analysis::rules::RuleEngine::notmay_pre_pruned`].
    pub reach: Formula,

    /// **Backward NOT-MAY (WP, over-approximation).**  A formula whose models
    /// over-approximate the set of entry states that can lead to an assertion
    /// violation through this node.  It is the weakest precondition of
    /// `NOT obligation` accumulated from the assertion site backward through
    /// this node.  Starts as `False` (no violation possible) and grows under
    /// disjunction as backward propagation discovers new violation paths.
    ///
    /// SMASH-paper term: **NOT-MAY**.  If `state[entry]` is `False`, the
    /// procedure is verified safe.
    pub state: Formula,

    /// **Forward MUST (under-approximation, feasibility-checked SP).**  A
    /// formula whose models are **definitely** concrete reachable states at
    /// this node.  Every disjunct was added only after an SMT feasibility
    /// check.  Starts as `False` (no concrete witness yet) and grows under
    /// disjunction as forward MUST propagation discovers feasible paths.
    ///
    /// SMASH-paper term: **MUST**.  If `must_reach[assertion_site] ∧ ¬obligation`
    /// is SAT with a model, the procedure has a real bug.  This is the only
    /// sound way to declare `BugFound` for cyclic CFGs (where `reach` is
    /// over-approximate and `reach ∧ state` SAT can be spurious).
    ///
    /// Loop handling: forward MUST cannot terminate over unbounded loops on
    /// its own.  Cyclic CFGs are unrolled to a bound `k` (via
    /// [`crate::may_must_analysis::bmc::bmc_check`]) before forward MUST
    /// propagation runs over the resulting acyclic graph.
    pub must_reach: Formula,
}

impl NodeSummary {
    /// Creates a summary for a node that is considered **unreachable** at
    /// initialisation time.  All three components are `False`.
    pub fn unreachable(node: CfgNodeId) -> Self {
        Self {
            node,
            reach: Formula::False,
            state: Formula::False,
            must_reach: Formula::False,
        }
    }

    /// Creates the seed summary for the **procedure entry** node.
    ///
    /// `reach` and `must_reach` are `True` (the entry is trivially reachable
    /// both over- and under-approximately).  `state` is `False` (no violation
    /// condition has been propagated back to the entry yet).
    pub fn entry(node: CfgNodeId) -> Self {
        Self {
            node,
            reach: Formula::True,
            state: Formula::False,
            must_reach: Formula::True,
        }
    }

    /// Returns `reach ∧ state`, the conjunction used to check whether a
    /// reachable state simultaneously satisfies the violation precondition.
    ///
    /// Short-circuits to `False` whenever either component is already `False`,
    /// avoiding unnecessary formula construction.  The combined formula is
    /// `False` iff there is no state that is both reachable and a violation
    /// witness.
    pub fn combined(&self) -> Formula {
        if self.reach == Formula::False || self.state == Formula::False {
            Formula::False
        } else {
            Formula::and(self.reach.clone(), self.state.clone())
        }
    }

    /// Widens `reach` by joining it with `incoming` under disjunction.
    ///
    /// Called during forward propagation when a new path to this node is
    /// discovered.  The result overapproximates the union of previously known
    /// reachable states and the newly propagated ones.
    pub fn join_reach(&mut self, incoming: &Formula) {
        self.reach = Formula::or(self.reach.clone(), incoming.clone());
    }

    /// Widens `state` by joining it with `incoming` under disjunction.
    ///
    /// Called during backward propagation when an additional violation
    /// precondition is propagated into this node from a successor.  The result
    /// captures all currently known ways a violation can be reached through
    /// this node.
    pub fn join_state(&mut self, incoming: &Formula) {
        self.state = Formula::or(self.state.clone(), incoming.clone());
    }

    /// Widens `must_reach` by joining it with `incoming` under disjunction.
    ///
    /// Callers must ensure `incoming` is **feasibility-checked** before
    /// joining — i.e. the SMT oracle has confirmed there exists a model of
    /// `incoming` corresponding to a real reachable execution.  The
    /// resulting disjunction preserves the under-approximation invariant:
    /// every model of `must_reach` is a real concrete reachable state.
    pub fn join_must_reach(&mut self, incoming: &Formula) {
        self.must_reach = Formula::or(self.must_reach.clone(), incoming.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unreachable_state_is_false_false() {
        let summary = NodeSummary::unreachable(CfgNodeId(0));
        assert_eq!(summary.reach, Formula::False);
        assert_eq!(summary.state, Formula::False);
    }

    #[test]
    fn entry_state_is_true_false() {
        let summary = NodeSummary::entry(CfgNodeId(0));
        assert_eq!(summary.reach, Formula::True);
        assert_eq!(summary.state, Formula::False);
    }

    #[test]
    fn combined_short_circuits_false_reach() {
        let summary = NodeSummary {
            node: CfgNodeId(1),
            reach: Formula::False,
            state: Formula::bool_var("x"),
            must_reach: Formula::False,
        };
        assert_eq!(summary.combined(), Formula::False);
    }

    #[test]
    fn join_reach_uses_or() {
        let mut summary = NodeSummary::entry(CfgNodeId(0));
        summary.join_reach(&Formula::bool_var("r"));
        assert_eq!(
            summary.reach,
            Formula::or(Formula::True, Formula::bool_var("r"))
        );
    }

    #[test]
    fn join_state_uses_or() {
        let mut summary = NodeSummary::unreachable(CfgNodeId(0));
        summary.join_state(&Formula::bool_var("s"));
        assert_eq!(
            summary.state,
            Formula::or(Formula::False, Formula::bool_var("s"))
        );
    }
}
