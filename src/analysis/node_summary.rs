use crate::analysis::abstract_cfg::CfgNodeId;
use crate::analysis::formula::Formula;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSummary {
    pub node: CfgNodeId,
    pub reach: Formula,
    pub state: Formula,
}

impl NodeSummary {
    pub fn unreachable(node: CfgNodeId) -> Self {
        Self {
            node,
            reach: Formula::False,
            state: Formula::False,
        }
    }

    pub fn entry(node: CfgNodeId) -> Self {
        Self {
            node,
            reach: Formula::True,
            state: Formula::False,
        }
    }

    pub fn combined(&self) -> Formula {
        if self.reach == Formula::False || self.state == Formula::False {
            Formula::False
        } else {
            Formula::and(self.reach.clone(), self.state.clone())
        }
    }

    pub fn join_reach(&mut self, incoming: &Formula) {
        self.reach = Formula::or(self.reach.clone(), incoming.clone());
    }

    pub fn join_state(&mut self, incoming: &Formula) {
        self.state = Formula::or(self.state.clone(), incoming.clone());
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
