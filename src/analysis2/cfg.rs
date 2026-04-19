//! Paper-shaped CFG and edge-transition vocabulary.

use crate::analysis2::formula::Predicate;
use crate::analysis2::vocabulary::{EdgeId, NodeId, ProcedureName};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PaperProcedure {
    pub name: ProcedureName,
    pub entry: NodeId,
    pub exit: NodeId,
    pub nodes: Vec<NodeId>,
    pub edges: Vec<PaperEdge>,
}

impl PaperProcedure {
    pub fn new(name: impl Into<ProcedureName>, entry: NodeId, exit: NodeId) -> Self {
        Self {
            name: name.into(),
            entry,
            exit,
            nodes: vec![entry, exit],
            edges: Vec::new(),
        }
    }

    pub fn add_node(&mut self, node: NodeId) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
            self.nodes.sort();
        }
    }

    pub fn add_edge(&mut self, edge: PaperEdge) {
        self.add_node(edge.from);
        self.add_node(edge.to);
        self.edges.push(edge);
        self.edges.sort_by_key(|edge| edge.id);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PaperEdge {
    pub id: EdgeId,
    pub from: NodeId,
    pub to: NodeId,
    /// This is the paper's `Gamma_e`: the concrete transition relation for
    /// the edge.  In the scaffold it is represented as a predicate over
    /// source/destination state vocabulary.
    pub gamma: Predicate,
    pub transition: EdgeTransition,
}

impl PaperEdge {
    pub fn local(
        id: EdgeId,
        from: NodeId,
        to: NodeId,
        gamma: Predicate,
        post_under_approx: Option<Predicate>,
        pre_over_approx: Option<Predicate>,
    ) -> Self {
        Self {
            id,
            from,
            to,
            gamma,
            transition: EdgeTransition {
                kind: EdgeKind::Local,
                post_under_approx,
                pre_over_approx,
            },
        }
    }

    pub fn call(
        id: EdgeId,
        from: NodeId,
        to: NodeId,
        callee: impl Into<ProcedureName>,
        gamma: Predicate,
    ) -> Self {
        Self {
            id,
            from,
            to,
            gamma,
            transition: EdgeTransition {
                kind: EdgeKind::Call {
                    callee: callee.into(),
                },
                post_under_approx: None,
                pre_over_approx: None,
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EdgeTransition {
    pub kind: EdgeKind,
    /// A chosen `theta` satisfying `theta subset Post(Gamma_e, source)`.
    /// Later SMT/analysis adapters should compute this instead of storing it.
    pub post_under_approx: Option<Predicate>,
    /// A chosen `beta` satisfying `Pre(Gamma_e, target) subset beta`.
    /// Later SMT/analysis adapters should compute this instead of storing it.
    pub pre_over_approx: Option<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EdgeKind {
    Local,
    BranchTrue,
    BranchFalse,
    Call { callee: ProcedureName },
    Return,
    Unknown(String),
}
