//! LLVM-independent control-flow graph for paper procedures `P`, nodes `n`,
//! edges `e`, and edge-local relations `Gamma_e`.
//!
//! Accumulated path predicates do not live here. They belong in `state.rs`.

use crate::analysis::formula::Formula;
use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CfgNodeId(pub usize);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CfgEdgeId(pub usize);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CfgNodeKind {
    Entry,
    Normal,
    Exit,
    SyntheticExit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CfgNode {
    pub id: CfgNodeId,
    pub label: String,
    pub kind: CfgNodeKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CfgEdge {
    pub id: CfgEdgeId,
    pub source: CfgNodeId,
    pub target: CfgNodeId,
    pub relation: Formula,
}

impl CfgEdge {
    pub fn trivial(id: CfgEdgeId, source: CfgNodeId, target: CfgNodeId) -> Self {
        Self {
            id,
            source,
            target,
            relation: Formula::True,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Cfg {
    nodes: BTreeMap<CfgNodeId, CfgNode>,
    edges: BTreeMap<CfgEdgeId, CfgEdge>,
    entry: CfgNodeId,
    concrete_exits: BTreeSet<CfgNodeId>,
    exit: Option<CfgNodeId>,
    next_node: usize,
    next_edge: usize,
}

impl Cfg {
    pub fn new(entry_label: impl Into<String>) -> Self {
        let entry = CfgNodeId(0);
        let mut nodes = BTreeMap::new();
        nodes.insert(
            entry,
            CfgNode {
                id: entry,
                label: entry_label.into(),
                kind: CfgNodeKind::Entry,
            },
        );
        Self {
            nodes,
            edges: BTreeMap::new(),
            entry,
            concrete_exits: BTreeSet::new(),
            exit: None,
            next_node: 1,
            next_edge: 0,
        }
    }

    pub fn entry(&self) -> CfgNodeId {
        self.entry
    }

    pub fn exit(&self) -> Option<CfgNodeId> {
        self.exit
    }

    pub fn concrete_exits(&self) -> &BTreeSet<CfgNodeId> {
        &self.concrete_exits
    }

    pub fn node(&self, node: CfgNodeId) -> Option<&CfgNode> {
        self.nodes.get(&node)
    }

    pub fn edge(&self, edge: CfgEdgeId) -> Option<&CfgEdge> {
        self.edges.get(&edge)
    }

    pub fn nodes(&self) -> &BTreeMap<CfgNodeId, CfgNode> {
        &self.nodes
    }

    pub fn edges(&self) -> &BTreeMap<CfgEdgeId, CfgEdge> {
        &self.edges
    }

    pub fn add_node(&mut self, label: impl Into<String>) -> CfgNodeId {
        let id = CfgNodeId(self.next_node);
        self.next_node += 1;
        self.nodes.insert(
            id,
            CfgNode {
                id,
                label: label.into(),
                kind: CfgNodeKind::Normal,
            },
        );
        id
    }

    pub fn mark_exit(&mut self, node: CfgNodeId) -> Result<(), CfgError> {
        let kind = if self.exit == Some(node) {
            CfgNodeKind::SyntheticExit
        } else if node == self.entry {
            CfgNodeKind::Entry
        } else {
            CfgNodeKind::Exit
        };
        let current = self
            .nodes
            .get_mut(&node)
            .ok_or(CfgError::UnknownNode { node })?;
        current.kind = kind;
        self.concrete_exits.insert(node);
        Ok(())
    }

    pub fn add_edge(
        &mut self,
        source: CfgNodeId,
        target: CfgNodeId,
        relation: Formula,
    ) -> Result<CfgEdgeId, CfgError> {
        if !self.nodes.contains_key(&source) {
            return Err(CfgError::UnknownNode { node: source });
        }
        if !self.nodes.contains_key(&target) {
            return Err(CfgError::UnknownNode { node: target });
        }
        let edge = CfgEdgeId(self.next_edge);
        self.next_edge += 1;
        self.edges.insert(
            edge,
            CfgEdge {
                id: edge,
                source,
                target,
                relation,
            },
        );
        Ok(edge)
    }

    pub fn successors(&self, node: CfgNodeId) -> Result<Vec<CfgNodeId>, CfgError> {
        self.require_node(node)?;
        Ok(self
            .edges
            .values()
            .filter(|edge| edge.source == node)
            .map(|edge| edge.target)
            .collect())
    }

    pub fn predecessors(&self, node: CfgNodeId) -> Result<Vec<CfgNodeId>, CfgError> {
        self.require_node(node)?;
        Ok(self
            .edges
            .values()
            .filter(|edge| edge.target == node)
            .map(|edge| edge.source)
            .collect())
    }

    pub fn incoming_edges(&self, node: CfgNodeId) -> Result<Vec<CfgEdgeId>, CfgError> {
        self.require_node(node)?;
        Ok(self
            .edges
            .values()
            .filter(|edge| edge.target == node)
            .map(|edge| edge.id)
            .collect())
    }

    pub fn outgoing_edges(&self, node: CfgNodeId) -> Result<Vec<CfgEdgeId>, CfgError> {
        self.require_node(node)?;
        Ok(self
            .edges
            .values()
            .filter(|edge| edge.source == node)
            .map(|edge| edge.id)
            .collect())
    }

    pub fn ensure_single_exit(&mut self) -> Result<CfgNodeId, CfgError> {
        match self.concrete_exits.len() {
            0 => Err(CfgError::MissingExit),
            1 => {
                let exit = *self.concrete_exits.iter().next().unwrap();
                self.exit = Some(exit);
                Ok(exit)
            }
            _ => {
                if let Some(existing) = self.exit {
                    return Ok(existing);
                }
                let exit = self.add_node("__synthetic_exit");
                if let Some(node) = self.nodes.get_mut(&exit) {
                    node.kind = CfgNodeKind::SyntheticExit;
                }
                let exits = self.concrete_exits.iter().copied().collect::<Vec<_>>();
                for real_exit in exits {
                    self.add_edge(real_exit, exit, Formula::True)?;
                }
                self.exit = Some(exit);
                Ok(exit)
            }
        }
    }

    fn require_node(&self, node: CfgNodeId) -> Result<(), CfgError> {
        if self.nodes.contains_key(&node) {
            Ok(())
        } else {
            Err(CfgError::UnknownNode { node })
        }
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum CfgError {
    #[error("unknown CFG node {node:?}")]
    UnknownNode { node: CfgNodeId },
    #[error("cannot normalize a CFG without exits")]
    MissingExit,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::formula::{Sort, Term};

    #[test]
    fn entry_exit_tracking_works() {
        let mut cfg = Cfg::new("entry");
        let exit = cfg.add_node("ret");
        cfg.mark_exit(exit).unwrap();
        assert_eq!(cfg.entry(), CfgNodeId(0));
        assert!(cfg.concrete_exits().contains(&exit));
    }

    #[test]
    fn predecessor_and_successor_lookup_works() {
        let mut cfg = Cfg::new("entry");
        let next = cfg.add_node("next");
        cfg.add_edge(cfg.entry(), next, Formula::True).unwrap();
        assert_eq!(cfg.successors(cfg.entry()).unwrap(), vec![next]);
        assert_eq!(cfg.predecessors(next).unwrap(), vec![cfg.entry()]);
    }

    #[test]
    fn edge_relations_are_stored() {
        let mut cfg = Cfg::new("entry");
        let exit = cfg.add_node("exit");
        let relation = Formula::gt(Term::var("x", Sort::Int), Term::int(0));
        let edge = cfg.add_edge(cfg.entry(), exit, relation.clone()).unwrap();
        assert_eq!(cfg.edge(edge).unwrap().relation, relation);
    }

    #[test]
    fn unknown_nodes_are_rejected() {
        let cfg = Cfg::new("entry");
        assert_eq!(
            cfg.successors(CfgNodeId(999)).unwrap_err(),
            CfgError::UnknownNode {
                node: CfgNodeId(999)
            }
        );
    }

    #[test]
    fn synthetic_exit_is_created_when_needed() {
        let mut cfg = Cfg::new("entry");
        let left = cfg.add_node("left");
        let right = cfg.add_node("right");
        cfg.mark_exit(left).unwrap();
        cfg.mark_exit(right).unwrap();
        let exit = cfg.ensure_single_exit().unwrap();
        assert_eq!(cfg.node(exit).unwrap().kind, CfgNodeKind::SyntheticExit);
        assert_eq!(cfg.incoming_edges(exit).unwrap().len(), 2);
    }

    #[test]
    fn single_exit_normalization_is_a_noop() {
        let mut cfg = Cfg::new("entry");
        let exit = cfg.add_node("exit");
        cfg.mark_exit(exit).unwrap();
        assert_eq!(cfg.ensure_single_exit().unwrap(), exit);
        assert_eq!(cfg.nodes().len(), 2);
    }

    #[test]
    fn missing_exit_is_rejected() {
        let mut cfg = Cfg::new("entry");
        assert_eq!(cfg.ensure_single_exit().unwrap_err(), CfgError::MissingExit);
    }
}
