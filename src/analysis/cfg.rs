//! LLVM-independent control-flow graph for paper procedures `P`, nodes `n`,
//! edges `e`, and edge-local relations `Gamma_e`.
//!
//! This module intentionally stays structural:
//!
//! - nodes and edges identify the paper graph shape;
//! - each edge carries only its local guard/relation `Gamma_e`;
//! - entry/exit normalization, including the synthetic single-exit node, lives
//!   here;
//! - SCC-based loop extraction and condensation into an acyclic summary
//!   structure also live here;
//! - accumulated path predicates, must regions, blocked pairs, and summaries do
//!   not live here.
//!
//! That separation keeps the paper objects easy to audit: `cfg.rs` says what
//! can happen next, while `state.rs` and `rules.rs` say what is known about the
//! executions that actually reach those points.

use crate::analysis::formula::Formula;
use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CfgNodeId(pub usize);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CfgEdgeId(pub usize);

/// Paper-level classification of one CFG node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CfgNodeKind {
    Entry,
    Normal,
    Exit,
    SyntheticExit,
}

/// One paper CFG node with a stable identifier and human-readable label.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CfgNode {
    pub id: CfgNodeId,
    pub label: String,
    pub kind: CfgNodeKind,
}

/// One directed CFG edge plus its local relation `Gamma_e`.
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

/// LLVM-independent CFG with optional synthetic single-exit normalization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cfg {
    nodes: BTreeMap<CfgNodeId, CfgNode>,
    edges: BTreeMap<CfgEdgeId, CfgEdge>,
    entry: CfgNodeId,
    concrete_exits: BTreeSet<CfgNodeId>,
    exit: Option<CfgNodeId>,
    next_node: usize,
    next_edge: usize,
}

/// SCC-based loop region extracted from one CFG.
///
/// Headers are the nodes in the SCC that receive control from outside the loop
/// body. For reducible LLVM loops this set is usually a singleton; multiple
/// headers indicate an irreducible cycle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopRegion {
    pub id: usize,
    pub headers: BTreeSet<CfgNodeId>,
    pub body: BTreeSet<CfgNodeId>,
    pub entry_edges: BTreeSet<CfgEdgeId>,
    pub exit_edges: BTreeSet<CfgEdgeId>,
    pub back_edges: BTreeSet<CfgEdgeId>,
}

/// Stable identifier for one condensation region in the summary structure.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SummaryRegionId(pub usize);

/// Summary-facing classification of one condensation region.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryRegionKind {
    StraightLine,
    Loop { loop_id: usize },
}

/// One acyclic condensation region used to sequence loop and non-loop work.
///
/// Each region is one SCC of the original CFG. Straight-line regions are
/// singleton SCCs; loop regions are cyclic SCCs that will later need an
/// invariant or loop summary before the whole function can be summarized
/// cleanly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryRegion {
    pub id: SummaryRegionId,
    pub kind: SummaryRegionKind,
    pub nodes: BTreeSet<CfgNodeId>,
    pub entry_edges: BTreeSet<CfgEdgeId>,
    pub exit_edges: BTreeSet<CfgEdgeId>,
}

/// One edge of the acyclic condensation graph used for summary sequencing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryRegionEdge {
    pub source: SummaryRegionId,
    pub target: SummaryRegionId,
    pub cfg_edges: BTreeSet<CfgEdgeId>,
}

/// Acyclic region graph derived from the CFG SCC condensation.
///
/// This is the structural hook used by the driver to see "summary sites"
/// rather than raw instruction nodes. Loop regions remain explicit, while the
/// rest of the graph becomes a DAG that can be summarized in topological
/// order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryStructure {
    regions: BTreeMap<SummaryRegionId, SummaryRegion>,
    edges: Vec<SummaryRegionEdge>,
    topological_order: Vec<SummaryRegionId>,
    node_regions: BTreeMap<CfgNodeId, SummaryRegionId>,
}

impl SummaryStructure {
    pub fn regions(&self) -> &BTreeMap<SummaryRegionId, SummaryRegion> {
        &self.regions
    }

    pub fn edges(&self) -> &[SummaryRegionEdge] {
        &self.edges
    }

    pub fn topological_order(&self) -> &[SummaryRegionId] {
        &self.topological_order
    }

    pub fn region_for_node(&self, node: CfgNodeId) -> Option<SummaryRegionId> {
        self.node_regions.get(&node).copied()
    }

    pub fn has_loops(&self) -> bool {
        self.regions
            .values()
            .any(|region| matches!(region.kind, SummaryRegionKind::Loop { .. }))
    }
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

    pub fn extract_loops(&self) -> Vec<LoopRegion> {
        let sccs = self.strongly_connected_components();
        let mut loops = Vec::new();
        for body in sccs {
            if !self.is_loop_body(&body) {
                continue;
            }

            loops.push(self.loop_region_from_body(body, loops.len()));
        }
        loops
    }

    /// Builds the acyclic SCC-condensation view used for loop-aware summary
    /// scheduling.
    pub fn summary_structure(&self) -> SummaryStructure {
        let sccs = self.strongly_connected_components();
        let mut regions = BTreeMap::<SummaryRegionId, SummaryRegion>::new();
        let mut node_regions = BTreeMap::<CfgNodeId, SummaryRegionId>::new();
        let mut next_loop_id = 0usize;

        for body in sccs {
            let region_id = SummaryRegionId(regions.len());
            let (entry_edges, exit_edges) = self.component_boundary_edges(&body);
            let kind = if self.is_loop_body(&body) {
                let loop_id = next_loop_id;
                next_loop_id += 1;
                SummaryRegionKind::Loop { loop_id }
            } else {
                SummaryRegionKind::StraightLine
            };
            for node in &body {
                node_regions.insert(*node, region_id);
            }
            regions.insert(
                region_id,
                SummaryRegion {
                    id: region_id,
                    kind,
                    nodes: body,
                    entry_edges,
                    exit_edges,
                },
            );
        }

        let mut edge_map =
            BTreeMap::<(SummaryRegionId, SummaryRegionId), BTreeSet<CfgEdgeId>>::new();
        for (edge_id, edge) in &self.edges {
            let source_region = node_regions[&edge.source];
            let target_region = node_regions[&edge.target];
            if source_region == target_region {
                continue;
            }
            edge_map
                .entry((source_region, target_region))
                .or_default()
                .insert(*edge_id);
        }

        let mut edges = edge_map
            .into_iter()
            .map(|((source, target), cfg_edges)| SummaryRegionEdge {
                source,
                target,
                cfg_edges,
            })
            .collect::<Vec<_>>();
        edges.sort_by_key(|edge| (edge.source, edge.target));

        let topological_order = topological_summary_order(&regions, &edges);
        SummaryStructure {
            regions,
            edges,
            topological_order,
            node_regions,
        }
    }

    fn strongly_connected_components(&self) -> Vec<BTreeSet<CfgNodeId>> {
        struct Tarjan<'a> {
            cfg: &'a Cfg,
            next_index: usize,
            index: BTreeMap<CfgNodeId, usize>,
            lowlink: BTreeMap<CfgNodeId, usize>,
            stack: Vec<CfgNodeId>,
            on_stack: BTreeSet<CfgNodeId>,
            components: Vec<BTreeSet<CfgNodeId>>,
        }

        impl<'a> Tarjan<'a> {
            fn new(cfg: &'a Cfg) -> Self {
                Self {
                    cfg,
                    next_index: 0,
                    index: BTreeMap::new(),
                    lowlink: BTreeMap::new(),
                    stack: Vec::new(),
                    on_stack: BTreeSet::new(),
                    components: Vec::new(),
                }
            }

            fn visit(&mut self, node: CfgNodeId) {
                self.index.insert(node, self.next_index);
                self.lowlink.insert(node, self.next_index);
                self.next_index += 1;
                self.stack.push(node);
                self.on_stack.insert(node);

                let outgoing = self
                    .cfg
                    .edges
                    .values()
                    .filter(|edge| edge.source == node)
                    .map(|edge| edge.target)
                    .collect::<Vec<_>>();
                for successor in outgoing {
                    if !self.index.contains_key(&successor) {
                        self.visit(successor);
                        let successor_low = self.lowlink[&successor];
                        let node_low = self.lowlink[&node];
                        self.lowlink.insert(node, node_low.min(successor_low));
                    } else if self.on_stack.contains(&successor) {
                        let successor_index = self.index[&successor];
                        let node_low = self.lowlink[&node];
                        self.lowlink.insert(node, node_low.min(successor_index));
                    }
                }

                if self.lowlink[&node] == self.index[&node] {
                    let mut component = BTreeSet::new();
                    loop {
                        let top = self
                            .stack
                            .pop()
                            .expect("Tarjan stack should contain the current SCC");
                        self.on_stack.remove(&top);
                        component.insert(top);
                        if top == node {
                            break;
                        }
                    }
                    self.components.push(component);
                }
            }
        }

        let mut tarjan = Tarjan::new(self);
        for node in self.nodes.keys().copied() {
            if !tarjan.index.contains_key(&node) {
                tarjan.visit(node);
            }
        }
        tarjan.components
    }

    fn is_loop_body(&self, body: &BTreeSet<CfgNodeId>) -> bool {
        let is_self_loop = body.len() == 1
            && body.iter().copied().any(|node| {
                self.edges
                    .values()
                    .any(|edge| edge.source == node && edge.target == node)
            });
        body.len() > 1 || is_self_loop
    }

    fn component_boundary_edges(
        &self,
        body: &BTreeSet<CfgNodeId>,
    ) -> (BTreeSet<CfgEdgeId>, BTreeSet<CfgEdgeId>) {
        let mut entry_edges = BTreeSet::new();
        let mut exit_edges = BTreeSet::new();
        for (edge_id, edge) in &self.edges {
            let source_in = body.contains(&edge.source);
            let target_in = body.contains(&edge.target);
            match (source_in, target_in) {
                (false, true) => {
                    entry_edges.insert(*edge_id);
                }
                (true, false) => {
                    exit_edges.insert(*edge_id);
                }
                _ => {}
            }
        }
        (entry_edges, exit_edges)
    }

    fn loop_region_from_body(&self, body: BTreeSet<CfgNodeId>, id: usize) -> LoopRegion {
        let (entry_edges, exit_edges) = self.component_boundary_edges(&body);
        let mut headers = BTreeSet::new();
        for edge_id in &entry_edges {
            let edge = self
                .edges
                .get(edge_id)
                .expect("loop entry edges should refer to existing CFG edges");
            headers.insert(edge.target);
        }

        if headers.is_empty() {
            if body.contains(&self.entry) {
                headers.insert(self.entry);
            } else if let Some(first) = body.iter().next().copied() {
                headers.insert(first);
            }
        }

        let mut back_edges = BTreeSet::new();
        for (edge_id, edge) in &self.edges {
            if body.contains(&edge.source) && headers.contains(&edge.target) {
                back_edges.insert(*edge_id);
            }
        }

        LoopRegion {
            id,
            headers,
            body,
            entry_edges,
            exit_edges,
            back_edges,
        }
    }
}

fn topological_summary_order(
    regions: &BTreeMap<SummaryRegionId, SummaryRegion>,
    edges: &[SummaryRegionEdge],
) -> Vec<SummaryRegionId> {
    let mut incoming = regions
        .keys()
        .copied()
        .map(|region| (region, 0usize))
        .collect::<BTreeMap<_, _>>();
    let mut outgoing = BTreeMap::<SummaryRegionId, Vec<SummaryRegionId>>::new();
    for edge in edges {
        *incoming
            .get_mut(&edge.target)
            .expect("summary edge target should be a known region") += 1;
        outgoing.entry(edge.source).or_default().push(edge.target);
    }

    let mut ready = incoming
        .iter()
        .filter_map(|(region, indegree)| (*indegree == 0).then_some(*region))
        .collect::<Vec<_>>();
    let mut order = Vec::new();
    while let Some(region) = ready.pop() {
        order.push(region);
        let mut successors = outgoing.get(&region).cloned().unwrap_or_default();
        successors.sort();
        for successor in successors {
            let indegree = incoming
                .get_mut(&successor)
                .expect("summary successor should be a known region");
            *indegree -= 1;
            if *indegree == 0 {
                ready.push(successor);
                ready.sort_by(|lhs, rhs| rhs.cmp(lhs));
            }
        }
    }
    order
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

    #[test]
    fn scc_loop_extraction_finds_headers_and_exit_edges() {
        let mut cfg = Cfg::new("entry");
        let header = cfg.add_node("header");
        let body = cfg.add_node("body");
        let exit = cfg.add_node("exit");
        cfg.mark_exit(exit).unwrap();
        let into_loop = cfg.add_edge(cfg.entry(), header, Formula::True).unwrap();
        cfg.add_edge(header, body, Formula::True).unwrap();
        let back = cfg.add_edge(body, header, Formula::True).unwrap();
        let leave = cfg.add_edge(body, exit, Formula::True).unwrap();

        let loops = cfg.extract_loops();
        assert_eq!(loops.len(), 1);
        let loop_region = &loops[0];
        assert!(loop_region.headers.contains(&header));
        assert!(loop_region.body.contains(&header));
        assert!(loop_region.body.contains(&body));
        assert!(loop_region.entry_edges.contains(&into_loop));
        assert!(loop_region.back_edges.contains(&back));
        assert!(loop_region.exit_edges.contains(&leave));
    }

    #[test]
    fn self_loop_is_reported_as_a_loop_region() {
        let mut cfg = Cfg::new("entry");
        let loop_node = cfg.add_node("loop");
        cfg.add_edge(cfg.entry(), loop_node, Formula::True).unwrap();
        cfg.add_edge(loop_node, loop_node, Formula::True).unwrap();
        cfg.mark_exit(loop_node).unwrap();

        let loops = cfg.extract_loops();
        assert_eq!(loops.len(), 1);
        assert!(loops[0].body.contains(&loop_node));
    }

    #[test]
    fn summary_structure_keeps_loops_as_explicit_regions() {
        let mut cfg = Cfg::new("entry");
        let pre = cfg.add_node("pre");
        let header = cfg.add_node("header");
        let body = cfg.add_node("body");
        let exit = cfg.add_node("exit");
        cfg.mark_exit(exit).unwrap();
        cfg.add_edge(cfg.entry(), pre, Formula::True).unwrap();
        cfg.add_edge(pre, header, Formula::True).unwrap();
        cfg.add_edge(header, body, Formula::True).unwrap();
        cfg.add_edge(body, header, Formula::True).unwrap();
        cfg.add_edge(body, exit, Formula::True).unwrap();

        let structure = cfg.summary_structure();
        assert!(structure.has_loops());

        let header_region = structure.region_for_node(header).unwrap();
        let body_region = structure.region_for_node(body).unwrap();
        assert_eq!(header_region, body_region);
        assert!(matches!(
            structure.regions()[&header_region].kind,
            SummaryRegionKind::Loop { .. }
        ));

        let pre_region = structure.region_for_node(pre).unwrap();
        let exit_region = structure.region_for_node(exit).unwrap();
        assert_ne!(pre_region, header_region);
        assert_ne!(exit_region, header_region);
        let order = structure.topological_order();
        let pre_index = order
            .iter()
            .position(|region| *region == pre_region)
            .unwrap();
        let loop_index = order
            .iter()
            .position(|region| *region == header_region)
            .unwrap();
        let exit_index = order
            .iter()
            .position(|region| *region == exit_region)
            .unwrap();
        assert!(pre_index < loop_index);
        assert!(loop_index < exit_index);
        assert!(structure
            .edges()
            .iter()
            .any(|edge| edge.source == pre_region && edge.target == header_region));
        assert!(structure
            .edges()
            .iter()
            .any(|edge| edge.source == header_region && edge.target == exit_region));
    }

    #[test]
    fn acyclic_cfg_summary_structure_has_no_loop_regions() {
        let mut cfg = Cfg::new("entry");
        let left = cfg.add_node("left");
        let right = cfg.add_node("right");
        let exit = cfg.add_node("exit");
        cfg.mark_exit(exit).unwrap();
        cfg.add_edge(cfg.entry(), left, Formula::True).unwrap();
        cfg.add_edge(cfg.entry(), right, Formula::True).unwrap();
        cfg.add_edge(left, exit, Formula::True).unwrap();
        cfg.add_edge(right, exit, Formula::True).unwrap();

        let structure = cfg.summary_structure();
        assert!(!structure.has_loops());
        assert_eq!(structure.regions().len(), cfg.nodes().len());
        assert!(structure
            .regions()
            .values()
            .all(|region| matches!(region.kind, SummaryRegionKind::StraightLine)));
    }
}
