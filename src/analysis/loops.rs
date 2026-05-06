//! Loop-region extraction and condensation over the paper CFG.
//!
//! `cfg.rs` owns the structural control-flow graph `P`. This module derives
//! loop-facing views from that graph:
//!
//! - SCC-based `LoopRegion` values
//! - an acyclic condensation `SummaryStructure`
//!
//! The driver consumes this module when it decides whether a procedure still
//! needs loop invariants before the Figure 5-10 rule slice can run.

use crate::analysis::cfg::{Cfg, CfgEdgeId, CfgNodeId};
use crate::analysis::formula::{Formula, Var};
use crate::analysis::oracle::{Oracle, OracleError, Validity};
use crate::analysis::summaries::{MustSummary, NotMaySummary};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use thiserror::Error;
use tokio::runtime::{Builder, Runtime};

/// SCC-based loop region extracted from one CFG.
///
/// Headers are the nodes in the SCC that receive control from outside the loop
/// body. For reducible LLVM loops this set is usually a singleton; multiple
/// headers indicate an irreducible cycle.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LoopRegion {
    pub id: usize,
    pub headers: BTreeSet<CfgNodeId>,
    pub body: BTreeSet<CfgNodeId>,
    pub entry_edges: BTreeSet<CfgEdgeId>,
    pub exit_edges: BTreeSet<CfgEdgeId>,
    pub back_edges: BTreeSet<CfgEdgeId>,
}

/// Stable identifier for one condensation region in the summary structure.
#[derive(
    Clone, Copy, Debug, Default, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize,
)]
pub struct SummaryRegionId(pub usize);

/// Summary-facing classification of one condensation region.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
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
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SummaryRegion {
    pub id: SummaryRegionId,
    pub kind: SummaryRegionKind,
    pub nodes: BTreeSet<CfgNodeId>,
    pub entry_edges: BTreeSet<CfgEdgeId>,
    pub exit_edges: BTreeSet<CfgEdgeId>,
}

/// One edge of the acyclic condensation graph used for summary sequencing.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
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
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
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

/// Summary-facing procedure interface passed to external loop/function modules.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SummaryInterface {
    pub parameters: Vec<String>,
    pub return_value: Option<Var>,
    pub visible_memory_roots: Vec<String>,
}

/// Formula bundle returned by loop/function summary generation.
///
/// `predicate` carries the scalar/state part of the summary, while
/// `memory_summaries` carries additional facts over visible memory ports.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct FormulaSummary {
    pub predicate: Formula,
    pub memory_summaries: Vec<Formula>,
}

/// External request for one loop invariant or loop summary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LoopSummaryRequest {
    pub procedure: String,
    pub interface: SummaryInterface,
    pub loop_region: LoopRegion,
    pub summary_structure: SummaryStructure,
}

/// External request for one function summary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct FunctionSummaryRequest {
    pub procedure: String,
    pub interface: SummaryInterface,
    pub loops: Vec<LoopRegion>,
    pub summary_structure: SummaryStructure,
}

/// Loop summary returned by an internal or external generator.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LoopSummaryResponse {
    pub invariant: FormulaSummary,
}

/// Function summaries returned by an internal or external generator.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct FunctionSummaryResponse {
    pub must_summaries: Vec<MustSummary>,
    pub notmay_summaries: Vec<NotMaySummary>,
    pub memory_summaries: Vec<Formula>,
}

/// Summary-generation request sent through the Tokio-backed placeholder.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SummaryGenerationRequest {
    Loop(LoopSummaryRequest),
    Function(FunctionSummaryRequest),
}

/// Summary-generation response sent back through the Tokio-backed placeholder.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SummaryGenerationResponse {
    Loop(LoopSummaryResponse),
    Function(FunctionSummaryResponse),
}

/// Direction of the Knaster-Tarski iteration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedPointKind {
    Least,
    Greatest,
}

/// Generic Knaster-Tarski style loop summary generator.
///
/// The current engine is intentionally structural: it iterates a monotone
/// summary transformer until SMT equivalence stabilizes. The driver can use it
/// directly or wrap it behind the Tokio summary-service boundary for external
/// modules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KnasterTarskiLoopSummaryGenerator {
    pub max_iterations: usize,
}

impl Default for KnasterTarskiLoopSummaryGenerator {
    fn default() -> Self {
        Self { max_iterations: 16 }
    }
}

impl KnasterTarskiLoopSummaryGenerator {
    pub fn generate<F>(
        &self,
        oracle: &Oracle,
        request: &LoopSummaryRequest,
        kind: FixedPointKind,
        transformer: F,
    ) -> Result<LoopSummaryResponse, LoopAnalysisError>
    where
        F: Fn(&LoopSummaryRequest, &LoopSummaryResponse) -> LoopSummaryResponse,
    {
        let mut current = match kind {
            FixedPointKind::Least => LoopSummaryResponse {
                invariant: FormulaSummary {
                    predicate: Formula::False,
                    memory_summaries: Vec::new(),
                },
            },
            FixedPointKind::Greatest => LoopSummaryResponse {
                invariant: FormulaSummary {
                    predicate: Formula::True,
                    memory_summaries: request
                        .interface
                        .visible_memory_roots
                        .iter()
                        .map(|root| {
                            Formula::memory_eq(
                                crate::analysis::formula::Memory::var(format!("{root}$mem_out")),
                                crate::analysis::formula::Memory::var(format!("{root}$mem_in")),
                            )
                        })
                        .collect(),
                },
            },
        };

        for _ in 0..self.max_iterations {
            let next = transformer(request, &current);
            if summaries_equivalent(oracle, &current, &next)? {
                return Ok(next);
            }
            current = next;
        }

        Err(LoopAnalysisError::FixedPointDidNotConverge {
            procedure: request.procedure.clone(),
            loop_id: request.loop_region.id,
            max_iterations: self.max_iterations,
        })
    }
}

/// Plug-in boundary for loop and function summary generation.
///
/// The driver talks to this trait instead of to a specific implementation so
/// it can use either an internal algorithm or an external module that returns
/// JSON.
pub trait SummaryGenerator: Send + Sync {
    fn generate_loop_summary(
        &self,
        oracle: &Oracle,
        request: &LoopSummaryRequest,
    ) -> Result<LoopSummaryResponse, LoopAnalysisError>;

    fn generate_function_summary(
        &self,
        oracle: &Oracle,
        request: &FunctionSummaryRequest,
    ) -> Result<FunctionSummaryResponse, LoopAnalysisError>;
}

impl SummaryGenerator for KnasterTarskiLoopSummaryGenerator {
    fn generate_loop_summary(
        &self,
        oracle: &Oracle,
        request: &LoopSummaryRequest,
    ) -> Result<LoopSummaryResponse, LoopAnalysisError> {
        self.generate(
            oracle,
            request,
            FixedPointKind::Greatest,
            |_request, current| current.clone(),
        )
    }

    fn generate_function_summary(
        &self,
        _oracle: &Oracle,
        _request: &FunctionSummaryRequest,
    ) -> Result<FunctionSummaryResponse, LoopAnalysisError> {
        Ok(FunctionSummaryResponse {
            must_summaries: Vec::new(),
            notmay_summaries: Vec::new(),
            memory_summaries: Vec::new(),
        })
    }
}

type SummaryJsonFuture = Pin<Box<dyn Future<Output = String> + Send + 'static>>;
type SummaryJsonHandler =
    Arc<dyn Fn(SummaryGenerationRequest) -> SummaryJsonFuture + Send + Sync + 'static>;

/// Tokio-backed external summary generator that parses JSON payloads.
#[derive(Clone)]
pub struct TokioJsonSummaryGenerator {
    runtime: Arc<Runtime>,
    handler: SummaryJsonHandler,
}

impl TokioJsonSummaryGenerator {
    pub fn new(handler: SummaryJsonHandler) -> Result<Self, LoopAnalysisError> {
        let runtime = Arc::new(
            Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|error| LoopAnalysisError::TokioRuntime(error.to_string()))?,
        );
        Ok(Self { runtime, handler })
    }

    pub fn from_handler<F, Fut>(handler: F) -> Result<Self, LoopAnalysisError>
    where
        F: Fn(SummaryGenerationRequest) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = String> + Send + 'static,
    {
        Self::new(Arc::new(move |request| Box::pin(handler(request))))
    }
}

impl SummaryGenerator for TokioJsonSummaryGenerator {
    fn generate_loop_summary(
        &self,
        _oracle: &Oracle,
        request: &LoopSummaryRequest,
    ) -> Result<LoopSummaryResponse, LoopAnalysisError> {
        let json = self
            .runtime
            .block_on((self.handler)(SummaryGenerationRequest::Loop(
                request.clone(),
            )));
        match serde_json::from_str::<SummaryGenerationResponse>(&json)
            .map_err(|error| LoopAnalysisError::Json(error.to_string()))?
        {
            SummaryGenerationResponse::Loop(response) => Ok(response),
            SummaryGenerationResponse::Function(_) => {
                Err(LoopAnalysisError::UnexpectedSummaryKind {
                    expected: "loop".to_string(),
                    received: "function".to_string(),
                })
            }
        }
    }

    fn generate_function_summary(
        &self,
        _oracle: &Oracle,
        request: &FunctionSummaryRequest,
    ) -> Result<FunctionSummaryResponse, LoopAnalysisError> {
        let json = self
            .runtime
            .block_on((self.handler)(SummaryGenerationRequest::Function(
                request.clone(),
            )));
        match serde_json::from_str::<SummaryGenerationResponse>(&json)
            .map_err(|error| LoopAnalysisError::Json(error.to_string()))?
        {
            SummaryGenerationResponse::Function(response) => Ok(response),
            SummaryGenerationResponse::Loop(_) => Err(LoopAnalysisError::UnexpectedSummaryKind {
                expected: "function".to_string(),
                received: "loop".to_string(),
            }),
        }
    }
}

/// Loop-analysis failures and external summary-service errors.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum LoopAnalysisError {
    #[error("tokio runtime construction failed: {0}")]
    TokioRuntime(String),
    #[error("json summary payload could not be parsed: {0}")]
    Json(String),
    #[error("expected a {expected} summary response but received {received}")]
    UnexpectedSummaryKind { expected: String, received: String },
    #[error(
        "Knaster-Tarski iteration did not converge for procedure {procedure} loop {loop_id} within {max_iterations} iterations"
    )]
    FixedPointDidNotConverge {
        procedure: String,
        loop_id: usize,
        max_iterations: usize,
    },
    #[error("oracle query failed while checking loop-summary convergence: {0}")]
    Oracle(#[from] OracleError),
}

/// Extracts loop SCCs from the lowered CFG.
pub fn extract_loops(cfg: &Cfg) -> Vec<LoopRegion> {
    let sccs = strongly_connected_components(cfg);
    let mut loops = Vec::new();
    for body in sccs {
        if !is_loop_body(cfg, &body) {
            continue;
        }

        loops.push(loop_region_from_body(cfg, body, loops.len()));
    }
    loops
}

/// Builds the acyclic SCC-condensation view used for loop-aware summary
/// scheduling.
pub fn summary_structure(cfg: &Cfg) -> SummaryStructure {
    let sccs = strongly_connected_components(cfg);
    let mut regions = BTreeMap::<SummaryRegionId, SummaryRegion>::new();
    let mut node_regions = BTreeMap::<CfgNodeId, SummaryRegionId>::new();
    let mut next_loop_id = 0usize;

    for body in sccs {
        let region_id = SummaryRegionId(regions.len());
        let (entry_edges, exit_edges) = component_boundary_edges(cfg, &body);
        let kind = if is_loop_body(cfg, &body) {
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

    let mut edge_map = BTreeMap::<(SummaryRegionId, SummaryRegionId), BTreeSet<CfgEdgeId>>::new();
    for (edge_id, edge) in cfg.edges() {
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

fn summaries_equivalent(
    oracle: &Oracle,
    lhs: &LoopSummaryResponse,
    rhs: &LoopSummaryResponse,
) -> Result<bool, LoopAnalysisError> {
    let lhs_formula = summarize_formula_bundle(&lhs.invariant);
    let rhs_formula = summarize_formula_bundle(&rhs.invariant);
    let lhs_implies_rhs = oracle.implies(&lhs_formula, &rhs_formula)?;
    let rhs_implies_lhs = oracle.implies(&rhs_formula, &lhs_formula)?;
    Ok(lhs_implies_rhs == Validity::Valid && rhs_implies_lhs == Validity::Valid)
}

fn summarize_formula_bundle(bundle: &FormulaSummary) -> Formula {
    Formula::and_all(
        std::iter::once(bundle.predicate.clone())
            .chain(bundle.memory_summaries.clone())
            .collect::<Vec<_>>(),
    )
}

fn strongly_connected_components(cfg: &Cfg) -> Vec<BTreeSet<CfgNodeId>> {
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
                .edges()
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

    let mut tarjan = Tarjan::new(cfg);
    for node in cfg.nodes().keys().copied() {
        if !tarjan.index.contains_key(&node) {
            tarjan.visit(node);
        }
    }
    tarjan.components
}

fn is_loop_body(cfg: &Cfg, body: &BTreeSet<CfgNodeId>) -> bool {
    let is_self_loop = body.len() == 1
        && body.iter().copied().any(|node| {
            cfg.edges()
                .values()
                .any(|edge| edge.source == node && edge.target == node)
        });
    body.len() > 1 || is_self_loop
}

fn component_boundary_edges(
    cfg: &Cfg,
    body: &BTreeSet<CfgNodeId>,
) -> (BTreeSet<CfgEdgeId>, BTreeSet<CfgEdgeId>) {
    let mut entry_edges = BTreeSet::new();
    let mut exit_edges = BTreeSet::new();
    for (edge_id, edge) in cfg.edges() {
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

fn loop_region_from_body(cfg: &Cfg, body: BTreeSet<CfgNodeId>, id: usize) -> LoopRegion {
    let (entry_edges, exit_edges) = component_boundary_edges(cfg, &body);
    let mut headers = BTreeSet::new();
    for edge_id in &entry_edges {
        let edge = cfg
            .edge(*edge_id)
            .expect("loop entry edges should refer to existing CFG edges");
        headers.insert(edge.target);
    }

    if headers.is_empty() {
        if body.contains(&cfg.entry()) {
            headers.insert(cfg.entry());
        } else if let Some(first) = body.iter().next().copied() {
            headers.insert(first);
        }
    }

    let mut back_edges = BTreeSet::new();
    for (edge_id, edge) in cfg.edges() {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::cfg::{Cfg, CfgNodeKind};
    use crate::analysis::formula::{Formula, Sort, Term};
    use crate::analysis::oracle::Oracle;

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

        let loops = extract_loops(&cfg);
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

        let loops = extract_loops(&cfg);
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

        let structure = summary_structure(&cfg);
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

        let structure = summary_structure(&cfg);
        assert!(!structure.has_loops());
        assert_eq!(structure.regions().len(), cfg.nodes().len());
        assert!(structure
            .regions()
            .values()
            .all(|region| matches!(region.kind, SummaryRegionKind::StraightLine)));
    }

    #[test]
    fn cfg_single_exit_behavior_is_still_available_to_loop_analysis_tests() {
        let mut cfg = Cfg::new("entry");
        let exit = cfg.add_node("exit");
        cfg.mark_exit(exit).unwrap();
        assert_eq!(cfg.node(exit).unwrap().kind, CfgNodeKind::Exit);
        let relation = Formula::gt(Term::var("x", Sort::Int), Term::int(0));
        let edge = cfg.add_edge(cfg.entry(), exit, relation.clone()).unwrap();
        assert_eq!(cfg.edge(edge).unwrap().relation, relation);
    }

    #[test]
    fn knaster_tarski_generator_converges_on_a_constant_candidate() {
        let mut cfg = Cfg::new("entry");
        let header = cfg.add_node("header");
        cfg.add_edge(cfg.entry(), header, Formula::True).unwrap();
        cfg.add_edge(header, header, Formula::True).unwrap();
        cfg.mark_exit(header).unwrap();

        let loop_region = extract_loops(&cfg).into_iter().next().unwrap();
        let request = LoopSummaryRequest {
            procedure: "main".to_string(),
            interface: SummaryInterface {
                parameters: Vec::new(),
                return_value: None,
                visible_memory_roots: Vec::new(),
            },
            loop_region,
            summary_structure: summary_structure(&cfg),
        };
        let generator = KnasterTarskiLoopSummaryGenerator { max_iterations: 4 };
        let oracle = Oracle::new();

        let summary = generator
            .generate(
                &oracle,
                &request,
                FixedPointKind::Least,
                |_request, _current| LoopSummaryResponse {
                    invariant: FormulaSummary {
                        predicate: Formula::gt(Term::var("x", Sort::Int), Term::int(0)),
                        memory_summaries: Vec::new(),
                    },
                },
            )
            .unwrap();
        assert_eq!(
            summary.invariant.predicate,
            Formula::gt(Term::var("x", Sort::Int), Term::int(0))
        );
    }

    #[test]
    fn tokio_json_generator_parses_loop_summary_payloads() {
        let mut cfg = Cfg::new("entry");
        let header = cfg.add_node("header");
        cfg.add_edge(cfg.entry(), header, Formula::True).unwrap();
        cfg.add_edge(header, header, Formula::True).unwrap();
        cfg.mark_exit(header).unwrap();

        let loop_region = extract_loops(&cfg).into_iter().next().unwrap();
        let request = LoopSummaryRequest {
            procedure: "main".to_string(),
            interface: SummaryInterface {
                parameters: Vec::new(),
                return_value: None,
                visible_memory_roots: vec!["%mem".to_string()],
            },
            loop_region,
            summary_structure: summary_structure(&cfg),
        };
        let generator = TokioJsonSummaryGenerator::from_handler(|request| async move {
            match request {
                SummaryGenerationRequest::Loop(_) => {
                    serde_json::to_string(&SummaryGenerationResponse::Loop(LoopSummaryResponse {
                        invariant: FormulaSummary {
                            predicate: Formula::bool_var("inv"),
                            memory_summaries: vec![Formula::memory_eq(
                                crate::analysis::formula::Memory::var("%mem$mem_out"),
                                crate::analysis::formula::Memory::var("%mem$mem_in"),
                            )],
                        },
                    }))
                    .unwrap()
                }
                SummaryGenerationRequest::Function(_) => serde_json::to_string(
                    &SummaryGenerationResponse::Function(FunctionSummaryResponse {
                        must_summaries: Vec::new(),
                        notmay_summaries: Vec::new(),
                        memory_summaries: Vec::new(),
                    }),
                )
                .unwrap(),
            }
        })
        .unwrap();

        let summary = generator
            .generate_loop_summary(&Oracle::new(), &request)
            .unwrap();
        assert_eq!(summary.invariant.predicate, Formula::bool_var("inv"));
        assert_eq!(summary.invariant.memory_summaries.len(), 1);
    }
}
