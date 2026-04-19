//! Analysis state in the notation of the paper.
//!
//! Paper correspondence:
//!
//! ```text
//! Partition at node n     -> Pi_n
//! must-reachable states   -> Omega_n
//! MayEdge set             -> N_e
//! Region                  -> phi_i inside Pi_n
//! ```

use crate::analysis::formula::Predicate;
use crate::analysis::vocabulary::{EdgeId, NodeId, RegionId};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Region {
    pub id: RegionId,
    pub predicate: Predicate,
}

impl Region {
    pub fn new(id: RegionId, predicate: Predicate) -> Self {
        Self { id, predicate }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Partition {
    regions: BTreeMap<RegionId, Region>,
}

impl Partition {
    pub fn new(regions: impl IntoIterator<Item = Region>) -> Self {
        Self {
            regions: regions
                .into_iter()
                .map(|region| (region.id, region))
                .collect(),
        }
    }

    pub fn top() -> Self {
        Self::new([Region::new(RegionId(0), Predicate::True)])
    }

    pub fn region(&self, id: RegionId) -> Option<&Region> {
        self.regions.get(&id)
    }

    pub fn regions(&self) -> impl Iterator<Item = &Region> {
        self.regions.values()
    }

    pub fn replace_with_split(
        &mut self,
        old: RegionId,
        left: Predicate,
        right: Predicate,
    ) -> Option<(RegionId, RegionId)> {
        self.regions.remove(&old)?;
        let left_id = next_region_id(self.regions.keys().copied());
        let right_id = RegionId(left_id.0 + 1);
        self.regions.insert(left_id, Region::new(left_id, left));
        self.regions.insert(right_id, Region::new(right_id, right));
        Some((left_id, right_id))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PaperAnalysisState {
    /// `Pi_n`: partition at each node.
    partitions: BTreeMap<NodeId, Partition>,
    /// `Omega_n`: under-approximate must-reachable states at each node.
    omega: BTreeMap<NodeId, Predicate>,
    /// `Ne`: may edges between partition regions.  The paper uses this to
    /// track abstract reachability/refinement.  We store identifiers here and
    /// leave graph algorithms to the driver.
    may_edges: BTreeSet<MayEdge>,
}

impl PaperAnalysisState {
    pub fn new() -> Self {
        Self {
            partitions: BTreeMap::new(),
            omega: BTreeMap::new(),
            may_edges: BTreeSet::new(),
        }
    }

    pub fn set_partition(&mut self, node: NodeId, partition: Partition) {
        self.partitions.insert(node, partition);
    }

    pub fn partition(&self, node: NodeId) -> Option<&Partition> {
        self.partitions.get(&node)
    }

    pub fn partition_mut(&mut self, node: NodeId) -> Option<&mut Partition> {
        self.partitions.get_mut(&node)
    }

    pub fn omega(&self, node: NodeId) -> Predicate {
        self.omega.get(&node).cloned().unwrap_or(Predicate::False)
    }

    pub fn set_omega(&mut self, node: NodeId, states: Predicate) {
        self.omega.insert(node, states);
    }

    pub fn add_omega(&mut self, node: NodeId, states: Predicate) {
        let current = self.omega(node);
        self.omega.insert(node, current.union(states));
    }

    pub fn add_may_edge(&mut self, may_edge: MayEdge) {
        self.may_edges.insert(may_edge);
    }

    pub fn may_edges(&self) -> impl Iterator<Item = &MayEdge> {
        self.may_edges.iter()
    }
}

impl Default for PaperAnalysisState {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MayEdge {
    pub edge: EdgeId,
    pub from_region: RegionId,
    pub to_region: RegionId,
}

impl MayEdge {
    pub fn new(edge: EdgeId, from_region: RegionId, to_region: RegionId) -> Self {
        Self {
            edge,
            from_region,
            to_region,
        }
    }
}

fn next_region_id(existing: impl IntoIterator<Item = RegionId>) -> RegionId {
    existing
        .into_iter()
        .map(|id| id.0)
        .max()
        .map(|id| RegionId(id + 1))
        .unwrap_or(RegionId(0))
}
