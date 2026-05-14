#![allow(dead_code)]

use crate::common::formula::{Formula, Memory, Term, Var};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use thiserror::Error;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct CfgNodeId(pub usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct CfgEdgeId(pub usize);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl SourceLocation {
    pub fn new(file: impl Into<String>, line: u32, column: u32) -> Self {
        Self {
            file: file.into(),
            line,
            column,
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.file.is_empty() {
            if self.column == 0 {
                write!(f, "<unknown>:{}", self.line)
            } else {
                write!(f, "<unknown>:{}:{}", self.line, self.column)
            }
        } else if self.column == 0 {
            write!(f, "{}:{}", self.file, self.line)
        } else {
            write!(f, "{}:{}:{}", self.file, self.line, self.column)
        }
    }
}

impl From<crate::common::source::SourceLocation> for SourceLocation {
    fn from(value: crate::common::source::SourceLocation) -> Self {
        SourceLocation::new(value.file, value.line, value.column)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CallMemoryEffect {
    PreservesMemory,
    HavocMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AssignValue {
    Term(Term),
    Predicate(Formula),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TransferEffect {
    Assign {
        target: Var,
        value: AssignValue,
    },
    Alloca {
        target: String,
        region: String,
    },
    GetElementPtr {
        target: String,
        base: String,
        offset: Term,
    },
    Load {
        target: Var,
        source: String,
    },
    Store {
        target: String,
        value: Term,
    },
    MemoryStore {
        region: String,
        offset: Term,
        value: Term,
    },
    PointerStore {
        target_slot: String,
        value_ptr: String,
    },
    PointerLoad {
        target_ptr: String,
        source_slot: String,
    },
    Assume(Formula),
    Obligation(Formula),
    Nop,
    Call {
        callee: String,
        memory_effect: CallMemoryEffect,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct TransferFn {
    pub effects: Vec<TransferEffect>,
}

impl TransferFn {
    pub fn new(effects: Vec<TransferEffect>) -> Self {
        Self { effects }
    }

    pub fn identity() -> Self {
        Self::default()
    }

    pub fn is_identity(&self) -> bool {
        self.effects.is_empty()
    }

    pub fn wp(&self, post: &Formula) -> Formula {
        self.effects
            .iter()
            .rev()
            .fold(post.clone(), |acc, effect| wp_one(effect, &acc))
    }

    pub fn sp(&self, pre: &Formula) -> Formula {
        self.effects
            .iter()
            .fold(pre.clone(), |acc, effect| sp_one(effect, &acc))
    }

    pub fn pointer_resolution(&self) -> PointerEnv {
        let mut env = PointerEnv::default();
        for effect in &self.effects {
            match effect {
                TransferEffect::Alloca { target, region } => {
                    env.bind(target.clone(), region.clone(), Term::int(0));
                }
                TransferEffect::GetElementPtr {
                    target,
                    base,
                    offset,
                } => {
                    if let Some(parent) = env.get(base) {
                        env.bind(
                            target.clone(),
                            parent.region.clone(),
                            Term::add(parent.offset.clone(), offset.clone()),
                        );
                    }
                }
                _ => {}
            }
        }
        env
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct PointerEnv {
    bindings: HashMap<String, PointerBinding>,
}

impl PointerEnv {
    pub fn bind(&mut self, pointer: String, region: String, offset: Term) {
        self.bindings
            .insert(pointer, PointerBinding { region, offset });
    }

    pub fn get(&self, pointer: &str) -> Option<&PointerBinding> {
        self.bindings.get(pointer)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PointerBinding {
    pub region: String,
    pub offset: Term,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum NodeKind {
    Entry,
    Normal,
    Exit,
    SyntheticExit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractNode {
    pub id: CfgNodeId,
    pub label: String,
    pub kind: NodeKind,
    pub source_location: Option<SourceLocation>,
    pub transfer: TransferFn,
    pub pre: Formula,
    pub post: Formula,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractEdge {
    pub id: CfgEdgeId,
    pub source: CfgNodeId,
    pub target: CfgNodeId,
    pub guard: Formula,
    pub effects: Vec<TransferEffect>,
}

impl AbstractEdge {
    pub fn transfer(&self) -> TransferFn {
        TransferFn::new(self.effects.clone())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AbstractCfg {
    nodes: BTreeMap<CfgNodeId, AbstractNode>,
    edges: BTreeMap<CfgEdgeId, AbstractEdge>,
    entry: CfgNodeId,
    concrete_exits: BTreeSet<CfgNodeId>,
    exit: Option<CfgNodeId>,
    next_node: usize,
    next_edge: usize,
}

impl AbstractCfg {
    pub fn new(entry_label: impl Into<String>) -> Self {
        let entry_id = CfgNodeId(0);
        let entry_node = AbstractNode {
            id: entry_id,
            label: entry_label.into(),
            kind: NodeKind::Entry,
            source_location: None,
            transfer: TransferFn::identity(),
            pre: Formula::True,
            post: Formula::True,
        };
        let mut nodes = BTreeMap::new();
        nodes.insert(entry_id, entry_node);
        Self {
            nodes,
            edges: BTreeMap::new(),
            entry: entry_id,
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

    pub fn node(&self, id: CfgNodeId) -> Result<&AbstractNode, CfgError> {
        self.nodes.get(&id).ok_or(CfgError::UnknownNode { id })
    }

    pub fn node_mut(&mut self, id: CfgNodeId) -> Result<&mut AbstractNode, CfgError> {
        self.nodes.get_mut(&id).ok_or(CfgError::UnknownNode { id })
    }

    pub fn edge(&self, id: CfgEdgeId) -> Result<&AbstractEdge, CfgError> {
        self.edges.get(&id).ok_or(CfgError::UnknownEdge { id })
    }

    pub fn nodes(&self) -> &BTreeMap<CfgNodeId, AbstractNode> {
        &self.nodes
    }

    pub fn edges(&self) -> &BTreeMap<CfgEdgeId, AbstractEdge> {
        &self.edges
    }

    pub fn node_ids(&self) -> impl Iterator<Item = CfgNodeId> + '_ {
        self.nodes.keys().copied()
    }

    pub fn edge_ids(&self) -> impl Iterator<Item = CfgEdgeId> + '_ {
        self.edges.keys().copied()
    }

    pub fn add_node(&mut self, label: impl Into<String>, transfer: TransferFn) -> CfgNodeId {
        let id = CfgNodeId(self.next_node);
        self.next_node += 1;
        self.nodes.insert(
            id,
            AbstractNode {
                id,
                label: label.into(),
                kind: NodeKind::Normal,
                source_location: None,
                transfer,
                pre: Formula::True,
                post: Formula::True,
            },
        );
        id
    }

    pub fn set_entry_transfer(&mut self, transfer: TransferFn) {
        if let Some(entry) = self.nodes.get_mut(&self.entry) {
            entry.transfer = transfer;
        }
    }

    pub fn set_source_location(
        &mut self,
        id: CfgNodeId,
        location: SourceLocation,
    ) -> Result<(), CfgError> {
        self.node_mut(id)?.source_location = Some(location);
        Ok(())
    }

    pub fn mark_exit(&mut self, id: CfgNodeId) -> Result<(), CfgError> {
        if id != self.entry {
            self.node_mut(id)?.kind = NodeKind::Exit;
            self.concrete_exits.insert(id);
            self.exit = None;
        }
        Ok(())
    }

    pub fn add_edge(
        &mut self,
        source: CfgNodeId,
        target: CfgNodeId,
        guard: Formula,
        effects: Vec<TransferEffect>,
    ) -> Result<CfgEdgeId, CfgError> {
        if !self.nodes.contains_key(&source) {
            return Err(CfgError::UnknownNode { id: source });
        }
        if !self.nodes.contains_key(&target) {
            return Err(CfgError::UnknownNode { id: target });
        }
        let id = CfgEdgeId(self.next_edge);
        self.next_edge += 1;
        self.edges.insert(
            id,
            AbstractEdge {
                id,
                source,
                target,
                guard,
                effects,
            },
        );
        Ok(id)
    }

    pub fn append_edge_effects(
        &mut self,
        id: CfgEdgeId,
        effects: impl IntoIterator<Item = TransferEffect>,
    ) -> Result<(), CfgError> {
        self.edge_mut(id)?.effects.extend(effects);
        Ok(())
    }

    pub fn successors(&self, id: CfgNodeId) -> Vec<CfgNodeId> {
        self.edges
            .values()
            .filter(|edge| edge.source == id)
            .map(|edge| edge.target)
            .collect()
    }

    pub fn predecessors(&self, id: CfgNodeId) -> Vec<CfgNodeId> {
        self.edges
            .values()
            .filter(|edge| edge.target == id)
            .map(|edge| edge.source)
            .collect()
    }

    pub fn outgoing_edges(&self, id: CfgNodeId) -> Vec<CfgEdgeId> {
        self.edges
            .values()
            .filter(|edge| edge.source == id)
            .map(|edge| edge.id)
            .collect()
    }

    pub fn incoming_edges(&self, id: CfgNodeId) -> Vec<CfgEdgeId> {
        self.edges
            .values()
            .filter(|edge| edge.target == id)
            .map(|edge| edge.id)
            .collect()
    }

    pub fn ensure_single_exit(&mut self) -> Result<CfgNodeId, CfgError> {
        if let Some(exit) = self.exit {
            return Ok(exit);
        }
        match self.concrete_exits.len() {
            0 => Err(CfgError::MissingExit),
            1 => {
                let exit = *self.concrete_exits.iter().next().expect("one exit exists");
                self.exit = Some(exit);
                Ok(exit)
            }
            _ => {
                let synthetic = self.add_node("__synthetic_exit", TransferFn::identity());
                self.node_mut(synthetic)?.kind = NodeKind::SyntheticExit;
                let exits = self.concrete_exits.iter().copied().collect::<Vec<_>>();
                for exit in exits {
                    self.add_edge(exit, synthetic, Formula::True, vec![])?;
                }
                self.exit = Some(synthetic);
                Ok(synthetic)
            }
        }
    }

    pub fn topological_order(&self) -> Option<Vec<CfgNodeId>> {
        let mut indegree = self
            .nodes
            .keys()
            .copied()
            .map(|id| (id, 0usize))
            .collect::<BTreeMap<_, _>>();

        for edge in self.edges.values() {
            *indegree.get_mut(&edge.target).expect("target exists") += 1;
        }

        let mut queue = indegree
            .iter()
            .filter_map(|(id, degree)| (*degree == 0).then_some(*id))
            .collect::<Vec<_>>();
        let mut order = Vec::with_capacity(self.nodes.len());

        while let Some(node) = queue.pop() {
            order.push(node);
            for edge in self.edges.values().filter(|edge| edge.source == node) {
                let degree = indegree
                    .get_mut(&edge.target)
                    .expect("target node exists for topological sort");
                *degree -= 1;
                if *degree == 0 {
                    queue.push(edge.target);
                }
            }
        }

        if order.len() == self.nodes.len() {
            Some(order)
        } else {
            None
        }
    }

    pub fn topological_order_excluding(
        &self,
        excluded: &BTreeSet<CfgEdgeId>,
    ) -> Option<Vec<CfgNodeId>> {
        let mut indegree = self
            .nodes
            .keys()
            .copied()
            .map(|id| (id, 0usize))
            .collect::<BTreeMap<_, _>>();

        for edge in self.edges.values() {
            if excluded.contains(&edge.id) {
                continue;
            }
            *indegree.get_mut(&edge.target).expect("target exists") += 1;
        }

        let mut queue = indegree
            .iter()
            .filter_map(|(id, degree)| (*degree == 0).then_some(*id))
            .collect::<Vec<_>>();
        let mut order = Vec::with_capacity(self.nodes.len());

        while let Some(node) = queue.pop() {
            order.push(node);
            for edge in self
                .edges
                .values()
                .filter(|edge| edge.source == node && !excluded.contains(&edge.id))
            {
                let degree = indegree
                    .get_mut(&edge.target)
                    .expect("target node exists for topological sort");
                *degree -= 1;
                if *degree == 0 {
                    queue.push(edge.target);
                }
            }
        }

        if order.len() == self.nodes.len() {
            Some(order)
        } else {
            None
        }
    }

    pub fn detect_back_edges(&self) -> Vec<CfgEdgeId> {
        let mut visited = BTreeSet::new();
        let mut stack = BTreeSet::new();
        let mut back_edges = Vec::new();
        self.detect_back_edges_from(self.entry, &mut visited, &mut stack, &mut back_edges);
        back_edges
    }

    fn detect_back_edges_from(
        &self,
        node: CfgNodeId,
        visited: &mut BTreeSet<CfgNodeId>,
        stack: &mut BTreeSet<CfgNodeId>,
        back_edges: &mut Vec<CfgEdgeId>,
    ) {
        visited.insert(node);
        stack.insert(node);
        for edge_id in self.outgoing_edges(node) {
            let Ok(edge) = self.edge(edge_id) else {
                continue;
            };
            if stack.contains(&edge.target) {
                back_edges.push(edge.id);
            } else if !visited.contains(&edge.target) {
                self.detect_back_edges_from(edge.target, visited, stack, back_edges);
            }
        }
        stack.remove(&node);
    }

    fn edge_mut(&mut self, id: CfgEdgeId) -> Result<&mut AbstractEdge, CfgError> {
        self.edges.get_mut(&id).ok_or(CfgError::UnknownEdge { id })
    }
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum CfgError {
    #[error("unknown node id: {id:?}")]
    UnknownNode { id: CfgNodeId },
    #[error("unknown edge id: {id:?}")]
    UnknownEdge { id: CfgEdgeId },
    #[error("missing CFG exit")]
    MissingExit,
}

fn wp_one(effect: &TransferEffect, post: &Formula) -> Formula {
    match effect {
        TransferEffect::Nop
        | TransferEffect::Alloca { .. }
        | TransferEffect::GetElementPtr { .. }
        | TransferEffect::PointerStore { .. }
        | TransferEffect::PointerLoad { .. }
        | TransferEffect::Call { .. }
        | TransferEffect::Load { .. }
        | TransferEffect::Store { .. } => post.clone(),
        TransferEffect::Assign { target, value } => match value {
            AssignValue::Term(term) => substitute_var_in_formula(target, term, post),
            AssignValue::Predicate(predicate) => {
                substitute_bool_var_in_formula(target, predicate, post)
            }
        },
        TransferEffect::Assume(condition) => Formula::implies(condition.clone(), post.clone()),
        TransferEffect::Obligation(condition) => Formula::and(condition.clone(), post.clone()),
        TransferEffect::MemoryStore {
            region,
            offset,
            value,
        } => substitute_memory_var_in_formula(
            region,
            &Memory::store(Memory::var(region), offset.clone(), value.clone()),
            post,
        ),
    }
}

fn sp_one(effect: &TransferEffect, pre: &Formula) -> Formula {
    match effect {
        TransferEffect::Nop
        | TransferEffect::Alloca { .. }
        | TransferEffect::GetElementPtr { .. }
        | TransferEffect::PointerStore { .. }
        | TransferEffect::PointerLoad { .. }
        | TransferEffect::Load { .. }
        | TransferEffect::Store { .. }
        | TransferEffect::MemoryStore { .. }
        | TransferEffect::Call { .. } => pre.clone(),
        TransferEffect::Assign { target, value } => match value {
            AssignValue::Term(term) => Formula::and(
                pre.clone(),
                Formula::eq(Term::Var(target.clone()), term.clone()),
            ),
            AssignValue::Predicate(predicate) => Formula::and(
                pre.clone(),
                Formula::and(
                    Formula::implies(Formula::Var(target.clone()), predicate.clone()),
                    Formula::implies(predicate.clone(), Formula::Var(target.clone())),
                ),
            ),
        },
        TransferEffect::Assume(condition) | TransferEffect::Obligation(condition) => {
            Formula::and(pre.clone(), condition.clone())
        }
    }
}

pub fn substitute_var_in_formula(target: &Var, replacement: &Term, formula: &Formula) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => Formula::not(substitute_var_in_formula(target, replacement, inner)),
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_var_in_formula(target, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_var_in_formula(target, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_var_in_formula(target, replacement, lhs),
            substitute_var_in_formula(target, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_var_in_memory(target, replacement, lhs),
            substitute_var_in_memory(target, replacement, rhs),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
    }
}

pub fn substitute_var_in_term(target: &Var, replacement: &Term, term: &Term) -> Term {
    match term {
        Term::Var(var) if var == target => replacement.clone(),
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(inner) => {
            Term::bool_to_int(substitute_var_in_formula(target, replacement, inner))
        }
        Term::Select(memory, index) => Term::select(
            substitute_var_in_memory(target, replacement, memory),
            substitute_var_in_term(target, replacement, index),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_var_in_term(target, replacement, lhs),
            substitute_var_in_term(target, replacement, rhs),
        ),
        Term::Neg(inner) => Term::neg(substitute_var_in_term(target, replacement, inner)),
    }
}

pub fn substitute_var_in_memory(target: &Var, replacement: &Term, memory: &Memory) -> Memory {
    match memory {
        Memory::Var(name) => Memory::var(name),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_var_in_memory(target, replacement, inner),
            substitute_var_in_term(target, replacement, index),
            substitute_var_in_term(target, replacement, value),
        ),
    }
}

pub fn substitute_bool_var_in_formula(
    target: &Var,
    replacement: &Formula,
    formula: &Formula,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) if var == target => replacement.clone(),
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => {
            Formula::not(substitute_bool_var_in_formula(target, replacement, inner))
        }
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_bool_var_in_formula(target, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_bool_var_in_formula(target, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_bool_var_in_formula(target, replacement, lhs),
            substitute_bool_var_in_formula(target, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(lhs.clone(), rhs.clone()),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(lhs.clone(), rhs.clone()),
        Formula::Lt(lhs, rhs) => Formula::lt(lhs.clone(), rhs.clone()),
        Formula::Le(lhs, rhs) => Formula::le(lhs.clone(), rhs.clone()),
        Formula::Gt(lhs, rhs) => Formula::gt(lhs.clone(), rhs.clone()),
        Formula::Ge(lhs, rhs) => Formula::ge(lhs.clone(), rhs.clone()),
    }
}

pub fn substitute_memory_var_in_formula(
    region: &str,
    replacement: &Memory,
    formula: &Formula,
) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Var(var) => Formula::Var(var.clone()),
        Formula::Not(inner) => {
            Formula::not(substitute_memory_var_in_formula(region, replacement, inner))
        }
        Formula::And(items) => Formula::and_many(
            items
                .iter()
                .map(|item| substitute_memory_var_in_formula(region, replacement, item)),
        ),
        Formula::Or(items) => Formula::or_many(
            items
                .iter()
                .map(|item| substitute_memory_var_in_formula(region, replacement, item)),
        ),
        Formula::Implies(lhs, rhs) => Formula::implies(
            substitute_memory_var_in_formula(region, replacement, lhs),
            substitute_memory_var_in_formula(region, replacement, rhs),
        ),
        Formula::Eq(lhs, rhs) => Formula::eq(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::MemoryEq(lhs, rhs) => Formula::memory_eq(
            substitute_memory_var_in_memory(region, replacement, lhs),
            substitute_memory_var_in_memory(region, replacement, rhs),
        ),
        Formula::Lt(lhs, rhs) => Formula::lt(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Le(lhs, rhs) => Formula::le(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Gt(lhs, rhs) => Formula::gt(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Formula::Ge(lhs, rhs) => Formula::ge(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
    }
}

pub fn substitute_memory_var_in_term(region: &str, replacement: &Memory, term: &Term) -> Term {
    match term {
        Term::Var(var) => Term::Var(var.clone()),
        Term::Int(value) => Term::Int(*value),
        Term::Real(value) => Term::Real(*value),
        Term::BoolToInt(inner) => {
            Term::bool_to_int(substitute_memory_var_in_formula(region, replacement, inner))
        }
        Term::Select(memory, index) => Term::select(
            substitute_memory_var_in_memory(region, replacement, memory),
            substitute_memory_var_in_term(region, replacement, index),
        ),
        Term::Add(lhs, rhs) => Term::add(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Sub(lhs, rhs) => Term::sub(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Mul(lhs, rhs) => Term::mul(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Div(lhs, rhs) => Term::div(
            substitute_memory_var_in_term(region, replacement, lhs),
            substitute_memory_var_in_term(region, replacement, rhs),
        ),
        Term::Neg(inner) => Term::neg(substitute_memory_var_in_term(region, replacement, inner)),
    }
}

pub fn substitute_memory_var_in_memory(
    region: &str,
    replacement: &Memory,
    memory: &Memory,
) -> Memory {
    match memory {
        Memory::Var(name) if name == region => replacement.clone(),
        Memory::Var(name) => Memory::var(name),
        Memory::Store(inner, index, value) => Memory::store(
            substitute_memory_var_in_memory(region, replacement, inner),
            substitute_memory_var_in_term(region, replacement, index),
            substitute_memory_var_in_term(region, replacement, value),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wp_assignment_substitutes_target() {
        let transfer = TransferFn::new(vec![TransferEffect::Assign {
            target: Var::int("x"),
            value: AssignValue::Term(Term::int(1)),
        }]);
        let post = Formula::eq(
            Term::var("x", crate::common::formula::Sort::Int),
            Term::int(3),
        );
        let pre = transfer.wp(&post);
        assert_eq!(pre, Formula::eq(Term::int(1), Term::int(3)));
    }

    #[test]
    fn wp_assume_creates_implication() {
        let transfer = TransferFn::new(vec![TransferEffect::Assume(Formula::bool_var("c"))]);
        let pre = transfer.wp(&Formula::bool_var("p"));
        assert_eq!(
            pre,
            Formula::implies(Formula::bool_var("c"), Formula::bool_var("p"))
        );
    }

    #[test]
    fn wp_obligation_creates_conjunction() {
        let transfer = TransferFn::new(vec![TransferEffect::Obligation(Formula::bool_var("c"))]);
        let pre = transfer.wp(&Formula::bool_var("p"));
        assert_eq!(
            pre,
            Formula::and(Formula::bool_var("c"), Formula::bool_var("p"))
        );
    }

    #[test]
    fn wp_composes_in_reverse_order() {
        let transfer = TransferFn::new(vec![
            TransferEffect::Assign {
                target: Var::int("x"),
                value: AssignValue::Term(Term::int(1)),
            },
            TransferEffect::Assign {
                target: Var::int("y"),
                value: AssignValue::Term(Term::var("x", crate::common::formula::Sort::Int)),
            },
        ]);
        let post = Formula::eq(
            Term::var("y", crate::common::formula::Sort::Int),
            Term::int(0),
        );
        let pre = transfer.wp(&post);
        assert_eq!(pre, Formula::eq(Term::int(1), Term::int(0)));
    }

    #[test]
    fn sp_assignment_adds_equality() {
        let transfer = TransferFn::new(vec![TransferEffect::Assign {
            target: Var::int("x"),
            value: AssignValue::Term(Term::int(8)),
        }]);
        let sp = transfer.sp(&Formula::bool_var("r"));
        assert_eq!(
            sp,
            Formula::and(
                Formula::bool_var("r"),
                Formula::eq(
                    Term::var("x", crate::common::formula::Sort::Int),
                    Term::int(8)
                ),
            )
        );
    }

    #[test]
    fn topological_order_accepts_dag_and_rejects_cycle() {
        let mut dag = AbstractCfg::new("entry");
        let n1 = dag.add_node("n1", TransferFn::identity());
        let n2 = dag.add_node("n2", TransferFn::identity());
        dag.add_edge(dag.entry(), n1, Formula::True, vec![])
            .unwrap();
        dag.add_edge(n1, n2, Formula::True, vec![]).unwrap();
        assert!(dag.topological_order().is_some());

        let mut cyclic = AbstractCfg::new("entry");
        let a = cyclic.add_node("a", TransferFn::identity());
        cyclic
            .add_edge(cyclic.entry(), a, Formula::True, vec![])
            .unwrap();
        cyclic
            .add_edge(a, cyclic.entry(), Formula::True, vec![])
            .unwrap();
        assert!(cyclic.topological_order().is_none());
    }

    #[test]
    fn ensure_single_exit_creates_synthetic_exit_for_multiple() {
        let mut cfg = AbstractCfg::new("entry");
        let a = cfg.add_node("a", TransferFn::identity());
        let b = cfg.add_node("b", TransferFn::identity());
        cfg.mark_exit(a).unwrap();
        cfg.mark_exit(b).unwrap();
        let exit = cfg.ensure_single_exit().unwrap();
        assert_eq!(cfg.node(exit).unwrap().kind, NodeKind::SyntheticExit);
        assert_eq!(cfg.predecessors(exit).len(), 2);
    }

    #[test]
    fn pointer_resolution_chains_alloca_and_gep() {
        let transfer = TransferFn::new(vec![
            TransferEffect::Alloca {
                target: "%p".to_string(),
                region: "r0".to_string(),
            },
            TransferEffect::GetElementPtr {
                target: "%q".to_string(),
                base: "%p".to_string(),
                offset: Term::int(4),
            },
        ]);
        let env = transfer.pointer_resolution();
        let q = env.get("%q").unwrap();
        assert_eq!(q.region, "r0");
        assert_eq!(q.offset, Term::add(Term::int(0), Term::int(4)));
    }

    #[test]
    fn memory_store_wp_substitutes_memory_region() {
        let transfer = TransferFn::new(vec![TransferEffect::MemoryStore {
            region: "mem".to_string(),
            offset: Term::int(3),
            value: Term::int(9),
        }]);
        let post = Formula::eq(Term::select(Memory::var("mem"), Term::int(3)), Term::int(9));
        let pre = transfer.wp(&post);
        assert!(pre.to_string().contains("(store mem 3 9)"));
    }

    #[test]
    fn source_location_from_source_module() {
        let source = crate::common::source::SourceLocation::new("f.c", 10, 2);
        let lowered: SourceLocation = source.into();
        assert_eq!(lowered.to_string(), "f.c:10:2");
    }
}
