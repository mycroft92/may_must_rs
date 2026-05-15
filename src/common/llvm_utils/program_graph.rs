#![allow(dead_code)]

//! Instruction-level LLVM graph construction.
//!
//! This is the fixed LLVM-facing foundation for the paper-style lowering. The
//! graph stays at instruction granularity, but `may_assert` and obvious noise
//! calls are removed so later analysis layers work on semantic steps rather
//! than frontend scaffolding.
//!
//! `AGENTS.md` treats this file as the fixed foundation for the later paper
//! lowering. The analysis stack may be reconstructed around it, but this raw
//! graph construction remains the source of truth for visible LLVM control and
//! data-flow structure, including the loops and call sites that later become
//! summary/invariant boundaries.

use crate::common::errors::*;
use crate::common::llvm_utils::llvm_wrap::*;
use crate::common::source::SourceLocation;
use dot::Labeller;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};
use std::fs;

const NOISE_CALLS: &[&str] = &["printf", "putchar"];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node {
    pub predecessors: BTreeSet<Instruction>,
    pub instr: Instruction,
    pub successors: BTreeSet<Instruction>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssertSite {
    pub asserted_value: Instruction,
    pub predecessor: Option<Instruction>,
    pub successor: Option<Instruction>,
    pub source_location: SourceLocation,
}

#[derive(Clone, Debug)]
pub struct FunctionGraph {
    pub name: String,
    pub params: Vec<String>,
    pub pointer_param_indices: Vec<usize>,
    pub vertices: Vec<Instruction>,
    pub edges: HashMap<Instruction, Node>,
    pub start: Option<Instruction>,
    pub end: Vec<Instruction>,
    pub vars: HashMap<String, Instruction>,
    pub asserts: Vec<AssertSite>,
}

impl<'a> Labeller<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new(self.name.clone()).unwrap()
    }

    fn node_id(&'a self, node: &Instruction) -> dot::Id<'a> {
        let index = self
            .vertices
            .iter()
            .position(|candidate| candidate == node)
            .unwrap();
        dot::Id::new(format!("N{index}")).unwrap()
    }

    fn node_label(&'a self, node: &Instruction) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(node.print().into())
    }
}

impl<'a> dot::GraphWalk<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, Instruction> {
        Cow::Owned(self.vertices.clone())
    }

    fn edges(&'a self) -> dot::Edges<'a, (Instruction, Instruction)> {
        let mut edges = Vec::new();
        for (source, node) in &self.edges {
            for target in &node.successors {
                edges.push((*source, *target));
            }
        }
        Cow::Owned(edges)
    }

    fn source(&'a self, edge: &(Instruction, Instruction)) -> Instruction {
        edge.0
    }

    fn target(&'a self, edge: &(Instruction, Instruction)) -> Instruction {
        edge.1
    }
}

impl FunctionGraph {
    pub fn new(function: Function) -> Result<FunctionGraph> {
        if function.get_basic_block_count() == 0 {
            return Err(ProgError::NoDefinitionForGraph(function.get_name()));
        }

        let params = function.get_params();
        let mut graph = FunctionGraph {
            name: function.get_name(),
            params: params
                .iter()
                .into_iter()
                .map(|param| param.display_name())
                .collect(),
            pointer_param_indices: params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| {
                    matches!(
                        param.get_type().map(|ty| ty.kind()),
                        Some(TypeKind::Pointer)
                    )
                    .then_some(index)
                })
                .collect(),
            vertices: Vec::new(),
            edges: HashMap::new(),
            start: None,
            end: Vec::new(),
            vars: HashMap::new(),
            asserts: Vec::new(),
        };

        let basic_blocks = function.get_all_basic_blocks();
        let mut visible_by_block = HashMap::<BasicBlock, Vec<Instruction>>::new();

        for basic_block in &basic_blocks {
            let instructions = basic_block.get_all_instructions();
            if instructions.is_empty() {
                visible_by_block.insert(*basic_block, Vec::new());
                continue;
            }

            for (index, instruction) in instructions.iter().copied().enumerate() {
                if is_may_assert_call(instruction) {
                    let asserted_value = instruction
                        .get_call_args()
                        .into_iter()
                        .next()
                        .unwrap_or(instruction);
                    let source_location = instruction.get_debug_location().unwrap_or_default();
                    graph.asserts.push(AssertSite {
                        asserted_value,
                        predecessor: previous_visible_instruction(&instructions, index),
                        successor: next_visible_instruction(&instructions, index),
                        source_location,
                    });
                }
            }

            let visible = instructions
                .iter()
                .copied()
                .filter(|instruction| !should_skip_instruction(*instruction))
                .collect::<Vec<_>>();

            if graph.start.is_none() {
                graph.start = visible.first().copied();
            }

            for instruction in &visible {
                if let Some(name) = instruction.get_assignment_var() {
                    graph.vars.insert(name, *instruction);
                }
                if instruction.is_return_instruction() {
                    graph.end.push(*instruction);
                }
                graph.add_instruction(*instruction);
            }

            visible_by_block.insert(*basic_block, visible);
        }

        for visible in visible_by_block.values() {
            for pair in visible.windows(2) {
                graph.add_edge(pair[0], pair[1])?;
            }
        }

        for basic_block in &basic_blocks {
            let Some(visible) = visible_by_block.get(basic_block) else {
                continue;
            };
            let Some(terminator) = visible.last().copied() else {
                continue;
            };
            if !terminator.is_terminator_instruction() {
                continue;
            }
            for successor_block in terminator.get_successor_blocks() {
                let Some(successor_visible) = visible_by_block.get(&successor_block) else {
                    continue;
                };
                let Some(first) = successor_visible.first().copied() else {
                    continue;
                };
                graph.add_edge(terminator, first)?;
            }
        }

        Ok(graph)
    }

    pub fn add_instruction(&mut self, instruction: Instruction) {
        if self.vertices.contains(&instruction) {
            return;
        }
        self.vertices.push(instruction);
        self.edges.insert(
            instruction,
            Node {
                predecessors: BTreeSet::new(),
                instr: instruction,
                successors: BTreeSet::new(),
            },
        );
    }

    pub fn add_edge(&mut self, from: Instruction, to: Instruction) -> Result<()> {
        self.add_instruction(from);
        self.add_instruction(to);

        {
            let source = self.edges.get_mut(&from).ok_or_else(|| {
                ProgError::GraphError(from, "missing source while adding successor".to_string())
            })?;
            source.successors.insert(to);
        }
        {
            let target = self.edges.get_mut(&to).ok_or_else(|| {
                ProgError::GraphError(to, "missing target while adding predecessor".to_string())
            })?;
            target.predecessors.insert(from);
        }

        Ok(())
    }

    pub fn generate_dot_file(&self, dirpath: &str) -> Result<()> {
        if !std::path::Path::new(dirpath).exists() {
            fs::create_dir(dirpath)?;
        }
        let mut file =
            fs::File::create(std::path::PathBuf::from(dirpath).join(format!("{}.dot", self.name)))?;
        dot::render(self, &mut file)?;
        Ok(())
    }
}

pub fn generate_program_graph(module: &Module) -> Result<Vec<FunctionGraph>> {
    let mut graphs = Vec::new();
    for function in module.get_all_functions() {
        match FunctionGraph::new(function) {
            Ok(graph) => graphs.push(graph),
            Err(ProgError::NoDefinitionForGraph(_)) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(graphs)
}

pub fn dump_graphs(graphs: &[FunctionGraph], outdir: &str) {
    for graph in graphs {
        let _ = graph.generate_dot_file(outdir);
    }
}

fn should_skip_instruction(instruction: Instruction) -> bool {
    is_may_assert_call(instruction) || is_noise_call(instruction)
}

fn is_may_assert_call(instruction: Instruction) -> bool {
    instruction.get_called_function().as_deref() == Some("may_assert")
}

fn is_noise_call(instruction: Instruction) -> bool {
    let Some(callee) = instruction.get_called_function() else {
        return false;
    };
    NOISE_CALLS.iter().any(|noise| *noise == callee)
}

fn previous_visible_instruction(instructions: &[Instruction], index: usize) -> Option<Instruction> {
    instructions[..index]
        .iter()
        .rev()
        .copied()
        .find(|instruction| !should_skip_instruction(*instruction))
}

fn next_visible_instruction(instructions: &[Instruction], index: usize) -> Option<Instruction> {
    instructions[index + 1..]
        .iter()
        .copied()
        .find(|instruction| !should_skip_instruction(*instruction))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_graphs(ir: &str, check: impl FnOnce(&[FunctionGraph])) {
        initialize_target();
        let context = Context::new();
        let module = context.parse_ir_str(ir, "test").unwrap();
        let graphs = generate_program_graph(&module).unwrap();
        check(&graphs);
    }

    #[test]
    fn branch_terminator_successors_exist() {
        with_graphs(
            r#"
                define void @main(i1 %cond) {
                entry:
                    br i1 %cond, label %then, label %else
                then:
                    ret void
                else:
                    ret void
                }
            "#,
            |graphs| {
                let graph = &graphs[0];
                let branch = graph
                    .vertices
                    .iter()
                    .copied()
                    .find(|instruction| instruction.print().contains("br i1 %cond"))
                    .unwrap();
                let successors = &graph.edges.get(&branch).unwrap().successors;
                assert_eq!(successors.len(), 2);
            },
        );
    }

    #[test]
    fn may_assert_is_recorded_but_not_emitted_as_a_node() {
        with_graphs(
            r#"
                declare void @may_assert(i1)

                define void @main(i1 %cond) {
                entry:
                    call void @may_assert(i1 %cond)
                    ret void
                }
            "#,
            |graphs| {
                let graph = &graphs[0];
                assert_eq!(graph.asserts.len(), 1);
                assert!(graph
                    .vertices
                    .iter()
                    .all(|instruction| !instruction.print().contains("@may_assert")));
                assert_eq!(
                    graph.asserts[0].asserted_value.display_name(),
                    "%cond".to_string()
                );
            },
        );
    }

    #[test]
    fn declaration_only_modules_are_handled_cleanly() {
        with_graphs(
            r#"
                declare void @helper()

                define void @main() {
                entry:
                    ret void
                }
            "#,
            |graphs| {
                assert_eq!(graphs.len(), 1);
                assert_eq!(graphs[0].name, "main");
            },
        );
    }
}
