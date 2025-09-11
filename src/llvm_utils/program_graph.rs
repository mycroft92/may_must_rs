use crate::errors::*;
use crate::llvm_utils::llvm_wrap::*;
use dot::{render, Edges, GraphWalk, Labeller, Nodes};
use std::borrow::Cow;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fs;

pub struct Node {
    pub predecessors: BTreeSet<Instruction>,
    pub instr: Instruction,
    pub successors: BTreeSet<Instruction>,
}

pub struct FunctionGraph {
    pub name: String,
    pub vertices: Vec<Instruction>,
    pub edges: HashMap<Instruction, Node>,
    pub start: Vec<Instruction>,
    pub end: Vec<Instruction>,
}

impl<'a> Labeller<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new(self.name.clone()).unwrap()
    }

    fn node_id(&'a self, n: &Instruction) -> dot::Id<'a> {
        dot::Id::new(n.print()).unwrap()
    }

    fn node_label(&'a self, n: &Instruction) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(n.print().into())
    }
}

impl<'a> dot::GraphWalk<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, Instruction> {
        Cow::Borrowed(&self.vertices)
    }

    fn edges(&'a self) -> dot::Edges<'a, (Instruction, Instruction)> {
        let mut edge_list = Vec::new();
        for (src, node) in &self.edges {
            for dst in &node.successors {
                edge_list.push((src.clone(), dst.clone()));
            }
        }
        Cow::Owned(edge_list)
    }

    fn source(&'a self, e: &(Instruction, Instruction)) -> Instruction {
        e.0.clone()
    }

    fn target(&'a self, e: &(Instruction, Instruction)) -> Instruction {
        e.1.clone()
    }
}

impl FunctionGraph {
    pub fn new(function: Function) -> FunctionGraph {
        let name = function.get_name();

        let bbs = function.get_all_basic_blocks();
        for bb in bbs {
            let instrs = bb.get_all_instructions();
        }

        FunctionGraph {
            name,
            edges: HashMap::new(),
            start: vec![],
            end: vec![],
            vertices: vec![],
        }
    }

    pub fn generate_dot_file(&self, dirpath: &str) -> std::io::Result<()> {
        if std::path::Path::new(dirpath).exists() {
            fs::remove_dir_all(dirpath)?;
        }
        fs::create_dir(dirpath)?;
        let basepath = std::path::PathBuf::from(dirpath);
        let mut f = fs::File::create(basepath.join(self.name.clone() + ".dot"))?;
        dot::render(self, &mut f)
    }

    pub fn add_instruction(&mut self, inst: Instruction) {
        if self.vertices.contains(&inst) {
            return;
        }
        self.vertices.push(inst);
        self.edges.insert(
            inst,
            Node {
                predecessors: BTreeSet::new(),
                successors: BTreeSet::new(),
                instr: inst,
            },
        );
    }

    pub fn add_edge(&mut self, from: Instruction, to: Instruction) -> Result<(), ProgError> {
        self.add_instruction(from);
        self.add_instruction(to);
        {
            let from_inst = self.edges.get_mut(&from).ok_or_else(|| {
                ProgError::GraphError(
                    from,
                    "Unable to get a mut ref while adding successor".to_string(),
                )
            })?;
            from_inst.successors.insert(to);
        }
        {
            let to_inst = self.edges.get_mut(&to).ok_or_else(|| {
                ProgError::GraphError(
                    to,
                    "Unable to get a mut ref while adding predecessor".to_string(),
                )
            })?;
            to_inst.predecessors.insert(from);
        }
        Ok(())
    }
}
