use crate::errors::*;
use crate::llvm_utils::llvm_wrap::*;
use dot::{render, Edges, GraphWalk, Labeller, Nodes};
use log::*;
use std::borrow::Cow;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fs;

#[derive(Clone, Debug)]
pub struct Node {
    pub predecessors: BTreeSet<Instruction>,
    pub instr: Instruction,
    pub successors: BTreeSet<Instruction>,
}

#[derive(Clone, Debug)]
pub struct FunctionGraph {
    pub name: String,
    pub vertices: Vec<Instruction>,
    pub edges: HashMap<Instruction, Node>,
    pub start: Vec<Instruction>,
    pub end: Vec<Instruction>,
}

type Result<a> = std::result::Result<a, ProgError>;

impl<'a> Labeller<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new(self.name.clone()).unwrap()
    }

    fn node_id(&'a self, n: &Instruction) -> dot::Id<'a> {
        let index = &self.vertices.iter().position(|x| x == n).unwrap();
        dot::Id::new(format!("N{}", index)).unwrap()
    }

    fn node_label(&'a self, n: &Instruction) -> dot::LabelText<'a> {
        dot::LabelText::LabelStr(n.print().into())
    }
}

impl<'a> dot::GraphWalk<'a, Instruction, (Instruction, Instruction)> for FunctionGraph {
    fn nodes(&'a self) -> dot::Nodes<'a, Instruction> {
        Cow::Owned(self.vertices.clone())
    }

    fn edges(&'a self) -> dot::Edges<'a, (Instruction, Instruction)> {
        let mut edge_list = Vec::new();
        for (src, node) in &self.edges {
            for dst in &node.successors {
                edge_list.push((*src, *dst));
            }
        }
        Cow::Owned(edge_list)
    }

    fn source(&'a self, e: &(Instruction, Instruction)) -> Instruction {
        e.0
    }

    fn target(&'a self, e: &(Instruction, Instruction)) -> Instruction {
        e.1
    }
}

impl FunctionGraph {
    pub fn new(function: Function) -> Result<FunctionGraph> {
        let name = function.get_name();
        let bb_count = function.get_basic_block_count();
        if bb_count == 0 {
            return Err(ProgError::NoDefinitionForGraph(name));
        }

        let mut res = FunctionGraph {
            name,
            edges: HashMap::new(),
            start: vec![],
            end: vec![],
            vertices: vec![],
        };

        let bbs = function.get_all_basic_blocks();

        for bb in bbs {
            let instrs = bb.get_all_instructions();
            let mut prev = bb
                .get_front()
                .ok_or_else(|| ProgError::LLVMError("Unable to get front for bb".to_string()))?;
            for inst in instrs {
                if inst == prev {
                    continue;
                }
                res.add_edge(prev, inst);
                if inst.is_terminator_instruction() {
                    let successors = inst.get_successors();
                    for scr in successors {
                        res.add_edge(inst, scr);
                        debug!("{inst} -> {scr}");
                    }
                }
                prev = inst;
            }
        }

        Ok(res)
    }

    pub fn show_vertices(&self) {
        for vert in &self.vertices {
            println!("{}", vert.print());
        }
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

    pub fn add_edge(&mut self, from: Instruction, to: Instruction) -> Result<()> {
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
    pub fn generate_dot_file(&self, dirpath: &str) -> Result<()> {
        if !std::path::Path::new(dirpath).exists() {
            fs::create_dir(dirpath)?;
        }

        let basepath = std::path::PathBuf::from(dirpath);
        let mut f = fs::File::create(basepath.join(self.name.clone() + ".dot"))?;
        dot::render(self, &mut f)?;
        Ok(())
    }
}

pub fn generate_program_graph(m: &Module) -> Result<Vec<FunctionGraph>> {
    let mut res = Vec::new();
    for func in m.get_all_functions() {
        match FunctionGraph::new(func) {
            Ok(graph) => {
                res.push(graph);
            }
            Err(ProgError::NoDefinitionForGraph(name)) => warn!("No definition found for {name}"),
            Err(err) => {
                return Err(err);
            }
        }
    }
    Ok(res)
}

pub fn dump_graphs(funcgraph: &Vec<FunctionGraph>, outdir: &str) {
    for g in funcgraph {
        g.generate_dot_file(outdir);
    }
}
