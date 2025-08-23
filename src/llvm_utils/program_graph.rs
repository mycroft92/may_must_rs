use crate::llvm_utils::llvm_wrap::*;

pub struct Node {
    pub predecessors: Vec<Instruction>,
    pub instr: Instruction,
    pub successors: Vec<Instruction>,
}

pub struct Graph {}

