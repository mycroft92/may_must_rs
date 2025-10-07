use libc::{c_uint, size_t};
use llvm_sys::bit_reader::*;
use llvm_sys::bit_writer::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use std::ffi::{CStr, CString};
use std::ptr;

pub fn initialize_target() {
    unsafe {
        LLVM_InitializeNativeTarget();
        LLVM_InitializeNativeAsmPrinter();
        LLVM_InitializeNativeAsmParser();
    }
}

pub struct Context(LLVMContextRef);

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            LLVMContextDispose(self.0);
        }
    }
}

impl Context {
    pub fn new() -> Context {
        unsafe { Context(LLVMContextCreate()) }
    }

    pub fn create_module(&self, name: &str) -> Module {
        unsafe {
            Module(LLVMModuleCreateWithNameInContext(
                CString::new(name).unwrap().as_ptr(),
                self.0,
            ))
        }
    }

    pub fn parse_bc_file(&self, name: &str) -> Option<Module> {
        unsafe {
            let mut mem_buffer = ptr::null_mut();
            let mut error_msg = ptr::null_mut();
            let result = LLVMCreateMemoryBufferWithContentsOfFile(
                CString::new(name).unwrap().as_ptr(),
                &mut mem_buffer,
                &mut error_msg,
            );
            if (result != 0) {
                let error = CStr::from_ptr(error_msg).to_string_lossy();
                println!("Error reading file: {}", error);
                LLVMDisposeMessage(error_msg);
                return None;
            }
            let mut module = ptr::null_mut();
            if LLVMParseBitcodeInContext2(self.0, mem_buffer, &mut module) != 0 {
                println!("Error parsing bitcode");
                LLVMDisposeMemoryBuffer(mem_buffer);
                return None;
            }

            Some(Module(module))
        }
    }
}

pub struct Module(LLVMModuleRef);

impl Drop for Module {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeModule(self.0);
        }
    }
}

impl Module {
    pub fn get_all_functions(&self) -> Vec<Function> {
        unsafe {
            let mut first_func = LLVMGetFirstFunction(self.0);
            let mut res: Vec<Function> = Vec::new();
            if first_func.is_null() {
                return vec![];
            }
            let mut func = Function(first_func);
            res.push(func);
            let mut nextf = LLVMGetNextFunction(first_func);
            while !nextf.is_null() {
                res.push(Function(nextf));
                nextf = LLVMGetNextFunction(nextf);
            }
            res
        }
    }
}

impl AsMut<llvm_sys::LLVMModule> for Module {
    fn as_mut(&mut self) -> &mut llvm_sys::LLVMModule {
        unsafe { &mut *self.0 }
    }
}

#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct Type(LLVMTypeRef);

impl Type {}

#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct FunctionType(LLVMTypeRef);

impl FunctionType {
    pub fn new(return_type: Type, parameter_types: &[Type]) -> FunctionType {
        let mut parameter_types: Vec<_> = parameter_types.iter().map(|t| t.0).collect();
        unsafe {
            FunctionType(LLVMFunctionType(
                return_type.0,
                parameter_types.as_mut_ptr(),
                parameter_types.len() as libc::c_uint,
                false as LLVMBool,
            ))
        }
    }
}

#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct Function(LLVMValueRef);

impl Function {
    pub fn get_basic_block_count(&self) -> u32 {
        unsafe { LLVMCountBasicBlocks(self.0) }
    }

    pub fn get_next_basic_block(&self, basic_block: BasicBlock) -> Option<BasicBlock> {
        let next_bb = unsafe { BasicBlock(LLVMGetNextBasicBlock(basic_block.0)) };
        if next_bb.0.is_null() {
            return None;
        }
        Some(next_bb)
    }

    pub fn get_name(&self) -> String {
        unsafe {
            let name = LLVMGetValueName2(self.0, &mut 0);
            let name_str = CStr::from_ptr(name).to_string_lossy();

            //let name = CStr::from_ptr(LLVMGetValueName2(self.0, ptr::null_mut()))
            //    .to_str()
            //    .unwrap();
            String::from(name_str)
        }
    }

    pub fn get_all_basic_blocks(&self) -> Vec<BasicBlock> {
        unsafe {
            let mut first_bb = LLVMGetFirstBasicBlock(self.0);
            if first_bb.is_null() {
                return vec![];
            }
            let mut res: Vec<BasicBlock> = Vec::new();
            res.push(BasicBlock(first_bb));
            let mut bb = LLVMGetNextBasicBlock(first_bb);
            while !(bb.is_null()) {
                res.push(BasicBlock(bb));
                bb = LLVMGetNextBasicBlock(bb);
            }

            res
        }
    }
}

#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct BasicBlock(LLVMBasicBlockRef);

impl BasicBlock {
    pub fn get_all_instructions(&self) -> Vec<Instruction> {
        //panic!("Unimplemented get all instructions");
        unsafe {
            let mut res: Vec<Instruction> = Vec::new();
            let mut first = LLVMGetFirstInstruction(self.0);
            if first.is_null() {
                return vec![];
            }
            res.push(Instruction(first));
            let mut next = LLVMGetNextInstruction(first);
            while !next.is_null() {
                res.push(Instruction(next));
                next = LLVMGetNextInstruction(next);
            }

            res
        }
    }

    pub fn get_front(&self) -> Option<Instruction> {
        unsafe {
            let mut instr = LLVMGetFirstInstruction(self.0);
            if instr.is_null() {
                return None;
            }
            Some(Instruction(instr))
        }
    }

    pub fn get_back(&self) -> Option<Instruction> {
        unsafe {
            let mut instr = LLVMGetBasicBlockTerminator(self.0);
            if instr.is_null() {
                return None;
            }
            Some(Instruction(instr))
        }
    }
}

#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug, Ord, PartialOrd)]
pub struct Instruction(LLVMValueRef);

impl Instruction {
    pub fn get_assignment_var(&self) -> String {
        let instr = self.print();
        if let Some((name, rest)) = instr.split_once(' ') {
            return String::from(name);
        }
        "".to_string()
    }
    pub fn print(&self) -> String {
        unsafe {
            let inst_str = LLVMPrintValueToString(self.0);
            if inst_str.is_null() {
                return "is null".to_string();
            }
            let res = String::from(CStr::from_ptr(inst_str).to_string_lossy());
            LLVMDisposeMessage(inst_str);
            res
        }
    }

    pub fn get_operand(&self) -> String {
        unsafe {
            let op = LLVMGetInstructionOpcode(self.0);
            format!("{:?}", op)
        }
    }
    pub fn is_branch_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsABranchInst(self.0);
            if !res.is_null() {
                let a = LLVMConstIntGetZExtValue(res);
                if a > 0 {
                    return true;
                } else {
                    return false;
                }
            }
            false
        }
    }

    pub fn is_return_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsAReturnInst(self.0);
            if !res.is_null() {
                let a = LLVMConstIntGetZExtValue(res);
                if a > 0 {
                    return true;
                }
                return false;
            }
            false
        }
    }

    pub fn is_terminator_instruction(&self) -> bool {
        unsafe {
            let resp = LLVMIsATerminatorInst(self.0);
            if !resp.is_null() {
                let a = LLVMConstIntGetZExtValue(resp);
                if a > 0 {
                    return true;
                } else {
                    return false;
                }
            }
            false
        }
    }

    pub fn get_successors(&self) -> Vec<Instruction> {
        unsafe {
            if !self.is_terminator_instruction() {
                return [].to_vec();
            }
            let mut ret: Vec<Instruction> = Vec::new();
            for i in 0..LLVMGetNumSuccessors(self.0) {
                let bb = LLVMGetSuccessor(self.0, i);
                let first = LLVMGetFirstInstruction(bb);
                ret.push(Instruction(first));
            }
            ret
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let inst_rust_str = self.print();
        write!(f, "{}", inst_rust_str)
    }
}
