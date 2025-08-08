//! THe approach taken from Move compiler's git repo

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

#[derive(Copy, Clone)]
pub struct Type(LLVMTypeRef);

impl Type {}

#[derive(Copy, Clone)]
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

#[derive(Copy, Clone)]
pub struct Function(LLVMValueRef);

impl Function {
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

#[derive(Copy, Clone)]
pub struct BasicBlock(LLVMBasicBlockRef);

impl BasicBlock {
    pub fn get_first_instruction(&self) -> Option<Instruction> {
        None
    }

    pub fn get_next_instruction(&self, inst: Instruction) -> Option<Instruction> {
        None
    }

    pub fn get_all_instructions(&self) -> Vec<Instruction> {
        panic!("Unimplemented get all instructions")
    }
}

#[derive(Copy, Clone)]
pub struct Instruction(LLVMValueRef);

impl Instruction {
    fn print(&self) -> String {
        unsafe {
            let inst_str = LLVMPrintValueToString(self.0);
            String::from(CStr::from_ptr(inst_str).to_str().unwrap())
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let inst_rust_str = self.print();
        write!(f, "{}", inst_rust_str)
    }
}
