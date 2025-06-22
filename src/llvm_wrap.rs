//! THe approach taken from Move compiler's git repo

use libc::{c_uint, size_t};
use llvm_sys::bit_reader::*;
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
            let mem_buffer = ptr::null_mut();
            let result = LLVMCreateMemoryBufferWithContentsOfFile(
                CString::new(name).unwrap().as_ptr(),
                mem_buffer,
                ptr::null_mut(),
            );
            if (result <= 0) {
                return None;
            }
            let mut module = ptr::null_mut();
            LLVMParseBitcode2(*mem_buffer, &mut module);
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

    pub fn get_all_basic_blocks(&self) -> Vec<BasicBlock> {
        vec![]
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
        vec![]
    }
}

#[derive(Copy, Clone)]
pub struct Instruction(LLVMValueRef);
