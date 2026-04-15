//! Safe-ish Rust boundary around the LLVM C API.
//!
//! This module is intentionally the narrowest place where most `unsafe` LLVM
//! calls live. The rest of the analyzer should work with small copyable wrapper
//! types (`Module`, `Function`, `BasicBlock`, `Instruction`) instead of raw
//! `LLVM*Ref` pointers. That keeps the design honest:
//!
//! - ownership and disposal live near the C API (`Drop` for `Context` and
//!   `Module`);
//! - callers get Rust `Option`/`Vec`/`String` results instead of null pointers;
//! - pointer identity remains available for graph keys by deriving `Hash`/`Eq`
//!   on the wrapper types;
//! - adding new LLVM queries means adding one wrapper method here rather than
//!   spreading `unsafe` through analysis code.
//!
//! These wrappers are not a complete type-safe LLVM binding. They are a local
//! boundary for the subset of LLVM IR the analyzer currently needs.

use llvm_sys::bit_reader::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::{LLVMIntPredicate, LLVMOpcode};
use std::ffi::{CStr, CString};
use std::ptr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstructionOpcode {
    // Terminator Instructions
    Ret,
    Br,
    Switch,
    IndirectBr,
    Invoke,
    Resume,
    Unreachable,
    CleanupRet,
    CatchRet,
    CatchSwitch,
    CallBr,

    // Standard Unary Operators
    FNeg,

    // Standard Binary Operators
    Add,
    FAdd,
    Sub,
    FSub,
    Mul,
    FMul,
    UDiv,
    SDiv,
    FDiv,
    URem,
    SRem,
    FRem,

    // Logical Operators
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,

    // Memory Operators
    Alloca,
    Load,
    Store,
    GetElementPtr,
    Fence,
    AtomicCmpXchg,
    AtomicRMW,

    // Cast Operators
    Trunc,
    ZExt,
    SExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    FPTrunc,
    FPExt,
    PtrToInt,
    IntToPtr,
    BitCast,
    AddrSpaceCast,

    // Other Operators
    ICmp,
    FCmp,
    PHI,
    Call,
    Select,
    UserOp1,
    UserOp2,
    VAArg,
    ExtractElement,
    InsertElement,
    ShuffleVector,
    ExtractValue,
    InsertValue,
    LandingPad,
    CleanupPad,
    CatchPad,
    Freeze,

    Unknown,
}

impl From<LLVMOpcode> for InstructionOpcode {
    fn from(opcode: LLVMOpcode) -> Self {
        match opcode {
            LLVMOpcode::LLVMRet => InstructionOpcode::Ret,
            LLVMOpcode::LLVMBr => InstructionOpcode::Br,
            LLVMOpcode::LLVMSwitch => InstructionOpcode::Switch,
            LLVMOpcode::LLVMIndirectBr => InstructionOpcode::IndirectBr,
            LLVMOpcode::LLVMInvoke => InstructionOpcode::Invoke,
            LLVMOpcode::LLVMUnreachable => InstructionOpcode::Unreachable,
            LLVMOpcode::LLVMCallBr => InstructionOpcode::CallBr,
            LLVMOpcode::LLVMFNeg => InstructionOpcode::FNeg,
            LLVMOpcode::LLVMAdd => InstructionOpcode::Add,
            LLVMOpcode::LLVMFAdd => InstructionOpcode::FAdd,
            LLVMOpcode::LLVMSub => InstructionOpcode::Sub,
            LLVMOpcode::LLVMFSub => InstructionOpcode::FSub,
            LLVMOpcode::LLVMMul => InstructionOpcode::Mul,
            LLVMOpcode::LLVMFMul => InstructionOpcode::FMul,
            LLVMOpcode::LLVMUDiv => InstructionOpcode::UDiv,
            LLVMOpcode::LLVMSDiv => InstructionOpcode::SDiv,
            LLVMOpcode::LLVMFDiv => InstructionOpcode::FDiv,
            LLVMOpcode::LLVMURem => InstructionOpcode::URem,
            LLVMOpcode::LLVMSRem => InstructionOpcode::SRem,
            LLVMOpcode::LLVMFRem => InstructionOpcode::FRem,
            LLVMOpcode::LLVMShl => InstructionOpcode::Shl,
            LLVMOpcode::LLVMLShr => InstructionOpcode::LShr,
            LLVMOpcode::LLVMAShr => InstructionOpcode::AShr,
            LLVMOpcode::LLVMAnd => InstructionOpcode::And,
            LLVMOpcode::LLVMOr => InstructionOpcode::Or,
            LLVMOpcode::LLVMXor => InstructionOpcode::Xor,
            LLVMOpcode::LLVMAlloca => InstructionOpcode::Alloca,
            LLVMOpcode::LLVMLoad => InstructionOpcode::Load,
            LLVMOpcode::LLVMStore => InstructionOpcode::Store,
            LLVMOpcode::LLVMGetElementPtr => InstructionOpcode::GetElementPtr,
            LLVMOpcode::LLVMTrunc => InstructionOpcode::Trunc,
            LLVMOpcode::LLVMZExt => InstructionOpcode::ZExt,
            LLVMOpcode::LLVMSExt => InstructionOpcode::SExt,
            LLVMOpcode::LLVMFPToUI => InstructionOpcode::FPToUI,
            LLVMOpcode::LLVMFPToSI => InstructionOpcode::FPToSI,
            LLVMOpcode::LLVMUIToFP => InstructionOpcode::UIToFP,
            LLVMOpcode::LLVMSIToFP => InstructionOpcode::SIToFP,
            LLVMOpcode::LLVMFPTrunc => InstructionOpcode::FPTrunc,
            LLVMOpcode::LLVMFPExt => InstructionOpcode::FPExt,
            LLVMOpcode::LLVMPtrToInt => InstructionOpcode::PtrToInt,
            LLVMOpcode::LLVMIntToPtr => InstructionOpcode::IntToPtr,
            LLVMOpcode::LLVMBitCast => InstructionOpcode::BitCast,
            LLVMOpcode::LLVMAddrSpaceCast => InstructionOpcode::AddrSpaceCast,
            LLVMOpcode::LLVMICmp => InstructionOpcode::ICmp,
            LLVMOpcode::LLVMFCmp => InstructionOpcode::FCmp,
            LLVMOpcode::LLVMPHI => InstructionOpcode::PHI,
            LLVMOpcode::LLVMCall => InstructionOpcode::Call,
            LLVMOpcode::LLVMSelect => InstructionOpcode::Select,
            LLVMOpcode::LLVMUserOp1 => InstructionOpcode::UserOp1,
            LLVMOpcode::LLVMUserOp2 => InstructionOpcode::UserOp2,
            LLVMOpcode::LLVMVAArg => InstructionOpcode::VAArg,
            LLVMOpcode::LLVMExtractElement => InstructionOpcode::ExtractElement,
            LLVMOpcode::LLVMInsertElement => InstructionOpcode::InsertElement,
            LLVMOpcode::LLVMShuffleVector => InstructionOpcode::ShuffleVector,
            LLVMOpcode::LLVMExtractValue => InstructionOpcode::ExtractValue,
            LLVMOpcode::LLVMInsertValue => InstructionOpcode::InsertValue,
            LLVMOpcode::LLVMFreeze => InstructionOpcode::Freeze,
            LLVMOpcode::LLVMFence => InstructionOpcode::Fence,
            LLVMOpcode::LLVMAtomicCmpXchg => InstructionOpcode::AtomicCmpXchg,
            LLVMOpcode::LLVMAtomicRMW => InstructionOpcode::AtomicRMW,
            LLVMOpcode::LLVMResume => InstructionOpcode::Resume,
            LLVMOpcode::LLVMLandingPad => InstructionOpcode::LandingPad,
            LLVMOpcode::LLVMCleanupRet => InstructionOpcode::CleanupRet,
            LLVMOpcode::LLVMCatchRet => InstructionOpcode::CatchRet,
            LLVMOpcode::LLVMCatchPad => InstructionOpcode::CatchPad,
            LLVMOpcode::LLVMCleanupPad => InstructionOpcode::CleanupPad,
            LLVMOpcode::LLVMCatchSwitch => InstructionOpcode::CatchSwitch,
            _ => InstructionOpcode::Unknown,
        }
    }
}

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
            let mut len = 0;
            let name = LLVMGetValueName2(self.0, &mut len);
            let name_str = CStr::from_ptr(name).to_string_lossy();

            //let name = CStr::from_ptr(LLVMGetValueName2(self.0, ptr::null_mut()))
            //    .to_str()
            //    .unwrap();
            String::from(name_str)
        }
    }

    pub fn get_params(&self) -> Vec<Instruction> {
        unsafe {
            let count = LLVMCountParams(self.0);
            let mut params = Vec::with_capacity(count as usize);
            for i in 0..count {
                let param = LLVMGetParam(self.0, i);
                if !param.is_null() {
                    params.push(Instruction(param));
                }
            }
            params
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
    pub fn get_assignment_var(&self) -> Option<String> {
        let instr = self.print();
        if let Some((name, rest)) = instr.trim().split_once(' ') {
            if (name.len() > 0) && (name.chars().nth(0).unwrap() == '%') {
                return Some(String::from(&name[1..]));
            }
        }
        None
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

    pub fn get_name(&self) -> Option<String> {
        unsafe {
            let mut len = 0;
            let name = LLVMGetValueName2(self.0, &mut len);
            if name.is_null() || len == 0 {
                return None;
            }
            Some(CStr::from_ptr(name).to_string_lossy().into_owned())
        }
    }

    pub fn display_name(&self) -> String {
        if let Some(name) = self.get_name() {
            if name.starts_with('%') || name.starts_with('@') {
                name
            } else {
                format!("%{name}")
            }
        } else if let Some(value) = self.as_constant_int() {
            value.to_string()
        } else {
            self.print()
        }
    }

    pub fn get_opcode(&self) -> InstructionOpcode {
        unsafe {
            let op = LLVMGetInstructionOpcode(self.0);
            InstructionOpcode::from(op)
        }
    }

    //pub fn get_operand(&self) -> String {
    //unsafe {
    //let op = LLVMGetInstructionOpcode(self.0);
    //format!("{:?}", op)
    //}
    //}
    pub fn is_branch_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsABranchInst(self.0);
            !res.is_null()
        }
    }

    pub fn get_ret_type(&self) -> Option<Type> {
        unsafe {
            let type_ref = LLVMTypeOf(self.0);
            if type_ref.is_null() {
                return None;
            }
            Some(Type(type_ref))
        }
    }

    pub fn is_return_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsAReturnInst(self.0);
            !res.is_null()
        }
    }

    pub fn is_terminator_instruction(&self) -> bool {
        unsafe {
            let resp = LLVMIsATerminatorInst(self.0);
            !resp.is_null()
        }
    }

    pub fn get_called_function(&self) -> Option<String> {
        if self.get_opcode() != InstructionOpcode::Call {
            return None;
        }
        unsafe {
            let val = LLVMGetCalledValue(self.0);
            let name = LLVMGetValueName(val);
            let name_str = CStr::from_ptr(name).to_string_lossy();
            return Some(String::from(name_str));
        }
    }

    pub fn get_call_args(&self) -> Vec<Instruction> {
        if self.get_opcode() != InstructionOpcode::Call {
            return vec![];
        }
        unsafe {
            let num_args = LLVMGetNumArgOperands(self.0);
            let mut args = Vec::with_capacity(num_args as usize);
            for i in 0..num_args {
                let arg = LLVMGetArgOperand(self.0, i);
                if !arg.is_null() {
                    args.push(Instruction(arg));
                }
            }
            args
        }
    }

    pub fn get_operand_count(&self) -> usize {
        unsafe { LLVMGetNumOperands(self.0).max(0) as usize }
    }

    pub fn get_operand(&self, index: usize) -> Option<Instruction> {
        unsafe {
            if index >= self.get_operand_count() {
                return None;
            }
            let operand = LLVMGetOperand(self.0, index as libc::c_uint);
            if operand.is_null() {
                None
            } else {
                Some(Instruction(operand))
            }
        }
    }

    pub fn get_operands(&self) -> Vec<Instruction> {
        (0..self.get_operand_count())
            .filter_map(|idx| self.get_operand(idx))
            .collect()
    }

    pub fn get_branch_condition(&self) -> Option<Instruction> {
        if !self.is_branch_instruction() {
            return None;
        }
        unsafe {
            let condition = LLVMGetCondition(self.0);
            if condition.is_null() {
                None
            } else {
                Some(Instruction(condition))
            }
        }
    }

    pub fn as_constant_int(&self) -> Option<i64> {
        unsafe {
            if LLVMIsAConstantInt(self.0).is_null() {
                None
            } else {
                Some(LLVMConstIntGetSExtValue(self.0))
            }
        }
    }

    pub fn get_icmp_predicate(&self) -> Option<&'static str> {
        if self.get_opcode() != InstructionOpcode::ICmp {
            return None;
        }
        unsafe {
            match LLVMGetICmpPredicate(self.0) {
                LLVMIntPredicate::LLVMIntEQ => Some("=="),
                LLVMIntPredicate::LLVMIntNE => Some("!="),
                LLVMIntPredicate::LLVMIntUGT | LLVMIntPredicate::LLVMIntSGT => Some(">"),
                LLVMIntPredicate::LLVMIntUGE | LLVMIntPredicate::LLVMIntSGE => Some(">="),
                LLVMIntPredicate::LLVMIntULT | LLVMIntPredicate::LLVMIntSLT => Some("<"),
                LLVMIntPredicate::LLVMIntULE | LLVMIntPredicate::LLVMIntSLE => Some("<="),
            }
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
