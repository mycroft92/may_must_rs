//! Safe-ish Rust boundary around the LLVM C API.
//!
//! This module is intentionally the narrowest place where most `unsafe` LLVM
//! calls live. The rest of the analyzer works with small copyable wrapper
//! types (`Module`, `Function`, `BasicBlock`, `Instruction`) instead of raw
//! `LLVM*Ref` pointers. That keeps the design honest:
//!
//! - Ownership and disposal live near the C API (`Drop` for `Context` and
//!   `Module`).
//! - Callers get Rust `Option`/`Vec`/`String` results instead of null pointers.
//! - Pointer identity is preserved for graph keys via `Hash`/`Eq` derived on
//!   the wrapper types.
//! - Adding new LLVM queries means adding one wrapper method here rather than
//!   spreading `unsafe` through analysis code.
//!
//! These wrappers are not a complete type-safe LLVM binding — only the subset
//! of LLVM IR the analyzer currently needs. No paper reasoning belongs here;
//! this file exists only to query LLVM safely enough for the raw graph builder
//! and later loop/call lowering.

use crate::common::source::SourceLocation;
use llvm_sys::bit_reader::*;
use llvm_sys::core::*;
use llvm_sys::debuginfo::*;
use llvm_sys::ir_reader::*;
use llvm_sys::prelude::*;
use llvm_sys::target::LLVMTargetDataRef;
use llvm_sys::target::*;
use llvm_sys::{LLVMIntPredicate, LLVMOpcode, LLVMRealPredicate, LLVMTypeKind};
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::ptr;

/// A Rust-friendly mirror of `LLVMOpcode`, covering the subset of LLVM IR
/// opcodes the analyzer cares about.
///
/// The conversion from `LLVMOpcode` is exhaustive for all opcodes present in
/// the version of `llvm-sys` in use; any opcode not listed maps to [`Unknown`].
/// Analysis code should match on concrete variants rather than relying on
/// LLVM's textual format, so that lowering stays independent of IR printing.
///
/// [`Unknown`]: InstructionOpcode::Unknown
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstructionOpcode {
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
    FNeg,
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
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,
    Alloca,
    Load,
    Store,
    GetElementPtr,
    Fence,
    AtomicCmpXchg,
    AtomicRMW,
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

#[allow(unreachable_patterns)]
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

/// An owned LLVM context.
///
/// A context holds the global state for one compilation unit: interned types,
/// the IR memory pool, and diagnostic handlers. The analyzer creates one
/// context per analysis run and disposes it on drop.
///
/// LLVM contexts are not thread-safe — do not share a `Context` across threads.
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

    /// Create a new, empty module owned by this context.
    ///
    /// The `name` is used only for display and debug output; it does not need
    /// to match a file path.
    pub fn create_module(&self, name: &str) -> Module {
        unsafe {
            Module(LLVMModuleCreateWithNameInContext(
                CString::new(name).unwrap().as_ptr(),
                self.0,
            ))
        }
    }

    /// Parse an LLVM bitcode file (`.bc`) into a module owned by this context.
    ///
    /// Returns `None` and prints an error to stdout if the file cannot be read
    /// or the bitcode is malformed. The caller must keep `self` alive for the
    /// lifetime of the returned `Module` — LLVM modules hold a back-pointer to
    /// their owning context.
    pub fn parse_bc_file(&self, name: &str) -> Option<Module> {
        unsafe {
            let mut mem_buffer = ptr::null_mut();
            let mut error_msg = ptr::null_mut();
            let result = LLVMCreateMemoryBufferWithContentsOfFile(
                CString::new(name).unwrap().as_ptr(),
                &mut mem_buffer,
                &mut error_msg,
            );
            if result != 0 {
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

    /// Parse a textual LLVM IR string into a module owned by this context.
    ///
    /// `ir` must be valid LLVM IR text (`.ll` format). `name` is used as the
    /// buffer label for diagnostics only. This is the main entry point for
    /// unit tests that supply inline IR.
    ///
    /// Returns `None` and prints a diagnostic to stderr if parsing fails.
    pub fn parse_ir_str(&self, ir: &str, name: &str) -> Option<Module> {
        unsafe {
            let name = CString::new(name).unwrap();
            let buffer = LLVMCreateMemoryBufferWithMemoryRangeCopy(
                ir.as_ptr() as *const _,
                ir.len(),
                name.as_ptr(),
            );
            let mut module = ptr::null_mut();
            let mut error = ptr::null_mut();
            let status = LLVMParseIRInContext(self.0, buffer, &mut module, &mut error);
            if status != 0 {
                if !error.is_null() {
                    let message = CStr::from_ptr(error).to_string_lossy();
                    eprintln!("Error parsing IR: {message}");
                    LLVMDisposeMessage(error);
                }
                return None;
            }
            Some(Module(module))
        }
    }
}

/// An owned LLVM module.
///
/// A module is the top-level container for LLVM IR: it holds the list of
/// global variables, function declarations, and function definitions.
/// `Module` disposes the underlying `LLVMModuleRef` on drop.
///
/// Note that the context used to create this module must outlive it; LLVM does
/// not enforce this in C but the `Context` / `Module` pair in this file keeps
/// the lifetimes aligned by convention (both are created together and dropped
/// at the end of one analysis run).
pub struct Module(LLVMModuleRef);

impl Drop for Module {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeModule(self.0);
        }
    }
}

impl Module {
    /// Return all function definitions and declarations in the module, in
    /// their textual order.
    ///
    /// Declaration-only functions (no basic blocks) are included; callers
    /// that only want definitions should filter on
    /// [`Function::get_basic_block_count`]` > 0`.
    pub fn get_all_functions(&self) -> Vec<Function> {
        unsafe {
            let first_func = LLVMGetFirstFunction(self.0);
            let mut res: Vec<Function> = Vec::new();
            if first_func.is_null() {
                return vec![];
            }
            let func = Function(first_func);
            res.push(func);
            let mut nextf = LLVMGetNextFunction(first_func);
            while !nextf.is_null() {
                res.push(Function(nextf));
                nextf = LLVMGetNextFunction(nextf);
            }
            res
        }
    }

    /// Build a [`TargetData`] from this module's data-layout string.
    ///
    /// The returned `TargetData` can compute struct field byte offsets
    /// (`offset_of_element`) and type store sizes (`store_size_of_type`),
    /// which are needed for correct GEP offset calculation.
    pub fn get_data_layout(&self) -> TargetData {
        unsafe {
            let layout_str = LLVMGetDataLayoutStr(self.0);
            let td = LLVMCreateTargetData(layout_str);
            TargetData(td)
        }
    }

    /// Return the module's data-layout string (e.g. `"e-m:o-i64:64-..."`)
    /// as an owned `String`.  This can be stored alongside a `FunctionGraph`
    /// so the layout can be reconstructed later without holding a `Module`
    /// reference.
    pub fn get_data_layout_str(&self) -> String {
        unsafe {
            let ptr = LLVMGetDataLayoutStr(self.0);
            CStr::from_ptr(ptr).to_string_lossy().into_owned()
        }
    }
}

/// Wraps an LLVM `TargetDataRef`, providing type-layout queries.
///
/// Built from the module's data-layout string via [`Module::get_data_layout`].
/// All size and offset values are in **bytes**. Divide by 4 to convert to
/// i32-unit offsets used by the abstract memory model.
pub struct TargetData(LLVMTargetDataRef);

impl Drop for TargetData {
    fn drop(&mut self) {
        unsafe { LLVMDisposeTargetData(self.0) }
    }
}

impl TargetData {
    /// Build a `TargetData` from a data-layout string (e.g. the value
    /// stored in [`FunctionGraph::data_layout_str`]).
    pub fn from_str(layout: &str) -> TargetData {
        unsafe {
            let cstr = CString::new(layout).unwrap_or_default();
            TargetData(LLVMCreateTargetData(cstr.as_ptr()))
        }
    }

    /// Returns the byte offset of `field_index` within `struct_type`.
    ///
    /// Accounts for alignment padding between fields, so this is correct
    /// for all C-compatible struct layouts including mixed-width fields.
    pub fn offset_of_element(&self, struct_type: Type, field_index: u32) -> u64 {
        unsafe { LLVMOffsetOfElement(self.0, struct_type.0, field_index) }
    }

    /// Returns the store size (in bytes) of `ty`.
    ///
    /// This is the number of bytes written by a store of this type,
    /// which is the correct stride for array element indexing.
    pub fn store_size_of_type(&self, ty: Type) -> u64 {
        unsafe { LLVMStoreSizeOfType(self.0, ty.0) }
    }
}

impl AsMut<llvm_sys::LLVMModule> for Module {
    fn as_mut(&mut self) -> &mut llvm_sys::LLVMModule {
        unsafe { &mut *self.0 }
    }
}

#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct Type(LLVMTypeRef);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeKind {
    Void,
    Integer(u32),
    Half,
    Float,
    Double,
    Pointer,
    Function,
    Label,
    /// A fixed-size array type `[N x T]`.
    Array,
    /// A struct type (named or literal, packed or not).
    Struct,
    Other,
}

impl Type {
    pub fn kind(&self) -> TypeKind {
        unsafe {
            match LLVMGetTypeKind(self.0) {
                LLVMTypeKind::LLVMVoidTypeKind => TypeKind::Void,
                LLVMTypeKind::LLVMIntegerTypeKind => TypeKind::Integer(LLVMGetIntTypeWidth(self.0)),
                LLVMTypeKind::LLVMHalfTypeKind => TypeKind::Half,
                LLVMTypeKind::LLVMFloatTypeKind => TypeKind::Float,
                LLVMTypeKind::LLVMDoubleTypeKind => TypeKind::Double,
                LLVMTypeKind::LLVMPointerTypeKind => TypeKind::Pointer,
                LLVMTypeKind::LLVMFunctionTypeKind => TypeKind::Function,
                LLVMTypeKind::LLVMLabelTypeKind => TypeKind::Label,
                LLVMTypeKind::LLVMArrayTypeKind => TypeKind::Array,
                LLVMTypeKind::LLVMStructTypeKind => TypeKind::Struct,
                _ => TypeKind::Other,
            }
        }
    }

    /// Returns the element type of an array or the pointee type of a pointer.
    /// Returns `None` for struct and scalar types.
    pub fn get_element_type(&self) -> Option<Type> {
        match self.kind() {
            TypeKind::Array | TypeKind::Pointer => {
                let ty = unsafe { LLVMGetElementType(self.0) };
                if ty.is_null() {
                    None
                } else {
                    Some(Type(ty))
                }
            }
            _ => None,
        }
    }

    /// Returns the type of the field at `index` for a struct type.
    /// Returns `None` for non-struct types or out-of-range indices.
    pub fn get_struct_element_type_at(&self, index: u32) -> Option<Type> {
        if self.kind() != TypeKind::Struct {
            return None;
        }
        unsafe {
            let count = LLVMCountStructElementTypes(self.0);
            if index >= count {
                return None;
            }
            let mut types = vec![std::ptr::null_mut(); count as usize];
            LLVMGetStructElementTypes(self.0, types.as_mut_ptr());
            let ty = types[index as usize];
            if ty.is_null() {
                None
            } else {
                Some(Type(ty))
            }
        }
    }

    /// Returns the number of fields in a struct type, or 0 for other types.
    pub fn count_struct_fields(&self) -> u32 {
        if self.kind() != TypeKind::Struct {
            return 0;
        }
        unsafe { LLVMCountStructElementTypes(self.0) }
    }
}

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

/// A lightweight handle to an LLVM function value.
///
/// Copyable and hashable via pointer identity; two `Function` values are equal
/// if and only if they refer to the same `LLVMValueRef`. Equality does NOT
/// compare function bodies.
///
/// This type covers both function definitions (with basic blocks) and
/// declarations (no body). Use [`Function::get_basic_block_count`] to
/// distinguish them.
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct Function(LLVMValueRef);

impl Function {
    /// Number of basic blocks in the function body.
    ///
    /// Returns `0` for declaration-only functions (no body). The graph builder
    /// rejects such functions via `ProgError::NoDefinitionForGraph`.
    pub fn get_basic_block_count(&self) -> u32 {
        unsafe { LLVMCountBasicBlocks(self.0) }
    }

    /// Return the basic block that immediately follows `basic_block` in the
    /// function's block list, or `None` if `basic_block` is the last block.
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

    /// Return the formal parameters of the function as `Instruction` handles.
    ///
    /// LLVM represents parameters as `LLVMValueRef`s — the same underlying
    /// pointer type used for instructions — so the `Instruction` wrapper is
    /// reused here. Callers can query names with [`Instruction::get_name`] or
    /// types with [`Instruction::get_type`].
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

    /// Return all basic blocks in the function, in their LLVM-internal order
    /// (which matches the textual IR order).
    ///
    /// The first block in the returned list is the function entry block.
    /// An empty vector is returned for declaration-only functions.
    pub fn get_all_basic_blocks(&self) -> Vec<BasicBlock> {
        unsafe {
            let first_bb = LLVMGetFirstBasicBlock(self.0);
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

    /// Build a map from alloca `Instruction` → source variable name.
    ///
    /// For `-O0` IR the alloca's SSA name IS the C source variable name
    /// (clang preserves it).  Returns an empty map when no names are present.
    pub fn collect_alloca_debug_names(&self) -> HashMap<Instruction, String> {
        let mut map = HashMap::new();
        unsafe {
            let mut bb = LLVMGetFirstBasicBlock(self.0);
            while !bb.is_null() {
                let mut inst = LLVMGetFirstInstruction(bb);
                while !inst.is_null() {
                    if !LLVMIsAAllocaInst(inst).is_null() {
                        let mut len = 0usize;
                        let name_ptr = LLVMGetValueName2(inst, &mut len);
                        if !name_ptr.is_null() && len > 0 {
                            let name = std::str::from_utf8(std::slice::from_raw_parts(
                                name_ptr as *const u8,
                                len,
                            ))
                            .unwrap_or("")
                            .to_owned();
                            if !name.is_empty() {
                                map.insert(Instruction(inst), name);
                            }
                        }
                    }
                    inst = LLVMGetNextInstruction(inst);
                }
                bb = LLVMGetNextBasicBlock(bb);
            }
        }
        map
    }
}

/// A lightweight handle to an LLVM basic block.
///
/// Copyable and hashable by pointer identity. A basic block is a maximal
/// straight-line sequence of instructions ending in exactly one terminator.
/// Control can only enter at the top and exit at the terminator.
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct BasicBlock(LLVMBasicBlockRef);

impl BasicBlock {
    /// Return all instructions in this block in program order, including the
    /// terminator.
    pub fn get_all_instructions(&self) -> Vec<Instruction> {
        //panic!("Unimplemented get all instructions");
        unsafe {
            let mut res: Vec<Instruction> = Vec::new();
            let first = LLVMGetFirstInstruction(self.0);
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

    /// Return the first instruction in the block, or `None` if the block is
    /// empty (which LLVM IR normally disallows but guards against defensively).
    pub fn get_front(&self) -> Option<Instruction> {
        unsafe {
            let instr = LLVMGetFirstInstruction(self.0);
            if instr.is_null() {
                return None;
            }
            Some(Instruction(instr))
        }
    }

    /// Return the terminator instruction of the block (the last instruction),
    /// or `None` if the block has no terminator.
    ///
    /// Every well-formed basic block has exactly one terminator, so `None`
    /// indicates malformed IR.
    pub fn get_back(&self) -> Option<Instruction> {
        unsafe {
            let instr = LLVMGetBasicBlockTerminator(self.0);
            if instr.is_null() {
                return None;
            }
            Some(Instruction(instr))
        }
    }

    /// Return the LLVM label name of this block (e.g. `"entry"`, `"loop.body"`),
    /// or `None` if the block is anonymous (unnamed in the IR).
    pub fn get_name(&self) -> Option<String> {
        unsafe {
            let value = LLVMBasicBlockAsValue(self.0);
            let mut len = 0;
            let name = LLVMGetValueName2(value, &mut len);
            if name.is_null() || len == 0 {
                return None;
            }
            Some(CStr::from_ptr(name).to_string_lossy().into_owned())
        }
    }

    /// Return a stable, human-readable label for this block.
    ///
    /// Uses the IR label name if present; otherwise falls back to a hex
    /// pointer address (`bb_0x…`). This ensures every block has a unique
    /// printable token regardless of how the IR was compiled.
    pub fn label_token(&self) -> String {
        self.get_name()
            .filter(|name| !name.is_empty())
            .unwrap_or_else(|| format!("bb_{:p}", self.0))
    }
}

/// A lightweight handle to an LLVM value — an instruction, a function
/// parameter, a constant, or any other `LLVMValueRef`.
///
/// Despite the name, this wrapper is used for all `LLVMValueRef`s in the
/// codebase (parameters, constants, globals) because LLVM's C API represents
/// them all with the same pointer type. The name reflects the primary use-case:
/// most values the analyzer inspects are instructions inside function bodies.
///
/// Copyable and hashable by pointer identity. Two `Instruction` values are
/// equal if and only if they wrap the same LLVM value pointer — this makes
/// `Instruction` suitable as a graph node key in `HashMap`/`BTreeMap`.
///
/// Deriving `Ord` on a raw pointer gives a deterministic but arbitrary
/// ordering; it is used only to satisfy `BTreeSet` requirements in graph data
/// structures, not to imply any semantic ordering.
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug, Ord, PartialOrd)]
pub struct Instruction(LLVMValueRef);

impl Instruction {
    /// Extract the SSA destination variable name from the printed IR text.
    ///
    /// Returns the bare name (without the leading `%`) if the instruction
    /// defines an SSA value, e.g. `%tmp` → `"tmp"`. Returns `None` for
    /// instructions that do not produce a result (stores, branches, `ret`).
    ///
    /// This is a textual heuristic: it parses the first token of the printed
    /// instruction and checks for the `%` sigil. It is used to populate the
    /// `vars` table in `FunctionGraph`.
    pub fn get_assignment_var(&self) -> Option<String> {
        let instr = self.print();
        if let Some((name, _rest)) = instr.trim().split_once(' ') {
            if (name.len() > 0) && (name.chars().nth(0).unwrap() == '%') {
                return Some(String::from(&name[1..]));
            }
        }
        None
    }
    /// Render this value as its LLVM IR text representation.
    ///
    /// This calls `LLVMPrintValueToString` and disposes the returned C string.
    /// The result is the same text you would see in a `.ll` file, e.g.
    /// `"  %add = add i32 %a, %b"`. Useful for debugging and for the DOT
    /// graph renderer.
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

    /// Return the LLVM value name if one is present.
    ///
    /// For instructions this is the SSA name without `%` (e.g. `"add"` for
    /// `%add = add i32 ...`). For function parameters it is the parameter
    /// name. Returns `None` for unnamed values (temporaries that LLVM numbers
    /// automatically) and for values that have no name slot (constants, void
    /// instructions).
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

    /// Return the best available human-readable name for this value, suitable
    /// for embedding in formula variable names and diagnostic output.
    ///
    /// Resolution order:
    /// 1. LLVM value name (prefixed with `%` / `@` if not already).
    /// 2. Constant integer literal (e.g. `"42"`).
    /// 3. LHS of the printed assignment, if the printed form contains `=`.
    /// 4. First `%`/`@`-prefixed token found anywhere in the printed text.
    /// 5. The full printed IR text as a last resort.
    ///
    /// This never returns an empty string.
    pub fn display_name(&self) -> String {
        if let Some(name) = self.get_name() {
            if name.starts_with('%') || name.starts_with('@') {
                name
            } else {
                format!("%{name}")
            }
        } else if let Some(value) = self.as_constant_int() {
            value.to_string()
        } else if let Some(name) = self.print_based_name() {
            name
        } else {
            self.print()
        }
    }

    fn print_based_name(&self) -> Option<String> {
        let printed = self.print();
        if let Some((lhs, _)) = printed.split_once('=') {
            let lhs = lhs.trim();
            if lhs.starts_with('%') || lhs.starts_with('@') {
                return Some(lhs.to_string());
            }
        }
        printed
            .split_whitespace()
            .map(|token| token.trim_matches(|ch: char| matches!(ch, ',' | '(' | ')')))
            .find(|token| token.starts_with('%') || token.starts_with('@'))
            .map(ToString::to_string)
    }

    /// Return the opcode of this instruction as the local [`InstructionOpcode`]
    /// enum, converting from the raw `LLVMOpcode` via the `From` impl.
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
    /// Return `true` if this instruction is a branch (`br`), including both
    /// conditional and unconditional variants.
    pub fn is_branch_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsABranchInst(self.0);
            !res.is_null()
        }
    }

    /// Return the LLVM type of the value produced by this instruction, or
    /// `None` if the type ref is null.
    ///
    /// For instructions that produce no result (e.g. `store`, `ret`, `br`)
    /// this returns a `Void` type rather than `None`. `None` only occurs when
    /// the LLVM API returns a null type pointer, which should not happen for
    /// well-formed IR.
    pub fn get_ret_type(&self) -> Option<Type> {
        unsafe {
            let type_ref = LLVMTypeOf(self.0);
            if type_ref.is_null() {
                return None;
            }
            Some(Type(type_ref))
        }
    }

    pub fn get_type(&self) -> Option<Type> {
        self.get_ret_type()
    }

    /// Return `true` if this instruction is a `ret`.
    pub fn is_return_instruction(&self) -> bool {
        unsafe {
            let res = LLVMIsAReturnInst(self.0);
            !res.is_null()
        }
    }

    /// Return `true` if this instruction is a block terminator (`ret`, `br`,
    /// `switch`, `invoke`, `unreachable`, etc.).
    ///
    /// The graph builder uses this to determine which instruction provides
    /// successor-block edges.
    pub fn is_terminator_instruction(&self) -> bool {
        unsafe {
            let resp = LLVMIsATerminatorInst(self.0);
            !resp.is_null()
        }
    }

    /// For a `call` instruction, return the name of the statically-known
    /// callee, or `None` if the call is indirect or the instruction is not
    /// a call.
    ///
    /// This is used throughout the analysis to identify `may_assert` sites and
    /// to look up per-function summaries. Indirect calls (function pointers)
    /// are not currently modelled.
    pub fn get_called_function(&self) -> Option<String> {
        if self.get_opcode() != InstructionOpcode::Call {
            return None;
        }
        unsafe {
            let val = LLVMGetCalledValue(self.0);
            let mut len = 0;
            let name = LLVMGetValueName2(val, &mut len);
            if name.is_null() || len == 0 {
                return None;
            }
            Some(CStr::from_ptr(name).to_string_lossy().into_owned())
        }
    }

    /// Return the actual arguments passed to a `call` instruction, in order.
    ///
    /// Returns an empty vector for non-call instructions. The returned
    /// `Instruction` handles may be constants, SSA values, or parameters —
    /// use [`Instruction::display_name`] or [`Instruction::as_constant_int`]
    /// to inspect them.
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

    /// Return the number of operands of this instruction.
    ///
    /// For a `call`, this includes the callee value as the last operand —
    /// prefer [`get_call_args`](Instruction::get_call_args) when you want only
    /// the actual arguments. For a binary instruction the count is 2; for PHI
    /// nodes it is the number of incoming (block, value) pairs.
    pub fn get_operand_count(&self) -> usize {
        unsafe { LLVMGetNumOperands(self.0).max(0) as usize }
    }

    /// Return the `index`-th operand of this instruction, or `None` if
    /// `index` is out of bounds or the operand pointer is null.
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

    /// Return the condition value of a conditional branch instruction, or
    /// `None` if this is not a branch or if the branch is unconditional.
    ///
    /// The returned value is typically an `i1` produced by a preceding `icmp`
    /// or `fcmp`. The graph builder uses this when emitting branch-edge guards
    /// in the abstract CFG.
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

    /// If this value is a constant integer, return its sign-extended `i64`
    /// value; otherwise return `None`.
    ///
    /// Sign-extension means a constant `u64` bit pattern whose high bit is 1
    /// will appear as a negative `i64`. This matches LLVM's
    /// `LLVMConstIntGetSExtValue` semantics. Callers that care about unsigned
    /// semantics should reinterpret via `as u64`.
    pub fn as_constant_int(&self) -> Option<i64> {
        unsafe {
            if LLVMIsAConstantInt(self.0).is_null() {
                None
            } else {
                Some(LLVMConstIntGetSExtValue(self.0))
            }
        }
    }

    /// If this value is a constant floating-point value, return it as an
    /// `f64`; otherwise return `None`.
    ///
    /// The LLVM API may lose precision when converting half or `float` values
    /// to `f64` (`loses_info` flag is queried but silently ignored here).
    pub fn as_constant_real(&self) -> Option<f64> {
        unsafe {
            if LLVMIsAConstantFP(self.0).is_null() {
                None
            } else {
                let mut loses_info = 0;
                Some(LLVMConstRealGetDouble(self.0, &mut loses_info))
            }
        }
    }

    /// Return `true` if this value is a reference to a global variable (as
    /// opposed to a local SSA value or function parameter).
    pub fn is_global_variable_ref(&self) -> bool {
        unsafe { !LLVMIsAGlobalVariable(self.0).is_null() }
    }

    /// Attempt to read this value as a flat array of constant integers.
    ///
    /// This handles two cases:
    /// - The value itself is a `ConstantArray` or `ConstantDataArray`.
    /// - The value is a `GlobalVariable` whose initializer is such an array,
    ///   or a `bitcast` / `getelementptr` of one (operand 0 is tried as a
    ///   fallback).
    ///
    /// Returns `None` if the array is empty, if any element is not a constant
    /// integer, or if the value is none of the recognised forms. This is used
    /// by the adapter to extract constant lookup tables embedded in globals.
    pub fn constant_int_elements(&self) -> Option<Vec<i64>> {
        self.constant_int_elements_inner()
            .or_else(|| self.get_operand(0)?.constant_int_elements_inner())
    }

    fn constant_int_elements_inner(&self) -> Option<Vec<i64>> {
        unsafe {
            let arr = if !LLVMIsAGlobalVariable(self.0).is_null() {
                let init = LLVMGetInitializer(self.0);
                if init.is_null() {
                    return None;
                }
                init
            } else if !LLVMIsAConstantArray(self.0).is_null()
                || !LLVMIsAConstantDataArray(self.0).is_null()
            {
                self.0
            } else {
                return None;
            };
            let mut out = Vec::new();
            let mut index = 0u32;
            loop {
                let elem = LLVMGetAggregateElement(arr, index);
                if elem.is_null() {
                    break;
                }
                if LLVMIsAConstantInt(elem).is_null() {
                    return None;
                }
                out.push(LLVMConstIntGetSExtValue(elem));
                index += 1;
            }
            if out.is_empty() {
                None
            } else {
                Some(out)
            }
        }
    }

    /// If this value is a ConstantExpr `getelementptr` whose base is a global
    /// variable and all indices are constant integers, return the global's display
    /// name and the sum of all indices.
    ///
    /// This handles the pattern used for vtable pointers in C++ code:
    /// ```llvm
    /// store ptr getelementptr inbounds ([3 x ptr], ptr @_ZTV3Foo, i64 0, i64 2), ptr %vptr_slot
    /// ```
    /// where the stored value is a ConstantExpr GEP rather than a named SSA value.
    /// In that case `as_const_gep_of_global()` returns `Some(("_ZTV3Foo", 2))`,
    /// allowing `resolve_memory_effects` to bind the result to
    /// `(global$_ZTV3Foo, 2)` in the `PointerEnv`.
    pub fn as_const_gep_of_global(&self) -> Option<(String, i64)> {
        unsafe {
            // Must be a ConstantExpr with GEP opcode.
            if LLVMIsAConstantExpr(self.0).is_null() {
                return None;
            }
            let opcode = LLVMGetConstOpcode(self.0);
            if opcode != llvm_sys::LLVMOpcode::LLVMGetElementPtr {
                return None;
            }
            // Operand 0 is the base pointer; it must be a global variable.
            let base = LLVMGetOperand(self.0, 0);
            if base.is_null() || LLVMIsAGlobalVariable(base).is_null() {
                return None;
            }
            let mut name_len = 0;
            let name_ptr = LLVMGetValueName2(base, &mut name_len);
            if name_ptr.is_null() || name_len == 0 {
                return None;
            }
            let global_name = CStr::from_ptr(name_ptr).to_string_lossy().into_owned();
            // Sum all index operands (operands 1..N-1 where the last operand is the
            // callee for calls, but for ConstantExpr GEPs all non-base operands are
            // indices).
            let num_ops = LLVMGetNumOperands(self.0) as usize;
            let mut total_offset: i64 = 0;
            for i in 1..num_ops {
                let idx = LLVMGetOperand(self.0, i as libc::c_uint);
                if idx.is_null() || LLVMIsAConstantInt(idx).is_null() {
                    return None; // Non-constant index — cannot evaluate statically.
                }
                total_offset += LLVMConstIntGetSExtValue(idx);
            }
            Some((global_name, total_offset))
        }
    }

    /// Attempt to read the function-pointer elements of a global constant array.
    ///
    /// Vtables in C++ LLVM IR are emitted as global constant arrays of `ptr`:
    /// ```llvm
    /// @_ZTV3Foo = constant [3 x ptr] [ptr null, ptr @_ZTI3Foo, ptr @_ZN3Foo3barEv]
    /// ```
    ///
    /// This method reads such an array and returns a `Vec` with one entry per
    /// element.  An entry is `Some(name)` if the element is a direct function
    /// reference (possibly through a `bitcast` constant expression), or `None`
    /// for null pointers, RTTI pointers, and other non-function entries.
    ///
    /// Returns `None` if `self` is not a global variable or if its initializer
    /// is not a constant array.  Also tried on `self.get_operand(0)` as a
    /// fallback to handle `bitcast`/`getelementptr` wrappers.
    pub fn constant_fn_ptr_elements(&self) -> Option<Vec<Option<String>>> {
        self.constant_fn_ptr_elements_inner()
            .or_else(|| self.get_operand(0)?.constant_fn_ptr_elements_inner())
    }

    fn constant_fn_ptr_elements_inner(&self) -> Option<Vec<Option<String>>> {
        unsafe {
            let arr = if !LLVMIsAGlobalVariable(self.0).is_null() {
                let init = LLVMGetInitializer(self.0);
                if init.is_null() {
                    return None;
                }
                // Clang often wraps the vtable array in a struct: `{ [N x ptr] } { [...] }`.
                // If the initializer is a ConstantArray, use it directly; otherwise try the
                // first struct field (index 0), which is the array in the common single-field
                // struct vtable layout.
                if !LLVMIsAConstantArray(init).is_null() {
                    init
                } else {
                    let field0 = LLVMGetAggregateElement(init, 0);
                    if field0.is_null() || LLVMIsAConstantArray(field0).is_null() {
                        return None;
                    }
                    field0
                }
            } else if !LLVMIsAConstantArray(self.0).is_null() {
                self.0
            } else {
                return None;
            };

            let mut out = Vec::new();
            let mut index = 0u32;
            loop {
                let elem = LLVMGetAggregateElement(arr, index);
                if elem.is_null() {
                    break;
                }
                // Direct function reference.
                if !LLVMIsAFunction(elem).is_null() {
                    let mut len = 0;
                    let name = LLVMGetValueName2(elem, &mut len);
                    out.push(if !name.is_null() && len > 0 {
                        Some(CStr::from_ptr(name).to_string_lossy().into_owned())
                    } else {
                        None
                    });
                } else if !LLVMIsAConstantPointerNull(elem).is_null() {
                    // Explicit null — common for the first vtable slot.
                    out.push(None);
                } else if !LLVMIsAConstantExpr(elem).is_null() {
                    // ConstantExpr (e.g. bitcast of function to ptr) — try operand 0.
                    // Only call LLVMGetOperand when elem is a ConstantExpr; calling it on
                    // plain constants (ConstantInt, GlobalVariable, etc.) is unsafe.
                    let inner = LLVMGetOperand(elem, 0);
                    if !inner.is_null() && !LLVMIsAFunction(inner).is_null() {
                        let mut len = 0;
                        let name = LLVMGetValueName2(inner, &mut len);
                        out.push(if !name.is_null() && len > 0 {
                            Some(CStr::from_ptr(name).to_string_lossy().into_owned())
                        } else {
                            None
                        });
                    } else {
                        // Bitcast of a non-function (e.g. RTTI pointer, offset-to-top).
                        out.push(None);
                    }
                } else {
                    // Other constant (integer, global variable reference, etc.) — not a
                    // function pointer.
                    out.push(None);
                }
                index += 1;
            }
            if out.is_empty() {
                None
            } else {
                Some(out)
            }
        }
    }

    /// Return the comparison operator of an `icmp` instruction as a symbolic
    /// string (`"=="`, `"!="`, `"<"`, `"<="`, `">"`, `">="`), or `None` if
    /// this is not an `icmp`.
    ///
    /// Signed and unsigned variants of `<`, `<=`, `>`, `>=` are collapsed to
    /// the same symbol because the formula layer currently uses a single
    /// integer sort. Callers that need to distinguish signedness must inspect
    /// the raw LLVM predicate themselves.
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

    /// Returns `true` if this is an `icmp` with an unsigned predicate
    /// (`ult`, `ule`, `ugt`, `uge`).  `eq` and `ne` are sign-agnostic and
    /// return `false`.
    pub fn is_unsigned_icmp(&self) -> bool {
        if self.get_opcode() != InstructionOpcode::ICmp {
            return false;
        }
        unsafe {
            matches!(
                LLVMGetICmpPredicate(self.0),
                LLVMIntPredicate::LLVMIntUGT
                    | LLVMIntPredicate::LLVMIntUGE
                    | LLVMIntPredicate::LLVMIntULT
                    | LLVMIntPredicate::LLVMIntULE
            )
        }
    }

    /// Return the comparison operator of an `fcmp` instruction as a symbolic
    /// string, or `None` if this is not an `fcmp` or if the predicate cannot
    /// be mapped (e.g. `uno`, `ord`, `true`, `false` predicates).
    ///
    /// Ordered and unordered variants of the same relation are collapsed to
    /// the same symbol, matching the behaviour of [`get_icmp_predicate`](Instruction::get_icmp_predicate).
    pub fn get_fcmp_predicate(&self) -> Option<&'static str> {
        if self.get_opcode() != InstructionOpcode::FCmp {
            return None;
        }
        unsafe {
            match LLVMGetFCmpPredicate(self.0) {
                LLVMRealPredicate::LLVMRealOEQ | LLVMRealPredicate::LLVMRealUEQ => Some("=="),
                LLVMRealPredicate::LLVMRealONE | LLVMRealPredicate::LLVMRealUNE => Some("!="),
                LLVMRealPredicate::LLVMRealOGT | LLVMRealPredicate::LLVMRealUGT => Some(">"),
                LLVMRealPredicate::LLVMRealOGE | LLVMRealPredicate::LLVMRealUGE => Some(">="),
                LLVMRealPredicate::LLVMRealOLT | LLVMRealPredicate::LLVMRealULT => Some("<"),
                LLVMRealPredicate::LLVMRealOLE | LLVMRealPredicate::LLVMRealULE => Some("<="),
                _ => None,
            }
        }
    }

    /// Return the basic block that contains this instruction, or `None` if the
    /// value is not an instruction (e.g. a constant or parameter).
    pub fn get_parent_basic_block(&self) -> Option<BasicBlock> {
        unsafe {
            let parent = LLVMGetInstructionParent(self.0);
            if parent.is_null() {
                None
            } else {
                Some(BasicBlock(parent))
            }
        }
    }

    /// Return the basic blocks that this terminator instruction may transfer
    /// control to, or an empty vector if this is not a terminator.
    ///
    /// For an unconditional `br` the result has one element; for a conditional
    /// `br` it has two (true-target first, then false-target); for `switch` it
    /// may have arbitrarily many. The `FunctionGraph` builder uses this to
    /// connect visible-instruction ranges across block boundaries.
    pub fn get_successor_blocks(&self) -> Vec<BasicBlock> {
        unsafe {
            if !self.is_terminator_instruction() {
                return vec![];
            }
            let mut ret = Vec::new();
            for i in 0..LLVMGetNumSuccessors(self.0) {
                let bb = LLVMGetSuccessor(self.0, i);
                if !bb.is_null() {
                    ret.push(BasicBlock(bb));
                }
            }
            ret
        }
    }

    /// Return the first instruction of each successor basic block.
    ///
    /// Unlike [`get_successor_blocks`](Instruction::get_successor_blocks) this
    /// dereferences into instructions rather than returning block handles. Used
    /// by the raw graph walk in certain older code paths; prefer
    /// `get_successor_blocks` in new code.
    ///
    /// # Safety caveat
    /// This does not check whether the first instruction in a successor block
    /// is null; malformed IR with an empty block would cause undefined
    /// behaviour here.
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

    /// Return the (predecessor block, incoming value) pairs for a PHI node, in
    /// the order LLVM stores them.
    ///
    /// Returns an empty vector for non-PHI instructions. The adapter uses
    /// these pairs to emit per-predecessor SSA merge points when lowering the
    /// CFG to the formula layer.
    pub fn get_phi_incomings(&self) -> Vec<(BasicBlock, Instruction)> {
        if self.get_opcode() != InstructionOpcode::PHI {
            return vec![];
        }
        unsafe {
            let count = LLVMCountIncoming(self.0);
            let mut res = Vec::with_capacity(count as usize);
            for index in 0..count {
                let block = LLVMGetIncomingBlock(self.0, index);
                let value = LLVMGetIncomingValue(self.0, index);
                if !block.is_null() && !value.is_null() {
                    res.push((BasicBlock(block), Instruction(value)));
                }
            }
            res
        }
    }

    /// Returns the source element type of a `getelementptr` instruction.
    ///
    /// For `getelementptr T, ptr %p, ...`, this returns `T` — the type that
    /// the pointer is declared to point to, which drives the offset calculation
    /// for each subsequent GEP index.  Returns `None` for non-GEP instructions.
    pub fn get_gep_source_element_type(&self) -> Option<Type> {
        unsafe {
            let ty = LLVMGetGEPSourceElementType(self.0);
            if ty.is_null() {
                None
            } else {
                Some(Type(ty))
            }
        }
    }

    /// Extract LLVM debug location (file, line, column) for this instruction.
    /// Returns `None` if the bitcode was compiled without `-g` or if the
    /// instruction has no debug metadata attached.
    pub fn get_debug_location(&self) -> Option<SourceLocation> {
        unsafe {
            let loc = LLVMInstructionGetDebugLoc(self.0);
            if loc.is_null() {
                return None;
            }
            let line = LLVMDILocationGetLine(loc);
            let column = LLVMDILocationGetColumn(loc);
            let scope = LLVMDILocationGetScope(loc);
            if scope.is_null() {
                return Some(SourceLocation::new("", line, column));
            }
            let file = LLVMDIScopeGetFile(scope);
            if file.is_null() {
                return Some(SourceLocation::new("", line, column));
            }
            let mut filename_len = 0u32;
            let filename_ptr = LLVMDIFileGetFilename(file, &mut filename_len);
            let filename = if filename_ptr.is_null() || filename_len == 0 {
                String::new()
            } else {
                let bytes =
                    std::slice::from_raw_parts(filename_ptr as *const u8, filename_len as usize);
                String::from_utf8_lossy(bytes).into_owned()
            };
            Some(SourceLocation::new(filename, line, column))
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let inst_rust_str = self.print();
        write!(f, "{}", inst_rust_str)
    }
}
