use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::{LLVM_InitializeNativeAsmPrinter, LLVM_InitializeNativeTarget};
use std::ffi::CStr;
use std::ptr;
mod llvm_wrap;
use crate::llvm_wrap::*;
pub unsafe fn count_instructions(module: LLVMModuleRef) {
    let mut function = LLVMGetFirstFunction(module);

    while !function.is_null() {
        // Get function name
        let name = LLVMGetValueName2(function as LLVMValueRef, &mut 0);
        let name = CStr::from_ptr(name).to_string_lossy();

        let mut count = 0;
        let mut block = LLVMGetFirstBasicBlock(function);

        // Iterate through all basic blocks
        while !block.is_null() {
            let mut inst = LLVMGetFirstInstruction(block);

            // Count instructions in this block
            while !inst.is_null() {
                count += 1;
                inst = LLVMGetNextInstruction(inst);
            }

            block = LLVMGetNextBasicBlock(block);
        }

        println!("Function {} has {} instructions", name, count);

        function = LLVMGetNextFunction(function);
    }
}

// Example usage:
fn main() {
    unsafe {
        // Initialize LLVM
        LLVM_InitializeNativeTarget();
        LLVM_InitializeNativeAsmPrinter();

        // Create module
        let context = LLVMContextCreate();
        let module =
            LLVMModuleCreateWithNameInContext(b"my_module\0".as_ptr() as *const _, context);

        // Run the pass
        count_instructions(module);

        // Cleanup
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    }
    print!("finished executing");
}
