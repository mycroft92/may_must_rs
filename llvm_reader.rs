use llvm_sys::bit_reader::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use std::ffi::CStr;
use std::ptr;

unsafe fn print_function(func: LLVMValueRef) {
    // Get function name
    let name = CStr::from_ptr(LLVMGetValueName2(func, ptr::null_mut()))
        .to_str()
        .unwrap();
    println!("\nFunction: {}", name);

    // Iterate through basic blocks
    let mut bb = LLVMGetFirstBasicBlock(func);
    while !bb.is_null() {
        // Get first instruction of block
        let mut inst = LLVMGetFirstInstruction(bb);

        while !inst.is_null() {
            // Convert instruction to string representation
            let inst_str = LLVMPrintValueToString(inst);
            let inst_rust_str = CStr::from_ptr(inst_str).to_str().unwrap();
            println!("  {}", inst_rust_str);

            LLVMDisposeMessage(inst_str);
            inst = LLVMGetNextInstruction(inst);
        }

        bb = LLVMGetNextBasicBlock(bb);
    }
}

fn main() {
    unsafe {
        // Initialize LLVM
        let context = LLVMContextCreate();
        let mut memory_buffer = LLVMCreateMemoryBufferWithContentsOfFile(
            std::ffi::CString::new(std::env::args().nth(1).expect("No input file provided"))
                .unwrap()
                .as_ptr(),
            ptr::null_mut(),
            ptr::null_mut(),
        );

        let mut module = ptr::null_mut();
        LLVMParseBitcode2(memory_buffer, &mut module);

        // Get first function
        let mut func = LLVMGetFirstFunction(module);

        // Iterate through all functions
        while !func.is_null() {
            print_function(func);
            func = LLVMGetNextFunction(func);
        }

        // Cleanup
        LLVMDisposeModule(module);
        LLVMContextDispose(context);
    }
}
