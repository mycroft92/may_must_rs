use crate::llvm_utils::llvm_wrap::Instruction;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProgError {
    #[error("Error processing bc file")]
    LLVMError(String),
    #[error("Error making program graph: {inst}, {1}", inst=(.0).print())]
    GraphError(Instruction, String),
    #[error("Unknown Error: {0}")]
    UnknownError(String),
}
