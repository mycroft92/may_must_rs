pub mod andersen;
pub mod pointer_env;

pub use andersen::{run_alias_analysis, AliasResult};
pub use pointer_env::{PointerBinding, PointerEnv};
