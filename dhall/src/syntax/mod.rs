#![allow(
    clippy::many_single_char_names,
    clippy::should_implement_trait,
    clippy::new_without_default,
    clippy::type_complexity
)]

mod core;
pub use crate::syntax::core::context;
pub use crate::syntax::core::visitor;
pub use crate::syntax::core::*;
mod printer;
pub use crate::syntax::printer::*;
mod parser;
pub use crate::syntax::parser::*;
pub mod binary;
