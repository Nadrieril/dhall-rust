#![feature(trace_macros)]
#![feature(proc_macro_hygiene)]
#![feature(slice_patterns)]
#![feature(label_break_value)]
#![cfg_attr(test, feature(custom_inner_attributes))]
#![allow(
    clippy::type_complexity,
    clippy::infallible_destructuring_match,
    clippy::many_single_char_names
)]

#[cfg(test)]
#[macro_use]
mod tests;

#[cfg(test)]
mod parser;

mod binary;
mod imports;
mod normalize;
mod traits;
mod typecheck;
pub use crate::traits::Deserialize;
pub use crate::traits::SimpleStaticType;
pub use crate::traits::StaticType;
pub use dhall_generator::SimpleStaticType;
pub mod expr;

pub fn from_str<'a, T: Deserialize<'a>>(
    s: &'a str,
    ty: Option<&crate::expr::Type>,
) -> crate::traits::Result<T> {
    T::from_str(s, ty)
}

pub fn from_str_auto_type<'a, T: Deserialize<'a> + StaticType>(
    s: &'a str,
) -> crate::traits::Result<T> {
    from_str(s, Some(&<T as StaticType>::get_static_type()))
}
