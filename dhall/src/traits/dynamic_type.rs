use crate::expr::*;
use crate::traits::StaticType;
use crate::typecheck::{TypeError, TypeMessage};
use dhall_core::context::Context;
use dhall_core::{Const, ExprF};
use std::borrow::Cow;

pub trait DynamicType {
    fn get_type<'a>(&'a self) -> Result<Cow<'a, Type>, TypeError>;
}

impl<T: StaticType> DynamicType for T {
    fn get_type<'a>(&'a self) -> Result<Cow<'a, Type>, TypeError> {
        Ok(Cow::Owned(T::get_static_type()))
    }
}

impl DynamicType for Type {
    fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        use TypeInternal::*;
        match &self.0 {
            Expr(e) => e.get_type(),
            SuperType => Err(TypeError::new(
                &Context::new(),
                dhall_core::rc(ExprF::Const(Const::Sort)),
                TypeMessage::Untyped,
            )),
        }
    }
}

impl DynamicType for Normalized {
    fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        match &self.1 {
            Some(t) => Ok(Cow::Borrowed(t)),
            None => Err(TypeError::new(
                &Context::new(),
                self.0.absurd(),
                TypeMessage::Untyped,
            )),
        }
    }
}

impl DynamicType for Typed {
    fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        match &self.1 {
            Some(t) => Ok(Cow::Borrowed(t)),
            None => Err(TypeError::new(
                &Context::new(),
                self.0.clone(),
                TypeMessage::Untyped,
            )),
        }
    }
}
