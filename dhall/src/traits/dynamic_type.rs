use crate::expr::*;
use crate::traits::StaticType;
#[allow(unused_imports)]
use crate::typecheck::{
    type_of_const, TypeError, TypeMessage, TypecheckContext,
};
#[allow(unused_imports)]
use dhall_core::{Const, ExprF};
use std::borrow::Cow;

pub trait DynamicType {
    fn get_type<'a>(&'a self) -> Result<Cow<'a, Type<'static>>, TypeError>;
}

impl<T: StaticType> DynamicType for T {
    fn get_type<'a>(&'a self) -> Result<Cow<'a, Type<'static>>, TypeError> {
        Ok(Cow::Owned(T::get_static_type()))
    }
}

impl<'a> DynamicType for Type<'a> {
    fn get_type(&self) -> Result<Cow<'_, Type<'static>>, TypeError> {
        Ok(Cow::Owned(
            self.clone().into_normalized()?.get_type()?.into_owned(),
        ))
    }
}

impl<'a> DynamicType for Normalized<'a> {
    fn get_type(&self) -> Result<Cow<'_, Type<'static>>, TypeError> {
        match &self.1 {
            Some(t) => Ok(Cow::Borrowed(t)),
            None => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
        }
    }
}

impl<'a> DynamicType for Typed<'a> {
    fn get_type(&self) -> Result<Cow<'_, Type<'static>>, TypeError> {
        match &self.1 {
            Some(t) => Ok(Cow::Borrowed(t)),
            None => Err(TypeError::new(
                &TypecheckContext::new(),
                TypeMessage::Untyped,
            )),
        }
    }
}
