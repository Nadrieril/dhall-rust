use crate::expr::*;
use crate::traits::StaticType;
#[allow(unused_imports)]
use crate::typecheck::{TypeError, TypeMessage, TypecheckContext};
#[allow(unused_imports)]
use dhall_syntax::{Const, ExprF};
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
        self.get_type()
    }
}

impl<'a> DynamicType for Normalized<'a> {
    fn get_type(&self) -> Result<Cow<'_, Type<'static>>, TypeError> {
        self.0.get_type()
    }
}

impl<'a> DynamicType for Typed<'a> {
    fn get_type(&self) -> Result<Cow<'_, Type<'static>>, TypeError> {
        self.0.get_type()
    }
}
