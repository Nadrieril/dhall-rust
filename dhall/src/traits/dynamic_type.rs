use crate::expr::*;
use crate::traits::StaticType;
#[allow(unused_imports)]
use crate::typecheck::{TypeError, TypeMessage, TypecheckContext};
#[allow(unused_imports)]
use dhall_syntax::{Const, ExprF};
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
        self.get_type()
    }
}

impl DynamicType for Normalized {
    fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.0.get_type()
    }
}

impl DynamicType for Typed {
    fn get_type(&self) -> Result<Cow<'_, Type>, TypeError> {
        self.get_type()
    }
}
