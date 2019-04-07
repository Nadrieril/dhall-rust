use dhall_core::*;
use dhall_generator::*;

#[derive(Debug, Clone)]
pub enum ConversionError {}

pub trait StaticType {
    fn get_type() -> DhallExpr;
    // fn as_dhall(&self) -> DhallExpr;
    // fn from_dhall(e: DhallExpr) -> Result<Self, DhallConversionError>;
}

impl StaticType for bool {
    fn get_type() -> DhallExpr {
        dhall_expr!(Bool)
    }
}

impl StaticType for Natural {
    fn get_type() -> DhallExpr {
        dhall_expr!(Natural)
    }
}

impl StaticType for Integer {
    fn get_type() -> DhallExpr {
        dhall_expr!(Integer)
    }
}

impl StaticType for String {
    fn get_type() -> DhallExpr {
        dhall_expr!(Text)
    }
}

impl<A: StaticType, B: StaticType> StaticType for (A, B) {
    fn get_type() -> DhallExpr {
        let ta = A::get_type();
        let tb = B::get_type();
        dhall_expr!({ _1: ta, _2: tb })
    }
}

impl<T: StaticType> StaticType for Option<T> {
    fn get_type() -> DhallExpr {
        let t = T::get_type();
        dhall_expr!(Optional t)
    }
}

impl<T: StaticType> StaticType for Vec<T> {
    fn get_type() -> DhallExpr {
        let t = T::get_type();
        dhall_expr!(List t)
    }
}

impl<'a, T: StaticType> StaticType for &'a T {
    fn get_type() -> DhallExpr {
        T::get_type()
    }
}

impl<T> StaticType for std::marker::PhantomData<T> {
    fn get_type() -> DhallExpr {
        dhall_expr!({})
    }
}

impl<T: StaticType, E: StaticType> StaticType for Result<T, E> {
    fn get_type() -> DhallExpr {
        let tt = T::get_type();
        let te = E::get_type();
        dhall_expr!(< Ok: tt | Err: te>)
    }
}
