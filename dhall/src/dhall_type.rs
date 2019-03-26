use dhall_core::*;
use dhall_generator::*;

#[derive(Debug, Clone)]
pub enum DhallConversionError {}

pub trait DhallType: Sized {
    fn dhall_type() -> DhallExpr;
    // fn as_dhall(&self) -> DhallExpr;
    // fn from_dhall(e: DhallExpr) -> Result<Self, DhallConversionError>;
}

impl DhallType for bool {
    fn dhall_type() -> DhallExpr {
        dhall_expr!(Bool)
    }
}

impl DhallType for Natural {
    fn dhall_type() -> DhallExpr {
        dhall_expr!(Natural)
    }
}

impl DhallType for Integer {
    fn dhall_type() -> DhallExpr {
        dhall_expr!(Integer)
    }
}

impl DhallType for String {
    fn dhall_type() -> DhallExpr {
        dhall_expr!(Text)
    }
}

impl<A: DhallType, B: DhallType> DhallType for (A, B) {
    fn dhall_type() -> DhallExpr {
        let ta = A::dhall_type();
        let tb = B::dhall_type();
        dhall_expr!({ _1: ta, _2: tb })
    }
}

impl<T: DhallType> DhallType for Option<T> {
    fn dhall_type() -> DhallExpr {
        let t = T::dhall_type();
        dhall_expr!(Optional t)
    }
}

impl<T: DhallType> DhallType for Vec<T> {
    fn dhall_type() -> DhallExpr {
        let t = T::dhall_type();
        dhall_expr!(List t)
    }
}

impl<'a, T: DhallType> DhallType for &'a T {
    fn dhall_type() -> DhallExpr {
        T::dhall_type()
    }
}

impl<T> DhallType for std::marker::PhantomData<T> {
    fn dhall_type() -> DhallExpr {
        dhall_expr!({})
    }
}

impl<T: DhallType, E: DhallType> DhallType for Result<T, E> {
    fn dhall_type() -> DhallExpr {
        let tt = T::dhall_type();
        let te = E::dhall_type();
        dhall_expr!(< Ok: tt | Err: te>)
    }
}
