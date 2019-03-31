use dhall_core::*;
use dhall_generator::*;

#[derive(Debug, Clone)]
pub enum ConversionError {}

pub trait Type {
    fn get_type() -> DhallExpr;
    // fn as_dhall(&self) -> DhallExpr;
    // fn from_dhall(e: DhallExpr) -> Result<Self, DhallConversionError>;
}

impl Type for bool {
    fn get_type() -> DhallExpr {
        dhall_expr!(Bool)
    }
}

impl Type for Natural {
    fn get_type() -> DhallExpr {
        dhall_expr!(Natural)
    }
}

impl Type for Integer {
    fn get_type() -> DhallExpr {
        dhall_expr!(Integer)
    }
}

impl Type for String {
    fn get_type() -> DhallExpr {
        dhall_expr!(Text)
    }
}

impl<A: Type, B: Type> Type for (A, B) {
    fn get_type() -> DhallExpr {
        let ta = A::get_type();
        let tb = B::get_type();
        dhall_expr!({ _1: ta, _2: tb })
    }
}

impl<T: Type> Type for Option<T> {
    fn get_type() -> DhallExpr {
        let t = T::get_type();
        dhall_expr!(Optional t)
    }
}

impl<T: Type> Type for Vec<T> {
    fn get_type() -> DhallExpr {
        let t = T::get_type();
        dhall_expr!(List t)
    }
}

impl<'a, T: Type> Type for &'a T {
    fn get_type() -> DhallExpr {
        T::get_type()
    }
}

impl<T> Type for std::marker::PhantomData<T> {
    fn get_type() -> DhallExpr {
        dhall_expr!({})
    }
}

impl<T: Type, E: Type> Type for Result<T, E> {
    fn get_type() -> DhallExpr {
        let tt = T::get_type();
        let te = E::get_type();
        dhall_expr!(< Ok: tt | Err: te>)
    }
}
