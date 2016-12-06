use core::Expr;

pub type BoxExpr = Box<Expr<(), ()>>;
pub type ExprOpFn = fn(BoxExpr, BoxExpr) -> Expr<(), ()>;

pub fn bx<T>(x: T) -> Box<T> {
    Box::new(x)
}
