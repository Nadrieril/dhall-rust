use std::collections::BTreeSet;

use crate::syntax::{trivial_result, Label};

// Definition order must match precedence order for
// pretty-printing to work correctly
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    /// x === y
    Equivalence,
    /// `x ? y`
    ImportAlt,
    /// `x || y`
    BoolOr,
    /// `x + y`
    NaturalPlus,
    /// `x ++ y`
    TextAppend,
    /// `x # y`
    ListAppend,
    /// `x && y`
    BoolAnd,
    /// `x ∧ y`
    RecursiveRecordMerge,
    /// `x ⫽ y`
    RightBiasedRecordMerge,
    /// `x ⩓ y`
    RecursiveRecordTypeMerge,
    /// `x * y`
    NaturalTimes,
    /// `x == y`
    BoolEQ,
    /// `x != y`
    BoolNE,
}

/// Operations
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpKind<SubExpr> {
    ///  `f a`
    App(SubExpr, SubExpr),
    /// Binary operations
    BinOp(BinOp, SubExpr, SubExpr),
    ///  `if x then y else z`
    BoolIf(SubExpr, SubExpr, SubExpr),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  `toMap x : t`
    ToMap(SubExpr, Option<SubExpr>),
    ///  `e.x`
    Field(SubExpr, Label),
    ///  `e.{ x, y, z }`
    Projection(SubExpr, BTreeSet<Label>),
    ///  `e.(t)`
    ProjectionByExpr(SubExpr, SubExpr),
    ///  `x::y`
    Completion(SubExpr, SubExpr),
    ///  `x with a.b.c = y`
    With(SubExpr, Vec<Label>, SubExpr),
}

impl<SE> OpKind<SE> {
    pub fn traverse_ref<'a, SE2, Err>(
        &'a self,
        mut f: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<OpKind<SE2>, Err> {
        // Can't use closures because of borrowing rules
        macro_rules! expr {
            ($e:expr) => {
                f($e)?
            };
        }
        macro_rules! opt {
            ($e:expr) => {
                $e.as_ref().map(|e| Ok(expr!(e))).transpose()?
            };
        }

        use OpKind::*;
        Ok(match self {
            App(f, a) => App(expr!(f), expr!(a)),
            BinOp(o, x, y) => BinOp(*o, expr!(x), expr!(y)),
            BoolIf(b, t, f) => BoolIf(expr!(b), expr!(t), expr!(f)),
            Merge(x, y, t) => Merge(expr!(x), expr!(y), opt!(t)),
            ToMap(x, t) => ToMap(expr!(x), opt!(t)),
            Field(e, l) => Field(expr!(e), l.clone()),
            Projection(e, ls) => Projection(expr!(e), ls.clone()),
            ProjectionByExpr(e, x) => ProjectionByExpr(expr!(e), expr!(x)),
            Completion(e, x) => Completion(expr!(e), expr!(x)),
            With(x, ls, y) => With(expr!(x), ls.clone(), expr!(y)),
        })
    }

    pub fn map_ref<'a, SE2>(
        &'a self,
        mut f: impl FnMut(&'a SE) -> SE2,
    ) -> OpKind<SE2> {
        trivial_result(self.traverse_ref(|x| Ok(f(x))))
    }
}
