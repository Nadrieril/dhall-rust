use crate::error::{TypeError, TypeMessage};
use crate::semantics::{AlphaVar, Hir, HirKind, NzEnv, Value};
use crate::syntax::{ExprKind, Span};
use crate::Normalized;
use crate::{NormalizedExpr, ToExprOptions};

pub(crate) type Type = Value;

#[derive(Debug, Clone)]
pub(crate) enum TyExprKind {
    Var(AlphaVar),
    // Forbidden ExprKind variants: Var, Import, Embed
    Expr(ExprKind<TyExpr, Normalized>),
}

// An expression with inferred types at every node and resolved variables.
#[derive(Clone)]
pub(crate) struct TyExpr {
    kind: Box<TyExprKind>,
    ty: Option<Type>,
    span: Span,
}

impl TyExpr {
    pub fn new(kind: TyExprKind, ty: Option<Type>, span: Span) -> Self {
        TyExpr {
            kind: Box::new(kind),
            ty,
            span,
        }
    }

    pub fn kind(&self) -> &TyExprKind {
        &*self.kind
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }
    pub fn get_type(&self) -> Result<Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t.clone()),
            None => Err(TypeError::new(TypeMessage::Sort)),
        }
    }

    pub fn to_hir(&self) -> Hir {
        let kind = match self.kind() {
            TyExprKind::Var(v) => HirKind::Var(v.clone()),
            TyExprKind::Expr(e) => HirKind::Expr(e.map_ref(|tye| tye.to_hir())),
        };
        Hir::new(kind, self.span())
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        self.to_hir().to_expr(opts)
    }

    /// Eval the TyExpr. It will actually get evaluated only as needed on demand.
    pub fn eval<'e>(&self, env: impl Into<&'e NzEnv>) -> Value {
        Value::new_thunk(env.into(), self.to_hir())
    }
    /// Eval a closed TyExpr (i.e. without free variables). It will actually get evaluated only as
    /// needed on demand.
    pub fn eval_closed_expr(&self) -> Value {
        self.eval(&NzEnv::new())
    }
    /// Eval a closed TyExpr fully and recursively;
    pub fn rec_eval_closed_expr(&self) -> Value {
        let val = self.eval_closed_expr();
        val.normalize();
        val
    }
}

impl std::fmt::Debug for TyExpr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut x = fmt.debug_struct("TyExpr");
        x.field("kind", self.kind());
        if let Some(ty) = self.ty.as_ref() {
            x.field("type", &ty);
        } else {
            x.field("type", &None::<()>);
        }
        x.finish()
    }
}
