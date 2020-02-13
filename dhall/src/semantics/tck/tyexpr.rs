use crate::error::{TypeError, TypeMessage};
use crate::semantics::{Hir, HirKind, NzEnv, TyEnv, Value};
use crate::syntax::{Const, Span};
use crate::{NormalizedExpr, ToExprOptions};

pub(crate) type Type = Value;

// A hir expression plus its inferred type.
#[derive(Clone)]
pub(crate) struct TyExpr {
    hir: Hir,
    ty: Option<Type>,
}

impl TyExpr {
    pub fn new(kind: HirKind, ty: Option<Type>, span: Span) -> Self {
        TyExpr {
            hir: Hir::new(kind, span),
            ty,
        }
    }

    pub fn kind(&self) -> &HirKind {
        self.hir.kind()
    }
    pub fn span(&self) -> Span {
        self.as_hir().span()
    }
    pub fn get_type(&self) -> Result<Type, TypeError> {
        match &self.ty {
            Some(t) => Ok(t.clone()),
            None => Err(TypeError::new(TypeMessage::Sort)),
        }
    }
    pub fn get_type_tyexpr(&self, env: &TyEnv) -> Result<TyExpr, TypeError> {
        Ok(self.get_type()?.to_hir(env.as_varenv()).typecheck(env)?)
    }
    /// Get the kind (the type of the type) of this value
    // TODO: avoid recomputing so much
    pub fn get_kind(&self, env: &TyEnv) -> Result<Option<Const>, TypeError> {
        Ok(self.get_type_tyexpr(env)?.get_type()?.as_const())
    }

    pub fn to_hir(&self) -> Hir {
        self.as_hir().clone()
    }
    pub fn as_hir(&self) -> &Hir {
        &self.hir
    }
    /// Converts a value back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        self.as_hir().to_expr(opts)
    }

    /// Eval the TyExpr. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: impl Into<NzEnv>) -> Value {
        self.as_hir().eval(&env.into())
    }
    /// Eval a closed TyExpr (i.e. without free variables). It will actually get evaluated only as
    /// needed on demand.
    pub fn eval_closed_expr(&self) -> Value {
        self.eval(NzEnv::new())
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
