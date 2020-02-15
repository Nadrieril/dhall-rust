use crate::error::TypeError;
use crate::semantics::{Hir, HirKind, NzEnv, TyEnv, Value, ValueKind, VarEnv};
use crate::syntax::{Builtin, Const, Span};
use crate::{NormalizedExpr, ToExprOptions};

/// An expression representing a type
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Type {
    val: Value,
}

/// A hir expression plus its inferred type.
#[derive(Debug, Clone)]
pub(crate) struct TyExpr {
    hir: Hir,
    ty: Type,
}

impl Type {
    pub fn from_const(c: Const) -> Self {
        Value::from_const(c).into()
    }
    pub fn from_builtin(b: Builtin) -> Self {
        Value::from_builtin(b).into()
    }

    pub fn to_value(&self) -> Value {
        self.val.clone()
    }
    pub fn as_value(&self) -> &Value {
        &self.val
    }
    pub fn into_value(self) -> Value {
        self.val
    }
    pub fn as_const(&self) -> Option<Const> {
        self.val.as_const()
    }
    pub fn kind(&self) -> &ValueKind {
        self.val.kind()
    }

    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        self.val.to_hir(venv)
    }
    pub fn to_expr_tyenv(&self, tyenv: &TyEnv) -> NormalizedExpr {
        self.val.to_hir(tyenv.as_varenv()).to_expr_tyenv(tyenv)
    }
}

impl TyExpr {
    pub fn new(kind: HirKind, ty: Type, span: Span) -> Self {
        TyExpr {
            hir: Hir::new(kind, span),
            ty,
        }
    }

    pub fn span(&self) -> Span {
        self.as_hir().span()
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    /// Get the kind (the type of the type) of this value
    // TODO: avoid recomputing so much
    pub fn get_kind(&self, env: &TyEnv) -> Result<Option<Const>, TypeError> {
        Ok(self
            .ty()
            .to_hir(env.as_varenv())
            .typecheck(env)?
            .ty()
            .as_const())
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
        self.as_hir().eval(env.into())
    }
    /// Evaluate to a Type.
    pub fn eval_to_type(&self, env: impl Into<NzEnv>) -> Type {
        self.eval(env).into()
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

impl From<Value> for Type {
    fn from(x: Value) -> Type {
        Type { val: x }
    }
}
