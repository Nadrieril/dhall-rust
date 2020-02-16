use crate::error::{ErrorBuilder, TypeError};
use crate::semantics::{mkerr, Hir, NzEnv, TyEnv, Value, ValueKind, VarEnv};
use crate::syntax::{Builtin, Const, Span};
use crate::{NormalizedExpr, ToExprOptions};

/// The type of a type. 0 is `Type`, 1 is `Kind`, etc...
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub(crate) struct Universe(u8);

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

impl Universe {
    pub fn from_const(c: Const) -> Self {
        Universe(match c {
            Const::Type => 0,
            Const::Kind => 1,
            Const::Sort => 2,
        })
    }
    pub fn as_const(self) -> Option<Const> {
        match self.0 {
            0 => Some(Const::Type),
            1 => Some(Const::Kind),
            2 => Some(Const::Sort),
            _ => None,
        }
    }
    pub fn next(self) -> Self {
        Universe(self.0 + 1)
    }
    pub fn previous(self) -> Option<Self> {
        if self.0 == 0 {
            None
        } else {
            Some(Universe(self.0 - 1))
        }
    }
}

impl Type {
    pub fn new(val: Value, _u: Universe) -> Self {
        Type { val }
    }
    pub fn from_const(c: Const) -> Self {
        Self::new(Value::from_const(c), c.to_universe().next())
    }
    pub fn from_builtin(b: Builtin) -> Self {
        use Builtin::*;
        match b {
            Bool | Natural | Integer | Double | Text => {}
            _ => unreachable!("this builtin is not a type: {}", b),
        }

        Self::new(Value::from_builtin(b), Universe::from_const(Const::Type))
    }

    /// Get the type of this type
    // TODO: avoid recomputing so much
    pub fn ty(&self, env: &TyEnv) -> Result<Option<Const>, TypeError> {
        Ok(self.to_hir(env.as_varenv()).typecheck(env)?.ty().as_const())
    }
    /// Get the type of this type
    // TODO: avoid recomputing so much
    pub fn ty_univ(&self, env: &TyEnv) -> Result<Universe, TypeError> {
        Ok(match self.ty(env)? {
            Some(c) => c.to_universe(),
            // TODO: hack, might explode
            None => Const::Sort.to_universe().next(),
        })
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
    pub fn from_hir(hir: &Hir, ty: Type) -> Self {
        TyExpr {
            hir: hir.clone(),
            ty,
        }
    }

    pub fn span(&self) -> Span {
        self.as_hir().span()
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    pub fn to_hir(&self) -> Hir {
        self.as_hir().clone()
    }
    pub fn as_hir(&self) -> &Hir {
        &self.hir
    }
    /// Converts a closed expression back to the corresponding AST expression.
    pub fn to_expr(&self, opts: ToExprOptions) -> NormalizedExpr {
        self.as_hir().to_expr(opts)
    }
    pub fn to_expr_tyenv(&self, env: &TyEnv) -> NormalizedExpr {
        self.as_hir().to_expr_tyenv(env)
    }

    /// Eval the TyExpr. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: impl Into<NzEnv>) -> Value {
        self.as_hir().eval(env.into())
    }
    pub fn ensure_is_type(&self, env: &TyEnv) -> Result<(), TypeError> {
        if self.ty().as_const().is_none() {
            return mkerr(
                ErrorBuilder::new(format!(
                    "Expected a type, found: `{}`",
                    self.to_expr_tyenv(env),
                ))
                .span_err(
                    self.span(),
                    format!(
                        "this has type: `{}`",
                        self.ty().to_expr_tyenv(env)
                    ),
                )
                .help(format!(
                    "An expression in type position must have type `Type`, \
                     `Kind` or `Sort`",
                ))
                .format(),
            );
        }
        Ok(())
    }
    /// Evaluate to a Type.
    pub fn eval_to_type(&self, env: &TyEnv) -> Result<Type, TypeError> {
        self.ensure_is_type(env)?;
        Ok(Type::new(
            self.eval(env),
            self.ty()
                .as_const()
                .expect("case handled in ensure_is_type")
                .to_universe(),
        ))
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
