use crate::builtins::Builtin;
use crate::error::{ErrorBuilder, TypeError};
use crate::semantics::{mkerr, Hir, Nir, NirKind, NzEnv, TyEnv, VarEnv};
use crate::syntax::{Const, Expr, Span};

/// The type of a type. 0 is `Type`, 1 is `Kind`, etc...
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Universe(u8);

/// An expression representing a type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    val: Nir,
    univ: Universe,
}

/// A hir expression plus its inferred type.
/// Stands for "Typed intermediate representation"
#[derive(Debug, Clone)]
pub struct Tir<'hir> {
    hir: &'hir Hir,
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
}

impl Type {
    pub fn new(val: Nir, univ: Universe) -> Self {
        Type { val, univ }
    }
    /// Creates a new Type and infers its universe by re-typechecking its value.
    /// TODO: ideally avoid this function altogether. Would need to store types in RecordType and
    /// PiClosure.
    pub fn new_infer_universe(
        env: &TyEnv,
        val: Nir,
    ) -> Result<Self, TypeError> {
        let c = val.to_hir(env.as_varenv()).typecheck(env)?.ty().as_const();
        let u = match c {
            Some(c) => c.to_universe(),
            None => unreachable!(
                "internal type error: this is not a type: {:?}",
                val
            ),
        };
        Ok(Type::new(val, u))
    }
    pub fn from_const(c: Const) -> Self {
        Self::new(Nir::from_const(c), c.to_universe().next())
    }
    pub fn from_builtin(b: Builtin) -> Self {
        use Builtin::*;
        match b {
            Bool | Natural | Integer | Double | Text => {}
            _ => unreachable!("this builtin is not a type: {}", b),
        }

        Self::new(Nir::from_builtin(b), Universe::from_const(Const::Type))
    }

    /// Get the type of this type
    pub fn ty(&self) -> Universe {
        self.univ
    }

    pub fn to_nir(&self) -> Nir {
        self.val.clone()
    }
    pub fn as_nir(&self) -> &Nir {
        &self.val
    }
    pub fn into_nir(self) -> Nir {
        self.val
    }
    pub fn as_const(&self) -> Option<Const> {
        self.val.as_const()
    }
    pub fn kind(&self) -> &NirKind {
        self.val.kind()
    }

    pub fn to_hir(&self, venv: VarEnv) -> Hir {
        self.val.to_hir(venv)
    }
    pub fn to_expr_tyenv(&self, tyenv: &TyEnv) -> Expr {
        self.val.to_hir(tyenv.as_varenv()).to_expr_tyenv(tyenv)
    }
}

impl<'hir> Tir<'hir> {
    pub fn from_hir(hir: &'hir Hir, ty: Type) -> Self {
        Tir { hir, ty }
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
    pub fn to_expr_tyenv(&self, env: &TyEnv) -> Expr {
        self.as_hir().to_expr_tyenv(env)
    }

    /// Eval the Tir. It will actually get evaluated only as needed on demand.
    pub fn eval(&self, env: impl Into<NzEnv>) -> Nir {
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
}

impl From<Const> for Universe {
    fn from(x: Const) -> Universe {
        Universe::from_const(x)
    }
}
