#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(unused_imports)]
use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;

use crate::error::{TypeError, TypeMessage};
use crate::semantics::core::context::TyCtx;
use crate::semantics::nze::{NameEnv, QuoteEnv};
use crate::semantics::phase::normalize::{merge_maps, NzEnv};
use crate::semantics::phase::typecheck::{
    builtin_to_value, const_to_value, type_of_builtin,
};
use crate::semantics::phase::Normalized;
use crate::semantics::{
    AlphaVar, Binder, Closure, TyExpr, TyExprKind, Type, Value, ValueKind,
};
use crate::syntax;
use crate::syntax::{
    Builtin, Const, Expr, ExprKind, InterpolatedTextContents, Label, Span,
    UnspannedExpr, V,
};

#[derive(Debug, Clone)]
pub(crate) struct TyEnv {
    names: NameEnv,
    items: NzEnv,
}

impl TyEnv {
    pub fn new() -> Self {
        TyEnv {
            names: NameEnv::new(),
            items: NzEnv::new(),
        }
    }
    pub fn as_quoteenv(&self) -> QuoteEnv {
        self.names.as_quoteenv()
    }
    pub fn as_nzenv(&self) -> &NzEnv {
        &self.items
    }
    pub fn as_nameenv(&self) -> &NameEnv {
        &self.names
    }

    pub fn insert_type(&self, x: &Label, t: Value) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_type(t),
        }
    }
    pub fn insert_value(&self, x: &Label, e: Value) -> Self {
        TyEnv {
            names: self.names.insert(x),
            items: self.items.insert_value(e),
        }
    }
    pub fn lookup(&self, var: &V<Label>) -> Option<(TyExprKind, Value)> {
        let var = self.names.unlabel_var(var)?;
        let ty = self.items.lookup_val(&var).get_type().unwrap();
        Some((TyExprKind::Var(var), ty))
    }
    pub fn size(&self) -> usize {
        self.names.size()
    }
}

fn mkerr<T>(x: impl ToString) -> Result<T, TypeError> {
    Err(TypeError::new(TypeMessage::Custom(x.to_string())))
}

fn type_last_layer(
    env: &TyEnv,
    kind: &ExprKind<TyExpr, Normalized>,
) -> Result<Value, TypeError> {
    Ok(match &kind {
        ExprKind::Import(..) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        ExprKind::Var(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Const(Const::Sort)
        | ExprKind::Embed(..) => unreachable!(),

        ExprKind::Const(Const::Type) => const_to_value(Const::Kind),
        ExprKind::Const(Const::Kind) => const_to_value(Const::Sort),
        ExprKind::Builtin(b) => {
            type_with(env, &type_of_builtin(*b))?.normalize_whnf(env.as_nzenv())
        }
        ExprKind::BoolLit(_) => builtin_to_value(Builtin::Bool),
        ExprKind::NaturalLit(_) => builtin_to_value(Builtin::Natural),
        ExprKind::IntegerLit(_) => builtin_to_value(Builtin::Integer),
        ExprKind::DoubleLit(_) => builtin_to_value(Builtin::Double),

        ExprKind::Annot(x, t) => {
            if x.get_type()? != t.normalize_whnf(env.as_nzenv()) {
                return mkerr("annot mismatch");
            }
            x.normalize_whnf(env.as_nzenv())
        }
        ExprKind::App(f, arg) => {
            let tf = f.get_type()?;
            let tf_borrow = tf.as_whnf();
            let (expected_arg_ty, ty_closure) = match &*tf_borrow {
                ValueKind::PiClosure { annot, closure, .. } => (annot, closure),
                _ => return mkerr(format!("apply to not Pi: {:?}", tf_borrow)),
            };
            // if arg.get_type()? != *expected_arg_ty {
            //     return mkerr(format!(
            //         "function annot mismatch: {:?}, {:?}",
            //         arg.get_type()?,
            //         expected_arg_ty
            //     ));
            // }

            let arg_nf = arg.normalize_whnf(env.as_nzenv());
            ty_closure.apply(arg_nf)
        }
        ExprKind::BoolIf(x, y, z) => {
            if *x.get_type()?.as_whnf()
                != ValueKind::from_builtin(Builtin::Bool)
            {
                return mkerr("InvalidPredicate");
            }
            if y.get_type()?.get_type()?.as_const() != Some(Const::Type) {
                return mkerr("IfBranchMustBeTerm");
            }
            if z.get_type()?.get_type()?.as_const() != Some(Const::Type) {
                return mkerr("IfBranchMustBeTerm");
            }
            if y.get_type()? != z.get_type()? {
                return mkerr("IfBranchMismatch");
            }

            y.get_type()?
        }

        _ => Value::from_const(Const::Type), // TODO
    })
}

/// Type-check an expression and return the expression alongside its type if type-checking
/// succeeded, or an error if type-checking failed.
fn type_with(
    env: &TyEnv,
    expr: &Expr<Normalized>,
) -> Result<TyExpr, TypeError> {
    let (tyekind, ty) = match expr.as_ref() {
        ExprKind::Var(var) => match env.lookup(&var) {
            Some((k, ty)) => (k, Some(ty)),
            None => return mkerr("unbound variable"),
        },
        ExprKind::Lam(binder, annot, body) => {
            let annot = type_with(env, annot)?;
            let annot_nf = annot.normalize_whnf(env.as_nzenv());
            let body =
                type_with(&env.insert_type(&binder, annot_nf.clone()), body)?;
            let ty = Value::from_kind_and_type(
                ValueKind::PiClosure {
                    binder: Binder::new(binder.clone()),
                    annot: annot_nf,
                    closure: Closure::new(
                        env.as_nzenv(),
                        body.get_type()?.to_tyexpr(env.as_quoteenv().insert()),
                    ),
                },
                Value::from_const(Const::Type), // TODO: function_check
            );
            (
                TyExprKind::Expr(ExprKind::Lam(binder.clone(), annot, body)),
                Some(ty),
            )
        }
        ExprKind::Pi(binder, annot, body) => {
            let annot = type_with(env, annot)?;
            let annot_nf = annot.normalize_whnf(env.as_nzenv());
            let body =
                type_with(&env.insert_type(binder, annot_nf.clone()), body)?;
            (
                TyExprKind::Expr(ExprKind::Pi(binder.clone(), annot, body)),
                Some(Value::from_const(Const::Type)), // TODO: function_check
            )
        }
        ExprKind::Let(binder, annot, val, body) => {
            let v = if let Some(t) = annot {
                t.rewrap(ExprKind::Annot(val.clone(), t.clone()))
            } else {
                val.clone()
            };

            let val = type_with(env, val)?;
            let val_nf = val.normalize_whnf(&env.as_nzenv());
            let body = type_with(&env.insert_value(&binder, val_nf), body)?;
            let body_ty = body.get_type().ok();
            (
                TyExprKind::Expr(ExprKind::Let(
                    binder.clone(),
                    None,
                    val,
                    body,
                )),
                body_ty,
            )
        }
        ExprKind::Const(Const::Sort) => {
            (TyExprKind::Expr(ExprKind::Const(Const::Sort)), None)
        }
        ExprKind::Embed(p) => {
            return Ok(p.clone().into_typed().into_value().to_tyexpr_noenv())
        }
        ekind => {
            let ekind = ekind.traverse_ref(|e| type_with(env, e))?;
            let ty = type_last_layer(env, &ekind)?;
            (TyExprKind::Expr(ekind), Some(ty))
        }
    };

    Ok(TyExpr::new(tyekind, ty, expr.span()))
}

pub(crate) fn typecheck(e: &Expr<Normalized>) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), e)
}
