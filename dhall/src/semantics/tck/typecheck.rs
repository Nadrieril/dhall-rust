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
    pub fn lookup_var(&self, var: &V<Label>) -> Option<(TyExprKind, Value)> {
        let var = self.names.unlabel_var(var)?;
        let ty = self.lookup_val(&var).get_type().unwrap();
        Some((TyExprKind::Var(var), ty))
    }
    pub fn lookup_val(&self, var: &AlphaVar) -> Value {
        self.items.lookup_val(var)
    }
    pub fn size(&self) -> usize {
        self.names.size()
    }
}

/// Type-check an expression and return the expression alongside its type if type-checking
/// succeeded, or an error if type-checking failed.
fn type_with(env: &TyEnv, expr: Expr<Normalized>) -> Result<TyExpr, TypeError> {
    let mkerr = || TypeError::new(TypeMessage::Sort);

    match expr.as_ref() {
        ExprKind::Var(var) => match env.lookup_var(&var) {
            Some((e, ty)) => Ok(TyExpr::new(e, Some(ty), expr.span())),
            None => Err(mkerr()),
        },
        ExprKind::Lam(binder, annot, body) => {
            let annot = type_with(env, annot.clone())?;
            let annot_nf = annot.normalize_whnf(env.as_nzenv());
            let body = type_with(
                &env.insert_type(&binder, annot_nf.clone()),
                body.clone(),
            )?;
            let ty = Value::from_kind_and_type(
                ValueKind::PiClosure {
                    binder: Binder::new(binder.clone()),
                    annot: annot_nf,
                    closure: Closure::new(
                        env.as_nzenv(),
                        body.get_type()?.to_tyexpr(env.as_quoteenv()),
                    ),
                },
                Value::from_const(Const::Type), // TODO: function_check
            );
            Ok(TyExpr::new(
                TyExprKind::Expr(ExprKind::Lam(binder.clone(), annot, body)),
                Some(ty),
                expr.span(),
            ))
        }
        ExprKind::Pi(binder, annot, body) => {
            let annot = type_with(env, annot.clone())?;
            let annot_nf = annot.normalize_whnf(env.as_nzenv());
            let body = type_with(
                &env.insert_type(binder, annot_nf.clone()),
                body.clone(),
            )?;
            Ok(TyExpr::new(
                TyExprKind::Expr(ExprKind::Pi(binder.clone(), annot, body)),
                None, // TODO: function_check
                expr.span(),
            ))
        }
        kind => {
            let kind = kind.traverse_ref(|e| type_with(env, e.clone()))?;
            let ty = match &kind {
                ExprKind::App(f, arg) => {
                    let tf = f.get_type()?;
                    let tf_borrow = tf.as_whnf();
                    let (_expected_arg_ty, ty_closure) = match &*tf_borrow {
                        ValueKind::PiClosure { annot, closure, .. } => {
                            (annot, closure)
                        }
                        _ => return Err(mkerr()),
                    };
                    // if arg.get_type()? != *expected_arg_ty {
                    //     return Err(mkerr());
                    // }

                    let arg_nf = arg.normalize_whnf(env.as_nzenv());
                    ty_closure.apply(arg_nf)
                }
                _ => Value::from_const(Const::Type), // TODO
            };

            Ok(TyExpr::new(TyExprKind::Expr(kind), Some(ty), expr.span()))
        }
    }
}

pub(crate) fn typecheck(e: Expr<Normalized>) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), e)
}
