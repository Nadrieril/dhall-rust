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
    BinOp, Builtin, Const, Expr, ExprKind, InterpolatedTextContents, Label,
    Span, UnspannedExpr, V,
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

    pub fn insert_type(&self, x: &Label, t: Type) -> Self {
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
    pub fn lookup(&self, var: &V<Label>) -> Option<(TyExprKind, Type)> {
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

fn type_one_layer(
    env: &TyEnv,
    kind: &ExprKind<TyExpr, Normalized>,
) -> Result<Type, TypeError> {
    Ok(match &kind {
        ExprKind::Import(..) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        ExprKind::Var(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Const(Const::Sort)
        | ExprKind::Embed(..) => unreachable!(), // Handled in type_with

        ExprKind::Const(Const::Type) => const_to_value(Const::Kind),
        ExprKind::Const(Const::Kind) => const_to_value(Const::Sort),
        ExprKind::Builtin(b) => {
            type_with(env, &type_of_builtin(*b))?.normalize_whnf(env.as_nzenv())
        }
        ExprKind::BoolLit(_) => builtin_to_value(Builtin::Bool),
        ExprKind::NaturalLit(_) => builtin_to_value(Builtin::Natural),
        ExprKind::IntegerLit(_) => builtin_to_value(Builtin::Integer),
        ExprKind::DoubleLit(_) => builtin_to_value(Builtin::Double),
        ExprKind::TextLit(interpolated) => {
            let text_type = builtin_to_value(Builtin::Text);
            for contents in interpolated.iter() {
                use InterpolatedTextContents::Expr;
                if let Expr(x) = contents {
                    if x.get_type()? != text_type {
                        return mkerr("InvalidTextInterpolation");
                    }
                }
            }
            text_type
        }

        // ExprKind::EmptyListLit(t) => {
        //     let arg = match &*t.as_whnf() {
        //         ValueKind::AppliedBuiltin(Builtin::List, args, _)
        //             if args.len() == 1 =>
        //         {
        //             args[0].clone()
        //         }
        //         _ => return mkerr("InvalidListType"),
        //     };
        //     RetWhole(Value::from_kind_and_type(
        //         ValueKind::EmptyListLit(arg),
        //         t.clone(),
        //     ))
        // }
        ExprKind::NEListLit(xs) => {
            let mut iter = xs.iter().enumerate();
            let (_, x) = iter.next().unwrap();
            for (i, y) in iter {
                if x.get_type()? != y.get_type()? {
                    return mkerr("InvalidListElement");
                }
            }
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Const::Type) {
                return mkerr("InvalidListType");
            }

            Value::from_builtin(Builtin::List).app(t)
        }
        ExprKind::SomeLit(x) => {
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Const::Type) {
                return mkerr("InvalidOptionalType");
            }

            Value::from_builtin(Builtin::Optional).app(t)
        }
        // ExprKind::RecordType(kts) => RetWhole(tck_record_type(
        //     kts.iter().map(|(x, t)| Ok((x.clone(), t.clone()))),
        // )?),
        // ExprKind::UnionType(kts) => RetWhole(tck_union_type(
        //     kts.iter().map(|(x, t)| Ok((x.clone(), t.clone()))),
        // )?),
        // ExprKind::RecordLit(kvs) => RetTypeOnly(tck_record_type(
        //     kvs.iter().map(|(x, v)| Ok((x.clone(), v.get_type()?))),
        // )?),
        ExprKind::Field(r, x) => {
            match &*r.get_type()?.as_whnf() {
                ValueKind::RecordType(kts) => match kts.get(&x) {
                    Some(tth) => tth.clone(),
                    None => return mkerr("MissingRecordField"),
                },
                // TODO: branch here only when r.get_type() is a Const
                _ => {
                    let r_nf = r.normalize_whnf(env.as_nzenv());
                    let r_nf_borrow = r_nf.as_whnf();
                    match &*r_nf_borrow {
                        ValueKind::UnionType(kts) => match kts.get(x) {
                            // Constructor has type T -> < x: T, ... >
                            // TODO: check pi type properly
                            Some(Some(t)) => Value::from_kind_and_type(
                                ValueKind::PiClosure {
                                    binder: Binder::new(x.clone()),
                                    annot: t.clone(),
                                    closure: Closure::new(
                                        t.clone(),
                                        env.as_nzenv(),
                                        r.clone(),
                                    ),
                                },
                                Value::from_const(Const::Type),
                            ),
                            Some(None) => r_nf.clone(),
                            None => return mkerr("MissingUnionField"),
                        },
                        _ => return mkerr("NotARecord"),
                    }
                } // _ => mkerr("NotARecord"),
            }
        }
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
        // ExprKind::BinOp(BinOp::RightBiasedRecordMerge, l, r) => {
        //     let l_type = l.get_type()?;
        //     let r_type = r.get_type()?;

        //     // Extract the LHS record type
        //     let l_type_borrow = l_type.as_whnf();
        //     let kts_x = match &*l_type_borrow {
        //         ValueKind::RecordType(kts) => kts,
        //         _ => return mkerr("MustCombineRecord"),
        //     };

        //     // Extract the RHS record type
        //     let r_type_borrow = r_type.as_whnf();
        //     let kts_y = match &*r_type_borrow {
        //         ValueKind::RecordType(kts) => kts,
        //         _ => return mkerr("MustCombineRecord"),
        //     };

        //     // Union the two records, prefering
        //     // the values found in the RHS.
        //     let kts = merge_maps::<_, _, _, !>(kts_x, kts_y, |_, _, r_t| {
        //         Ok(r_t.clone())
        //     })?;

        //     // Construct the final record type from the union
        //     RetTypeOnly(tck_record_type(
        //         kts.into_iter().map(|(x, v)| Ok((x.clone(), v))),
        //     )?)
        // }
        // ExprKind::BinOp(BinOp::RecursiveRecordMerge, l, r) => RetTypeOnly(type_last_layer(
        //     ctx,
        //     ExprKind::BinOp(
        //         RecursiveRecordTypeMerge,
        //         l.get_type()?,
        //         r.get_type()?,
        //     ),
        //     Span::Artificial,
        // )?),
        // ExprKind::BinOp(BinOp::RecursiveRecordTypeMerge, l, r) => {
        //     // Extract the LHS record type
        //     let borrow_l = l.as_whnf();
        //     let kts_x = match &*borrow_l {
        //         ValueKind::RecordType(kts) => kts,
        //         _ => {
        //             return mkerr("RecordTypeMergeRequiresRecordType")
        //         }
        //     };

        //     // Extract the RHS record type
        //     let borrow_r = r.as_whnf();
        //     let kts_y = match &*borrow_r {
        //         ValueKind::RecordType(kts) => kts,
        //         _ => {
        //             return mkerr("RecordTypeMergeRequiresRecordType")
        //         }
        //     };

        //     // Ensure that the records combine without a type error
        //     let kts = merge_maps(
        //         kts_x,
        //         kts_y,
        //         // If the Label exists for both records, then we hit the recursive case.
        //         |_, l: &Value, r: &Value| {
        //             type_last_layer(
        //                 ctx,
        //                 ExprKind::BinOp(
        //                     RecursiveRecordTypeMerge,
        //                     l.clone(),
        //                     r.clone(),
        //                 ),
        //                 Span::Artificial,
        //             )
        //         },
        //     )?;

        //     RetWhole(tck_record_type(kts.into_iter().map(Ok))?)
        // }
        // ExprKind::BinOp(o @ BinOp::ListAppend, l, r) => {
        //     match &*l.get_type()?.as_whnf() {
        //         ValueKind::AppliedBuiltin(List, _, _) => {}
        //         _ => return mkerr("BinOpTypeMismatch"),
        //     }

        //     if l.get_type()? != r.get_type()? {
        //         return mkerr("BinOpTypeMismatch");
        //     }

        //     l.get_type()?
        // }
        // ExprKind::BinOp(BinOp::Equivalence, l, r) => {
        //     if l.get_type()?.get_type()?.as_const() != Some(Const::Type) {
        //         return mkerr("EquivalenceArgumentMustBeTerm");
        //     }
        //     if r.get_type()?.get_type()?.as_const() != Some(Const::Type) {
        //         return mkerr("EquivalenceArgumentMustBeTerm");
        //     }

        //     if l.get_type()? != r.get_type()? {
        //         return mkerr("EquivalenceTypeMismatch");
        //     }

        //     RetWhole(Value::from_kind_and_type(
        //         ValueKind::Equivalence(l.clone(), r.clone()),
        //         Value::from_const(Type),
        //     ))
        // }
        ExprKind::BinOp(o, l, r) => {
            let t = builtin_to_value(match o {
                BinOp::BoolAnd
                | BinOp::BoolOr
                | BinOp::BoolEQ
                | BinOp::BoolNE => Builtin::Bool,
                BinOp::NaturalPlus | BinOp::NaturalTimes => Builtin::Natural,
                BinOp::TextAppend => Builtin::Text,
                BinOp::ListAppend
                | BinOp::RightBiasedRecordMerge
                | BinOp::RecursiveRecordMerge
                | BinOp::RecursiveRecordTypeMerge
                | BinOp::Equivalence => unreachable!(),
                BinOp::ImportAlt => unreachable!("ImportAlt leftover in tck"),
            });

            if l.get_type()? != t {
                return mkerr("BinOpTypeMismatch");
            }

            if r.get_type()? != t {
                return mkerr("BinOpTypeMismatch");
            }

            t
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
                    annot: annot_nf.clone(),
                    closure: Closure::new(
                        annot_nf,
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
            let ty = type_one_layer(env, &ekind)?;
            (TyExprKind::Expr(ekind), Some(ty))
        }
    };

    Ok(TyExpr::new(tyekind, ty, expr.span()))
}

pub(crate) fn typecheck(e: &Expr<Normalized>) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), e)
}
