use std::cmp::max;

use crate::builtins::{type_of_builtin, Builtin};
use crate::error::{ErrorBuilder, TypeError, TypeMessage};
use crate::operations::typecheck_operation;
use crate::semantics::{Hir, HirKind, Nir, NirKind, Tir, TyEnv, Type};
use crate::syntax::{Const, ExprKind, InterpolatedTextContents, NumKind, Span};
use crate::Ctxt;

fn function_check(a: Const, b: Const) -> Const {
    if b == Const::Type {
        Const::Type
    } else {
        max(a, b)
    }
}

pub fn mkerr<T, S: ToString>(msg: S) -> Result<T, TypeError> {
    Err(TypeError::new(TypeMessage::Custom(msg.to_string())))
}

pub fn mk_span_err<T, S: ToString>(span: Span, msg: S) -> Result<T, TypeError> {
    mkerr(
        ErrorBuilder::new(msg.to_string())
            .span_err(span, msg.to_string())
            .format(),
    )
}

/// When all sub-expressions have been typed, check the remaining toplevel
/// layer.
fn type_one_layer(
    env: &TyEnv<'_>,
    ekind: ExprKind<Tir<'_>>,
    span: Span,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| mk_span_err(span.clone(), msg);

    Ok(match ekind {
        ExprKind::Import(..) => {
            unreachable!("This case should have been handled in resolution")
        }
        ExprKind::Var(..)
        | ExprKind::Const(Const::Sort)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Annot(..) => {
            unreachable!("This case should have been handled in type_with")
        }

        ExprKind::Const(Const::Type) => Type::from_const(Const::Kind),
        ExprKind::Const(Const::Kind) => Type::from_const(Const::Sort),
        ExprKind::Num(num) => Type::from_builtin(match num {
            NumKind::Bool(_) => Builtin::Bool,
            NumKind::Natural(_) => Builtin::Natural,
            NumKind::Integer(_) => Builtin::Integer,
            NumKind::Double(_) => Builtin::Double,
        }),
        ExprKind::Builtin(b) => {
            let t_hir = type_of_builtin(b);
            typecheck(env.cx(), &t_hir)?.eval_to_type(env)?
        }
        ExprKind::TextLit(interpolated) => {
            let text_type = Type::from_builtin(Builtin::Text);
            for contents in interpolated.iter() {
                use InterpolatedTextContents::Expr;
                if let Expr(x) = contents {
                    if *x.ty() != text_type {
                        return span_err("InvalidTextInterpolation");
                    }
                }
            }
            text_type
        }
        ExprKind::SomeLit(x) => {
            if x.ty().ty().as_const() != Some(Const::Type) {
                return span_err("InvalidOptionalType");
            }

            let t = x.ty().to_nir();
            Nir::from_builtin(Builtin::Optional)
                .app(t)
                .to_type(Const::Type)
        }
        ExprKind::EmptyListLit(t) => {
            let t = t.eval_to_type(env)?;
            match t.kind() {
                NirKind::ListType(..) => {}
                _ => return span_err("InvalidListType"),
            };
            t
        }
        ExprKind::NEListLit(xs) => {
            let mut iter = xs.iter();
            let x = iter.next().unwrap();
            for y in iter {
                if x.ty() != y.ty() {
                    return span_err("InvalidListElement");
                }
            }
            if x.ty().ty().as_const() != Some(Const::Type) {
                return span_err("InvalidListType");
            }

            let t = x.ty().to_nir();
            Nir::from_builtin(Builtin::List).app(t).to_type(Const::Type)
        }
        ExprKind::RecordLit(kvs) => {
            // An empty record type has type Type
            let mut k = Const::Type;
            for v in kvs.values() {
                // Check that the fields have a valid kind
                match v.ty().ty().as_const() {
                    Some(c) => k = max(k, c),
                    None => return mk_span_err(v.span(), "InvalidFieldType"),
                }
            }

            let kts = kvs
                .iter()
                .map(|(x, v)| (x.clone(), v.ty().to_nir()))
                .collect();

            Nir::from_kind(NirKind::RecordType(kts)).to_type(k)
        }
        ExprKind::RecordType(kts) => {
            // An empty record type has type Type
            let mut k = Const::Type;
            for t in kts.values() {
                // Check the type is a Const and compute final type
                match t.ty().as_const() {
                    Some(c) => k = max(k, c),
                    None => return mk_span_err(t.span(), "InvalidFieldType"),
                }
            }

            Type::from_const(k)
        }
        ExprKind::UnionType(kts) => {
            // An empty union type has type Type;
            // an union type with only unary variants also has type Type
            let mut k = Const::Type;
            for t in kts.values() {
                if let Some(t) = t {
                    match t.ty().as_const() {
                        Some(c) => k = max(k, c),
                        None => {
                            return mk_span_err(t.span(), "InvalidVariantType")
                        }
                    }
                }
            }

            Type::from_const(k)
        }
        ExprKind::Op(op) => typecheck_operation(env, span, op)?,
        ExprKind::Assert(t) => {
            let t = t.eval_to_type(env)?;
            match t.kind() {
                NirKind::Equivalence(x, y) if x == y => {}
                NirKind::Equivalence(..) => return span_err("AssertMismatch"),
                _ => return span_err("AssertMustTakeEquivalence"),
            }
            t
        }
    })
}

/// `type_with` typechecks an expression in the provided environment. Optionally pass an annotation
/// to compare with.
// We pass the annotation to avoid duplicating the annot checking logic. I hope one day we can use
// it to handle the annotations in merge/toMap/etc. uniformly.
pub fn type_with<'hir>(
    env: &TyEnv<'_>,
    hir: &'hir Hir,
    annot: Option<Type>,
) -> Result<Tir<'hir>, TypeError> {
    let tir = match hir.kind() {
        HirKind::Var(var) => Tir::from_hir(hir, env.lookup(*var)),
        HirKind::Import(_, ty) => Tir::from_hir(hir, ty.clone()),
        HirKind::Expr(ExprKind::Var(_)) => {
            unreachable!("Hir should contain no unresolved variables")
        }
        HirKind::Expr(ExprKind::Const(Const::Sort)) => {
            return mk_span_err(hir.span(), "Sort does not have a type")
        }
        HirKind::Expr(ExprKind::Annot(x, t)) => {
            let t = match t.kind() {
                HirKind::Expr(ExprKind::Const(Const::Sort)) => {
                    Type::from_const(Const::Sort)
                }
                _ => type_with(env, t, None)?.eval_to_type(env)?,
            };
            type_with(env, x, Some(t))?
        }

        HirKind::Expr(ExprKind::Lam(binder, annot, body)) => {
            let annot = type_with(env, annot, None)?;
            let annot_nf = annot.eval_to_type(env)?;
            let body_env = env.insert_type(binder, annot_nf);
            let body = type_with(&body_env, body, None)?;

            let u_annot = annot.ty().as_const().unwrap();
            let u_body = match body.ty().ty().as_const() {
                Some(k) => k,
                _ => return mk_span_err(hir.span(), "Invalid output type"),
            };
            let u = function_check(u_annot, u_body).to_universe();
            let ty_hir = Hir::new(
                HirKind::Expr(ExprKind::Pi(
                    binder.clone(),
                    annot.to_hir(),
                    body.ty().to_hir(body_env.as_varenv()),
                )),
                hir.span(),
            );
            let ty = Type::new(ty_hir.eval(env), u);

            Tir::from_hir(hir, ty)
        }
        HirKind::Expr(ExprKind::Pi(binder, annot, body)) => {
            let annot = type_with(env, annot, None)?;
            let annot_val = annot.eval_to_type(env)?;
            let body_env = env.insert_type(binder, annot_val);
            let body = type_with(&body_env, body, None)?;
            body.ensure_is_type(env)?;

            let ks = annot.ty().as_const().unwrap();
            let kt = body.ty().as_const().unwrap();
            let ty = Type::from_const(function_check(ks, kt));
            Tir::from_hir(hir, ty)
        }
        HirKind::Expr(ExprKind::Let(binder, annot, val, body)) => {
            let val_annot = annot
                .as_ref()
                .map(|t| Ok(type_with(env, t, None)?.eval_to_type(env)?))
                .transpose()?;
            let val = type_with(env, &val, val_annot)?;
            let val_nf = val.eval(env);
            let body_env = env.insert_value(&binder, val_nf, val.ty().clone());
            let body = type_with(&body_env, body, None)?;
            let ty = body.ty().clone();
            Tir::from_hir(hir, ty)
        }
        HirKind::Expr(ekind) => {
            let ekind = ekind.traverse_ref(|e| type_with(env, e, None))?;
            let ty = type_one_layer(env, ekind, hir.span())?;
            Tir::from_hir(hir, ty)
        }
    };

    if let Some(annot) = annot {
        if *tir.ty() != annot {
            return mk_span_err(
                hir.span(),
                &format!(
                    "annot mismatch: {} != {}",
                    tir.ty().to_expr_tyenv(env),
                    annot.to_expr_tyenv(env)
                ),
            );
        }
    }

    Ok(tir)
}

/// Typecheck an expression and return the expression annotated with its type if type-checking
/// succeeded, or an error if type-checking failed.
pub fn typecheck<'hir>(
    cx: Ctxt<'_>,
    hir: &'hir Hir,
) -> Result<Tir<'hir>, TypeError> {
    type_with(&TyEnv::new(cx), hir, None)
}

/// Like `typecheck`, but additionally checks that the expression's type matches the provided type.
pub fn typecheck_with<'hir>(
    cx: Ctxt<'_>,
    hir: &'hir Hir,
    ty: &Hir,
) -> Result<Tir<'hir>, TypeError> {
    let ty = typecheck(cx, ty)?.eval_to_type(&TyEnv::new(cx))?;
    type_with(&TyEnv::new(cx), hir, Some(ty))
}
