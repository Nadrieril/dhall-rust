use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;

use crate::error::{ErrorBuilder, TypeError, TypeMessage};
use crate::semantics::merge_maps;
use crate::semantics::{
    type_of_builtin, Binder, BuiltinClosure, Closure, TyEnv, TyExpr,
    TyExprKind, Type, Value, ValueKind,
};
use crate::syntax::{
    BinOp, Builtin, Const, Expr, ExprKind, InterpolatedTextContents, Span,
};
use crate::Normalized;

fn type_of_recordtype<'a>(
    span: Span,
    tys: impl Iterator<Item = Cow<'a, TyExpr>>,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| {
        mkerr(
            ErrorBuilder::new(msg.to_string())
                .span_err(span.clone(), msg.to_string())
                .format(),
        )
    };
    // An empty record type has type Type
    let mut k = Const::Type;
    for t in tys {
        match t.get_type()?.as_const() {
            Some(c) => k = max(k, c),
            None => return span_err("InvalidFieldType"),
        }
    }
    Ok(Value::from_const(k))
}

fn function_check(a: Const, b: Const) -> Const {
    if b == Const::Type {
        Const::Type
    } else {
        max(a, b)
    }
}

fn mkerr<T, S: ToString>(x: S) -> Result<T, TypeError> {
    Err(TypeError::new(TypeMessage::Custom(x.to_string())))
}

/// When all sub-expressions have been typed, check the remaining toplevel
/// layer.
fn type_one_layer(
    env: &TyEnv,
    kind: &ExprKind<TyExpr, Normalized>,
    span: Span,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| {
        mkerr(
            ErrorBuilder::new(msg.to_string())
                .span_err(span.clone(), msg.to_string())
                .format(),
        )
    };

    Ok(match kind {
        ExprKind::Import(..) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        ExprKind::Var(..)
        | ExprKind::Const(Const::Sort)
        | ExprKind::Embed(..) => unreachable!(), // Handled in type_with

        ExprKind::Lam(binder, annot, body) => {
            let body_ty = body.get_type()?;
            let body_ty = body_ty.to_tyexpr(env.as_varenv().insert());
            let pi_ekind = ExprKind::Pi(binder.clone(), annot.clone(), body_ty);
            let pi_ty = type_one_layer(env, &pi_ekind, Span::Artificial)?;
            let ty = TyExpr::new(
                TyExprKind::Expr(pi_ekind),
                Some(pi_ty),
                Span::Artificial,
            );
            ty.eval(env.as_nzenv())
        }
        ExprKind::Pi(_, annot, body) => {
            let ks = match annot.get_type()?.as_const() {
                Some(k) => k,
                _ => {
                    return mkerr(
                        ErrorBuilder::new(format!(
                            "Invalid input type: `{}`",
                            annot.get_type()?.to_expr_tyenv(env),
                        ))
                        .span_err(
                            annot.span(),
                            format!(
                                "this has type: `{}`",
                                annot.get_type()?.to_expr_tyenv(env)
                            ),
                        )
                        .help(format!(
                            "The input type of a function must have type \
                             `Type`, `Kind` or `Sort`",
                        ))
                        .format(),
                    );
                }
            };
            let kt = match body.get_type()?.as_const() {
                Some(k) => k,
                _ => return span_err("Invalid output type"),
            };

            Value::from_const(function_check(ks, kt))
        }
        ExprKind::Let(_, _, _, body) => body.get_type()?,

        ExprKind::Const(Const::Type) => Value::from_const(Const::Kind),
        ExprKind::Const(Const::Kind) => Value::from_const(Const::Sort),
        ExprKind::Builtin(b) => {
            let t_expr = type_of_builtin(*b);
            let t_tyexpr = type_with(env, &t_expr)?;
            t_tyexpr.eval(env.as_nzenv())
        }
        ExprKind::BoolLit(_) => Value::from_builtin(Builtin::Bool),
        ExprKind::NaturalLit(_) => Value::from_builtin(Builtin::Natural),
        ExprKind::IntegerLit(_) => Value::from_builtin(Builtin::Integer),
        ExprKind::DoubleLit(_) => Value::from_builtin(Builtin::Double),
        ExprKind::TextLit(interpolated) => {
            let text_type = Value::from_builtin(Builtin::Text);
            for contents in interpolated.iter() {
                use InterpolatedTextContents::Expr;
                if let Expr(x) = contents {
                    if x.get_type()? != text_type {
                        return span_err("InvalidTextInterpolation");
                    }
                }
            }
            text_type
        }
        ExprKind::EmptyListLit(t) => {
            let t = t.eval(env.as_nzenv());
            match &*t.kind() {
                ValueKind::AppliedBuiltin(BuiltinClosure {
                    b: Builtin::List,
                    args,
                    ..
                }) if args.len() == 1 => {}
                _ => return span_err("InvalidListType"),
            };
            t
        }
        ExprKind::NEListLit(xs) => {
            let mut iter = xs.iter();
            let x = iter.next().unwrap();
            for y in iter {
                if x.get_type()? != y.get_type()? {
                    return span_err("InvalidListElement");
                }
            }
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Const::Type) {
                return span_err("InvalidListType");
            }

            Value::from_builtin(Builtin::List).app(t)
        }
        ExprKind::SomeLit(x) => {
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Const::Type) {
                return span_err("InvalidOptionalType");
            }

            Value::from_builtin(Builtin::Optional).app(t)
        }
        ExprKind::RecordLit(kvs) => {
            use std::collections::hash_map::Entry;
            let mut kts = HashMap::new();
            for (x, v) in kvs {
                // Check for duplicated entries
                match kts.entry(x.clone()) {
                    Entry::Occupied(_) => {
                        return span_err("RecordTypeDuplicateField")
                    }
                    Entry::Vacant(e) => e.insert(v.get_type()?),
                };
            }

            let ty = type_of_recordtype(
                span,
                kts.iter()
                    .map(|(_, t)| Cow::Owned(t.to_tyexpr(env.as_varenv()))),
            )?;
            Value::from_kind_and_type(ValueKind::RecordType(kts), ty)
        }
        ExprKind::RecordType(kts) => {
            use std::collections::hash_map::Entry;
            let mut seen_fields = HashMap::new();
            for (x, _) in kts {
                // Check for duplicated entries
                match seen_fields.entry(x.clone()) {
                    Entry::Occupied(_) => {
                        return span_err("RecordTypeDuplicateField")
                    }
                    Entry::Vacant(e) => e.insert(()),
                };
            }

            type_of_recordtype(span, kts.iter().map(|(_, t)| Cow::Borrowed(t)))?
        }
        ExprKind::UnionType(kts) => {
            use std::collections::hash_map::Entry;
            let mut seen_fields = HashMap::new();
            // Check that all types are the same const
            let mut k = None;
            for (x, t) in kts {
                if let Some(t) = t {
                    match (k, t.get_type()?.as_const()) {
                        (None, Some(k2)) => k = Some(k2),
                        (Some(k1), Some(k2)) if k1 == k2 => {}
                        _ => return span_err("InvalidFieldType"),
                    }
                }
                match seen_fields.entry(x) {
                    Entry::Occupied(_) => {
                        return span_err("UnionTypeDuplicateField")
                    }
                    Entry::Vacant(e) => e.insert(()),
                };
            }

            // An empty union type has type Type;
            // an union type with only unary variants also has type Type
            let k = k.unwrap_or(Const::Type);

            Value::from_const(k)
        }
        ExprKind::Field(scrut, x) => {
            match &*scrut.get_type()?.kind() {
                ValueKind::RecordType(kts) => match kts.get(&x) {
                    Some(tth) => tth.clone(),
                    None => return span_err("MissingRecordField"),
                },
                // TODO: branch here only when scrut.get_type() is a Const
                _ => {
                    let scrut_nf = scrut.eval(env.as_nzenv());
                    match scrut_nf.kind() {
                        ValueKind::UnionType(kts) => match kts.get(x) {
                            // Constructor has type T -> < x: T, ... >
                            Some(Some(ty)) => {
                                // Can't fail because uniontypes must have type Const(_).
                                let kt = scrut.get_type()?.as_const().unwrap();
                                // The type of the field must be Const smaller than `kt`, thus the
                                // function type has type `kt`.
                                let pi_ty = Value::from_const(kt);

                                Value::from_kind_and_type(
                                    ValueKind::PiClosure {
                                        binder: Binder::new(x.clone()),
                                        annot: ty.clone(),
                                        closure: Closure::new_constant(
                                            scrut_nf,
                                        ),
                                    },
                                    pi_ty,
                                )
                            }
                            Some(None) => scrut_nf,
                            None => return span_err("MissingUnionField"),
                        },
                        _ => return span_err("NotARecord"),
                    }
                } // _ => span_err("NotARecord"),
            }
        }
        ExprKind::Annot(x, t) => {
            let t = t.eval(env.as_nzenv());
            let x_ty = x.get_type()?;
            if x_ty != t {
                return span_err(&format!(
                    "annot mismatch: ({} : {}) : {}",
                    x.to_expr_tyenv(env),
                    x_ty.to_tyexpr(env.as_varenv()).to_expr_tyenv(env),
                    t.to_tyexpr(env.as_varenv()).to_expr_tyenv(env)
                ));
                // return span_err(format!(
                //     "annot mismatch: {} != {}",
                //     x_ty.to_tyexpr(env.as_varenv()).to_expr_tyenv(env),
                //     t.to_tyexpr(env.as_varenv()).to_expr_tyenv(env)
                // ));
                // return span_err(format!("annot mismatch: {:#?} : {:#?}", x, t,));
            }
            x_ty
        }
        ExprKind::Assert(t) => {
            let t = t.eval(env.as_nzenv());
            match &*t.kind() {
                ValueKind::Equivalence(x, y) if x == y => {}
                ValueKind::Equivalence(..) => {
                    return span_err("AssertMismatch")
                }
                _ => return span_err("AssertMustTakeEquivalence"),
            }
            t
        }
        ExprKind::App(f, arg) => {
            match f.get_type()?.kind() {
                ValueKind::PiClosure { annot, closure, .. } => {
                    if arg.get_type()? != *annot {
                        return mkerr(
                            ErrorBuilder::new(format!(
                                "wrong type of function argument"
                            ))
                            .span_err(
                                f.span(),
                                format!(
                                    "this expects an argument of type: {}",
                                    annot.to_expr_tyenv(env),
                                ),
                            )
                            .span_err(
                                arg.span(),
                                format!(
                                    "but this has type: {}",
                                    arg.get_type()?.to_expr_tyenv(env),
                                ),
                            )
                            .note(format!(
                                "expected type `{}`\n   found type `{}`",
                                annot.to_expr_tyenv(env),
                                arg.get_type()?.to_expr_tyenv(env),
                            ))
                            .format(),
                        );
                    }

                    let arg_nf = arg.eval(env.as_nzenv());
                    closure.apply(arg_nf)
                }
                _ => return mkerr(
                    ErrorBuilder::new(format!(
                        "expected function, found `{}`",
                        f.get_type()?.to_expr_tyenv(env)
                    ))
                    .span_err(
                        f.span(),
                        format!("function application requires a function",),
                    )
                    .format(),
                ),
            }
        }
        ExprKind::BoolIf(x, y, z) => {
            if *x.get_type()?.kind() != ValueKind::from_builtin(Builtin::Bool) {
                return span_err("InvalidPredicate");
            }
            if y.get_type()?.get_type()?.as_const() != Some(Const::Type) {
                return span_err("IfBranchMustBeTerm");
            }
            if z.get_type()?.get_type()?.as_const() != Some(Const::Type) {
                return span_err("IfBranchMustBeTerm");
            }
            if y.get_type()? != z.get_type()? {
                return span_err("IfBranchMismatch");
            }

            y.get_type()?
        }
        ExprKind::BinOp(BinOp::RightBiasedRecordMerge, x, y) => {
            let x_type = x.get_type()?;
            let y_type = y.get_type()?;

            // Extract the LHS record type
            let kts_x = match x_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("MustCombineRecord"),
            };
            // Extract the RHS record type
            let kts_y = match y_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("MustCombineRecord"),
            };

            // Union the two records, prefering
            // the values found in the RHS.
            let kts = merge_maps::<_, _, _, !>(kts_x, kts_y, |_, _, r_t| {
                Ok(r_t.clone())
            })?;

            // Construct the final record type
            let ty = type_of_recordtype(
                span,
                kts.iter()
                    .map(|(_, t)| Cow::Owned(t.to_tyexpr(env.as_varenv()))),
            )?;
            Value::from_kind_and_type(ValueKind::RecordType(kts), ty)
        }
        ExprKind::BinOp(BinOp::RecursiveRecordMerge, x, y) => {
            let ekind = ExprKind::BinOp(
                BinOp::RecursiveRecordTypeMerge,
                x.get_type()?.to_tyexpr(env.as_varenv()),
                y.get_type()?.to_tyexpr(env.as_varenv()),
            );
            let ty = type_one_layer(env, &ekind, Span::Artificial)?;
            TyExpr::new(TyExprKind::Expr(ekind), Some(ty), Span::Artificial)
                .eval(env.as_nzenv())
        }
        ExprKind::BinOp(BinOp::RecursiveRecordTypeMerge, x, y) => {
            let x_val = x.eval(env.as_nzenv());
            let y_val = y.eval(env.as_nzenv());
            let kts_x = match x_val.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("RecordTypeMergeRequiresRecordType"),
            };
            let kts_y = match y_val.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("RecordTypeMergeRequiresRecordType"),
            };
            for (k, tx) in kts_x {
                if let Some(ty) = kts_y.get(k) {
                    type_one_layer(
                        env,
                        &ExprKind::BinOp(
                            BinOp::RecursiveRecordTypeMerge,
                            tx.to_tyexpr(env.as_varenv()),
                            ty.to_tyexpr(env.as_varenv()),
                        ),
                        Span::Artificial,
                    )?;
                }
            }

            // A RecordType's type is always a const
            let xk = x.get_type()?.as_const().unwrap();
            let yk = y.get_type()?.as_const().unwrap();
            Value::from_const(max(xk, yk))
        }
        ExprKind::BinOp(BinOp::ListAppend, l, r) => {
            let l_ty = l.get_type()?;
            match &*l_ty.kind() {
                ValueKind::AppliedBuiltin(BuiltinClosure {
                    b: Builtin::List,
                    ..
                }) => {}
                _ => return span_err("BinOpTypeMismatch"),
            }

            if l_ty != r.get_type()? {
                return span_err("BinOpTypeMismatch");
            }

            l_ty
        }
        ExprKind::BinOp(BinOp::Equivalence, l, r) => {
            if l.get_type()? != r.get_type()? {
                return span_err("EquivalenceTypeMismatch");
            }
            if l.get_type()?.get_type()?.as_const() != Some(Const::Type) {
                return span_err("EquivalenceArgumentsMustBeTerms");
            }

            Value::from_const(Const::Type)
        }
        ExprKind::BinOp(o, l, r) => {
            let t = Value::from_builtin(match o {
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
                return span_err("BinOpTypeMismatch");
            }

            if r.get_type()? != t {
                return span_err("BinOpTypeMismatch");
            }

            t
        }
        ExprKind::Merge(record, union, type_annot) => {
            let record_type = record.get_type()?;
            let handlers = match record_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("Merge1ArgMustBeRecord"),
            };

            let union_type = union.get_type()?;
            let variants = match union_type.kind() {
                ValueKind::UnionType(kts) => Cow::Borrowed(kts),
                ValueKind::AppliedBuiltin(BuiltinClosure {
                    b: Builtin::Optional,
                    args,
                    ..
                }) if args.len() == 1 => {
                    let ty = &args[0];
                    let mut kts = HashMap::new();
                    kts.insert("None".into(), None);
                    kts.insert("Some".into(), Some(ty.clone()));
                    Cow::Owned(kts)
                }
                _ => return span_err("Merge2ArgMustBeUnionOrOptional"),
            };

            let mut inferred_type = None;
            for (x, handler_type) in handlers {
                let handler_return_type = match variants.get(x) {
                    // Union alternative with type
                    Some(Some(variant_type)) => match handler_type.kind() {
                        ValueKind::PiClosure { closure, annot, .. } => {
                            if variant_type != annot {
                                return mkerr(
                                    ErrorBuilder::new(format!(
                                        "Wrong handler input type"
                                    ))
                                    .span_err(
                                        span,
                                        format!("in this merge expression",),
                                    )
                                    .span_err(
                                        record.span(),
                                        format!(
                                            "the handler for `{}` expects a \
                                             value of type: `{}`",
                                            x,
                                            annot.to_expr_tyenv(env)
                                        ),
                                    )
                                    .span_err(
                                        union.span(),
                                        format!(
                                            "but the corresponding variant \
                                             has type: `{}`",
                                            variant_type.to_expr_tyenv(env)
                                        ),
                                    )
                                    .format(),
                                );
                            }

                            closure.remove_binder().or_else(|()| {
                                span_err("MergeReturnTypeIsDependent")
                            })?
                        }
                        _ => {
                            return mkerr(
                                ErrorBuilder::new(format!(
                                    "merge handler is not a function"
                                ))
                                .span_err(
                                    span,
                                    format!("in this merge expression"),
                                )
                                .span_err(
                                    record.span(),
                                    format!(
                                        "the handler for `{}` has type: `{}`",
                                        x,
                                        handler_type.to_expr_tyenv(env)
                                    ),
                                )
                                .span_help(
                                    union.span(),
                                    format!(
                                        "the corresponding variant has type: \
                                         `{}`",
                                        variant_type.to_expr_tyenv(env)
                                    ),
                                )
                                .help(format!(
                                    "a handler for this variant must be a \
                                     function that takes an input of type: \
                                     `{}`",
                                    variant_type.to_expr_tyenv(env)
                                ))
                                .format(),
                            )
                        }
                    },
                    // Union alternative without type
                    Some(None) => handler_type.clone(),
                    None => return span_err("MergeHandlerMissingVariant"),
                };
                match &inferred_type {
                    None => inferred_type = Some(handler_return_type),
                    Some(t) => {
                        if t != &handler_return_type {
                            return span_err("MergeHandlerTypeMismatch");
                        }
                    }
                }
            }
            for x in variants.keys() {
                if !handlers.contains_key(x) {
                    return span_err("MergeVariantMissingHandler");
                }
            }

            let type_annot =
                type_annot.as_ref().map(|t| t.eval(env.as_nzenv()));
            match (inferred_type, type_annot) {
                (Some(t1), Some(t2)) => {
                    if t1 != t2 {
                        return span_err("MergeAnnotMismatch");
                    }
                    t1
                }
                (Some(t), None) => t,
                (None, Some(t)) => t,
                (None, None) => return span_err("MergeEmptyNeedsAnnotation"),
            }
        }
        ExprKind::ToMap(_, _) => unimplemented!("toMap"),
        ExprKind::Projection(record, labels) => {
            let record_type = record.get_type()?;
            let kts = match record_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("ProjectionMustBeRecord"),
            };

            let mut new_kts = HashMap::new();
            for l in labels {
                match kts.get(l) {
                    None => return span_err("ProjectionMissingEntry"),
                    Some(t) => {
                        use std::collections::hash_map::Entry;
                        match new_kts.entry(l.clone()) {
                            Entry::Occupied(_) => {
                                return span_err("ProjectionDuplicateField")
                            }
                            Entry::Vacant(e) => e.insert(t.clone()),
                        }
                    }
                };
            }

            Value::from_kind_and_type(
                ValueKind::RecordType(new_kts),
                record_type.get_type()?,
            )
        }
        ExprKind::ProjectionByExpr(_, _) => {
            unimplemented!("selection by expression")
        }
        ExprKind::Completion(_, _) => unimplemented!("record completion"),
    })
}

/// `type_with` typechecks an expressio in the provided environment.
pub(crate) fn type_with(
    env: &TyEnv,
    expr: &Expr<Normalized>,
) -> Result<TyExpr, TypeError> {
    let (tyekind, ty) = match expr.as_ref() {
        ExprKind::Var(var) => match env.lookup(&var) {
            Some((v, ty)) => (TyExprKind::Var(v), Some(ty)),
            None => {
                return mkerr(
                    ErrorBuilder::new(format!("unbound variable `{}`", var))
                        .span_err(expr.span(), "not found in this scope")
                        .format(),
                )
            }
        },
        ExprKind::Const(Const::Sort) => {
            (TyExprKind::Expr(ExprKind::Const(Const::Sort)), None)
        }
        ExprKind::Embed(p) => {
            return Ok(p.clone().into_value().to_tyexpr_noenv())
        }
        ekind => {
            let ekind = match ekind {
                ExprKind::Lam(binder, annot, body) => {
                    let annot = type_with(env, annot)?;
                    let annot_nf = annot.eval(env.as_nzenv());
                    let body_env = env.insert_type(binder, annot_nf);
                    let body = type_with(&body_env, body)?;
                    ExprKind::Lam(binder.clone(), annot, body)
                }
                ExprKind::Pi(binder, annot, body) => {
                    let annot = type_with(env, annot)?;
                    let annot_nf = annot.eval(env.as_nzenv());
                    let body_env = env.insert_type(binder, annot_nf);
                    let body = type_with(&body_env, body)?;
                    ExprKind::Pi(binder.clone(), annot, body)
                }
                ExprKind::Let(binder, annot, val, body) => {
                    let val = if let Some(t) = annot {
                        t.rewrap(ExprKind::Annot(val.clone(), t.clone()))
                    } else {
                        val.clone()
                    };
                    let val = type_with(env, &val)?;
                    val.get_type()?; // Ensure val is not Sort
                    let val_nf = val.eval(&env.as_nzenv());
                    let body_env = env.insert_value(&binder, val_nf);
                    let body = type_with(&body_env, body)?;
                    ExprKind::Let(binder.clone(), None, val, body)
                }
                _ => ekind.traverse_ref(|e| type_with(env, e))?,
            };

            let ty = type_one_layer(env, &ekind, expr.span())?;
            (TyExprKind::Expr(ekind), Some(ty))
        }
    };

    Ok(TyExpr::new(tyekind, ty, expr.span()))
}

/// Typecheck an expression and return the expression annotated with types if type-checking
/// succeeded, or an error if type-checking failed.
pub(crate) fn typecheck(e: &Expr<Normalized>) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), e)
}

/// Like `typecheck`, but additionally checks that the expression's type matches the provided type.
pub(crate) fn typecheck_with(
    expr: &Expr<Normalized>,
    ty: Expr<Normalized>,
) -> Result<TyExpr, TypeError> {
    typecheck(&expr.rewrap(ExprKind::Annot(expr.clone(), ty)))
}
