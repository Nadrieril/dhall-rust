use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;

use crate::error::{ErrorBuilder, TypeError, TypeMessage};
use crate::semantics::merge_maps;
use crate::semantics::{
    type_of_builtin, Binder, BuiltinClosure, Closure, Hir, HirKind, TyEnv,
    TyExpr, Type, Value, ValueKind,
};
use crate::syntax::{
    BinOp, Builtin, Const, ExprKind, InterpolatedTextContents, LitKind, Span,
};

fn check_rectymerge(
    span: &Span,
    env: &TyEnv,
    x: Type,
    y: Type,
) -> Result<(), TypeError> {
    let kts_x = match x.kind() {
        ValueKind::RecordType(kts) => kts,
        _ => {
            return mk_span_err(
                span.clone(),
                "RecordTypeMergeRequiresRecordType",
            )
        }
    };
    let kts_y = match y.kind() {
        ValueKind::RecordType(kts) => kts,
        _ => {
            return mk_span_err(
                span.clone(),
                "RecordTypeMergeRequiresRecordType",
            )
        }
    };
    for (k, tx) in kts_x {
        if let Some(ty) = kts_y.get(k) {
            check_rectymerge(span, env, tx.clone(), ty.clone())?;
        }
    }
    Ok(())
}

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
    env: &TyEnv,
    ekind: ExprKind<TyExpr>,
    annot: Option<Type>,
    span: Span,
) -> Result<TyExpr, TypeError> {
    let span_err = |msg: &str| mk_span_err(span.clone(), msg);

    let ty = match &ekind {
        ExprKind::Import(..) | ExprKind::Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
        ExprKind::Var(..)
        | ExprKind::Const(Const::Sort)
        | ExprKind::Annot(..) => {
            unreachable!("This case should have been handled in type_with")
        }

        ExprKind::Lam(binder, annot, body) => {
            if annot.ty().as_const().is_none() {
                return mkerr(
                    ErrorBuilder::new(format!(
                        "Invalid input type: `{}`",
                        annot.ty().to_expr_tyenv(env),
                    ))
                    .span_err(
                        annot.span(),
                        format!(
                            "this has type: `{}`",
                            annot.ty().to_expr_tyenv(env)
                        ),
                    )
                    .help(format!(
                        "The input type of a function must have type `Type`, \
                         `Kind` or `Sort`",
                    ))
                    .format(),
                );
            }
            let body_env = env.insert_type(&binder, annot.eval(env));
            if body.get_kind(&body_env)?.is_none() {
                return span_err("Invalid output type");
            }
            Hir::new(
                HirKind::Expr(ExprKind::Pi(
                    binder.clone(),
                    annot.to_hir(),
                    body.ty().to_hir(body_env.as_varenv()),
                )),
                span.clone(),
            )
            .eval(env)
        }
        ExprKind::Pi(_, annot, body) => {
            let ks = match annot.ty().as_const() {
                Some(k) => k,
                _ => {
                    return mkerr(
                        ErrorBuilder::new(format!(
                            "Invalid input type: `{}`",
                            annot.ty().to_expr_tyenv(env),
                        ))
                        .span_err(
                            annot.span(),
                            format!(
                                "this has type: `{}`",
                                annot.ty().to_expr_tyenv(env)
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
            let kt = match body.ty().as_const() {
                Some(k) => k,
                _ => return span_err("Invalid output type"),
            };

            Value::from_const(function_check(ks, kt))
        }
        ExprKind::Let(_, _, _, body) => body.ty().clone(),

        ExprKind::Const(Const::Type) => Value::from_const(Const::Kind),
        ExprKind::Const(Const::Kind) => Value::from_const(Const::Sort),
        ExprKind::Builtin(b) => {
            let t_hir = type_of_builtin(*b);
            let t_tyexpr = typecheck(&t_hir)?;
            t_tyexpr.eval(env)
        }
        ExprKind::Lit(LitKind::Bool(_)) => Value::from_builtin(Builtin::Bool),
        ExprKind::Lit(LitKind::Natural(_)) => {
            Value::from_builtin(Builtin::Natural)
        }
        ExprKind::Lit(LitKind::Integer(_)) => {
            Value::from_builtin(Builtin::Integer)
        }
        ExprKind::Lit(LitKind::Double(_)) => {
            Value::from_builtin(Builtin::Double)
        }
        ExprKind::TextLit(interpolated) => {
            let text_type = Value::from_builtin(Builtin::Text);
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
        ExprKind::EmptyListLit(t) => {
            let t = t.eval(env);
            match t.kind() {
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
                if x.ty() != y.ty() {
                    return span_err("InvalidListElement");
                }
            }
            if x.get_kind(env)? != Some(Const::Type) {
                return span_err("InvalidListType");
            }

            let t = x.ty().clone();
            Value::from_builtin(Builtin::List).app(t)
        }
        ExprKind::SomeLit(x) => {
            if x.get_kind(env)? != Some(Const::Type) {
                return span_err("InvalidOptionalType");
            }

            let t = x.ty().clone();
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
                    Entry::Vacant(e) => e.insert(v.ty().clone()),
                };

                // Check that the fields have a valid kind
                match v.get_kind(env)? {
                    Some(_) => {}
                    None => return span_err("InvalidFieldType"),
                }
            }

            Value::from_kind(ValueKind::RecordType(kts))
        }
        ExprKind::RecordType(kts) => {
            use std::collections::hash_map::Entry;
            let mut seen_fields = HashMap::new();
            // An empty record type has type Type
            let mut k = Const::Type;

            for (x, t) in kts {
                // Check for duplicated entries
                match seen_fields.entry(x.clone()) {
                    Entry::Occupied(_) => {
                        return span_err("RecordTypeDuplicateField")
                    }
                    Entry::Vacant(e) => e.insert(()),
                };

                // Check the type is a Const and compute final type
                match t.ty().as_const() {
                    Some(c) => k = max(k, c),
                    None => return span_err("InvalidFieldType"),
                }
            }

            Value::from_const(k)
        }
        ExprKind::UnionType(kts) => {
            use std::collections::hash_map::Entry;
            let mut seen_fields = HashMap::new();
            // Check that all types are the same const
            let mut k = None;
            for (x, t) in kts {
                if let Some(t) = t {
                    match (k, t.ty().as_const()) {
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
            match scrut.ty().kind() {
                ValueKind::RecordType(kts) => match kts.get(&x) {
                    Some(tth) => tth.clone(),
                    None => return span_err("MissingRecordField"),
                },
                // TODO: branch here only when scrut.ty() is a Const
                _ => {
                    let scrut_nf = scrut.eval(env);
                    match scrut_nf.kind() {
                        ValueKind::UnionType(kts) => match kts.get(x) {
                            // Constructor has type T -> < x: T, ... >
                            Some(Some(ty)) => {
                                Value::from_kind(ValueKind::PiClosure {
                                    binder: Binder::new(x.clone()),
                                    annot: ty.clone(),
                                    closure: Closure::new_constant(scrut_nf),
                                })
                            }
                            Some(None) => scrut_nf,
                            None => return span_err("MissingUnionField"),
                        },
                        _ => return span_err("NotARecord"),
                    }
                } // _ => span_err("NotARecord"),
            }
        }
        ExprKind::Assert(t) => {
            let t = t.eval(env);
            match t.kind() {
                ValueKind::Equivalence(x, y) if x == y => {}
                ValueKind::Equivalence(..) => {
                    return span_err("AssertMismatch")
                }
                _ => return span_err("AssertMustTakeEquivalence"),
            }
            t
        }
        ExprKind::App(f, arg) => {
            match f.ty().kind() {
                ValueKind::PiClosure { annot, closure, .. } => {
                    if arg.ty() != annot {
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
                                    arg.ty().to_expr_tyenv(env),
                                ),
                            )
                            .note(format!(
                                "expected type `{}`\n   found type `{}`",
                                annot.to_expr_tyenv(env),
                                arg.ty().to_expr_tyenv(env),
                            ))
                            .format(),
                        );
                    }

                    let arg_nf = arg.eval(env);
                    closure.apply(arg_nf)
                }
                _ => return mkerr(
                    ErrorBuilder::new(format!(
                        "expected function, found `{}`",
                        f.ty().to_expr_tyenv(env)
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
            if *x.ty().kind() != ValueKind::from_builtin(Builtin::Bool) {
                return span_err("InvalidPredicate");
            }
            if y.get_kind(env)? != Some(Const::Type) {
                return span_err("IfBranchMustBeTerm");
            }
            if y.ty() != z.ty() {
                return span_err("IfBranchMismatch");
            }

            y.ty().clone()
        }
        ExprKind::BinOp(BinOp::RightBiasedRecordMerge, x, y) => {
            let x_type = x.ty();
            let y_type = y.ty();

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

            Value::from_kind(ValueKind::RecordType(kts))
        }
        ExprKind::BinOp(BinOp::RecursiveRecordMerge, x, y) => {
            check_rectymerge(&span, env, x.ty().clone(), y.ty().clone())?;

            Hir::new(
                HirKind::Expr(ExprKind::BinOp(
                    BinOp::RecursiveRecordTypeMerge,
                    x.ty().to_hir(env.as_varenv()),
                    y.ty().to_hir(env.as_varenv()),
                )),
                span.clone(),
            )
            .eval(env)
        }
        ExprKind::BinOp(BinOp::RecursiveRecordTypeMerge, x, y) => {
            check_rectymerge(&span, env, x.eval(env), y.eval(env))?;

            // A RecordType's type is always a const
            let xk = x.ty().as_const().unwrap();
            let yk = y.ty().as_const().unwrap();
            Value::from_const(max(xk, yk))
        }
        ExprKind::BinOp(BinOp::ListAppend, l, r) => {
            match l.ty().kind() {
                ValueKind::AppliedBuiltin(BuiltinClosure {
                    b: Builtin::List,
                    ..
                }) => {}
                _ => return span_err("BinOpTypeMismatch"),
            }

            if l.ty() != r.ty() {
                return span_err("BinOpTypeMismatch");
            }

            l.ty().clone()
        }
        ExprKind::BinOp(BinOp::Equivalence, l, r) => {
            if l.ty() != r.ty() {
                return span_err("EquivalenceTypeMismatch");
            }
            if l.get_kind(env)? != Some(Const::Type) {
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

            if *l.ty() != t {
                return span_err("BinOpTypeMismatch");
            }

            if *r.ty() != t {
                return span_err("BinOpTypeMismatch");
            }

            t
        }
        ExprKind::Merge(record, union, type_annot) => {
            let record_type = record.ty();
            let handlers = match record_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("Merge1ArgMustBeRecord"),
            };

            let union_type = union.ty();
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

                            match closure.remove_binder() {
                                Ok(v) => v,
                                Err(()) => {
                                    return span_err(
                                        "MergeReturnTypeIsDependent",
                                    )
                                }
                            }
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

            let type_annot = type_annot.as_ref().map(|t| t.eval(env));
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
        ExprKind::ToMap(record, annot) => {
            if record.get_kind(env)? != Some(Const::Type) {
                return span_err("`toMap` only accepts records of type `Type`");
            }
            let record_t = record.ty();
            let kts = match record_t.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => {
                    return span_err("The argument to `toMap` must be a record")
                }
            };

            if kts.is_empty() {
                let annot = if let Some(annot) = annot {
                    annot
                } else {
                    return span_err(
                        "`toMap` applied to an empty record requires a type \
                         annotation",
                    );
                };
                let annot_val = annot.eval(env);

                let err_msg = "The type of `toMap x` must be of the form \
                               `List { mapKey : Text, mapValue : T }`";
                let arg = match annot_val.kind() {
                    ValueKind::AppliedBuiltin(BuiltinClosure {
                        b: Builtin::List,
                        args,
                        ..
                    }) if args.len() == 1 => &args[0],
                    _ => return span_err(err_msg),
                };
                let kts = match arg.kind() {
                    ValueKind::RecordType(kts) => kts,
                    _ => return span_err(err_msg),
                };
                if kts.len() != 2 {
                    return span_err(err_msg);
                }
                match kts.get(&"mapKey".into()) {
                    Some(t) if *t == Value::from_builtin(Builtin::Text) => {}
                    _ => return span_err(err_msg),
                }
                match kts.get(&"mapValue".into()) {
                    Some(_) => {}
                    None => return span_err(err_msg),
                }
                annot_val
            } else {
                let entry_type = kts.iter().next().unwrap().1.clone();
                for (_, t) in kts.iter() {
                    if *t != entry_type {
                        return span_err(
                            "Every field of the record must have the same type",
                        );
                    }
                }

                let mut kts = HashMap::new();
                kts.insert("mapKey".into(), Value::from_builtin(Builtin::Text));
                kts.insert("mapValue".into(), entry_type);
                let output_type = Value::from_builtin(Builtin::List)
                    .app(Value::from_kind(ValueKind::RecordType(kts)));
                if let Some(annot) = annot {
                    let annot_val = annot.eval(env);
                    if output_type != annot_val {
                        return span_err("Annotation mismatch");
                    }
                }
                output_type
            }
        }
        ExprKind::Projection(record, labels) => {
            let record_type = record.ty();
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

            Value::from_kind(ValueKind::RecordType(new_kts))
        }
        ExprKind::ProjectionByExpr(record, selection) => {
            let record_type = record.ty();
            let rec_kts = match record_type.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("ProjectionMustBeRecord"),
            };

            let selection_val = selection.eval(env);
            let sel_kts = match selection_val.kind() {
                ValueKind::RecordType(kts) => kts,
                _ => return span_err("ProjectionByExprTakesRecordType"),
            };

            for (l, sel_ty) in sel_kts {
                match rec_kts.get(l) {
                    Some(rec_ty) => {
                        if rec_ty != sel_ty {
                            return span_err("ProjectionWrongType");
                        }
                    }
                    None => return span_err("ProjectionMissingEntry"),
                }
            }

            selection_val
        }
    };

    if let Some(annot) = annot {
        if ty != annot {
            return span_err(&format!(
                "annot mismatch: {} != {}",
                ty.to_expr_tyenv(env),
                annot.to_expr_tyenv(env)
            ));
        }
    }

    // TODO: avoid retraversing
    Ok(TyExpr::new(
        HirKind::Expr(ekind.map_ref(|tye| tye.to_hir())),
        ty,
        span,
    ))
}

/// `type_with` typechecks an expression in the provided environment. Optionally pass an annotation
/// to compare with.
pub(crate) fn type_with(
    env: &TyEnv,
    hir: &Hir,
    annot: Option<Type>,
) -> Result<TyExpr, TypeError> {
    match hir.kind() {
        HirKind::Var(var) => {
            Ok(TyExpr::new(HirKind::Var(*var), env.lookup(var), hir.span()))
        }
        HirKind::Expr(ExprKind::Var(_)) => {
            unreachable!("Hir should contain no unresolved variables")
        }
        HirKind::Expr(ExprKind::Const(Const::Sort)) => {
            mk_span_err(hir.span(), "Sort does not have a type")
        }
        HirKind::Expr(ExprKind::Annot(x, t)) => {
            let t = match t.kind() {
                HirKind::Expr(ExprKind::Const(Const::Sort)) => {
                    Value::from_const(Const::Sort)
                }
                _ => type_with(env, t, None)?.eval(env),
            };
            type_with(env, x, Some(t))
        }
        HirKind::Expr(ekind) => {
            let ekind = match ekind {
                ExprKind::Lam(binder, annot, body) => {
                    let annot = type_with(env, annot, None)?;
                    let annot_nf = annot.eval(env);
                    let body_env = env.insert_type(binder, annot_nf);
                    let body = type_with(&body_env, body, None)?;
                    ExprKind::Lam(binder.clone(), annot, body)
                }
                ExprKind::Pi(binder, annot, body) => {
                    let annot = type_with(env, annot, None)?;
                    let annot_nf = annot.eval(env);
                    let body_env = env.insert_type(binder, annot_nf);
                    let body = type_with(&body_env, body, None)?;
                    ExprKind::Pi(binder.clone(), annot, body)
                }
                ExprKind::Let(binder, annot, val, body) => {
                    let val_annot = if let Some(t) = annot {
                        Some(type_with(env, t, None)?.eval(env))
                    } else {
                        None
                    };
                    let val = type_with(env, &val, val_annot)?;
                    let val_nf = val.eval(env);
                    let body_env =
                        env.insert_value(&binder, val_nf, val.ty().clone());
                    let body = type_with(&body_env, body, None)?;
                    ExprKind::Let(binder.clone(), None, val, body)
                }
                _ => ekind.traverse_ref(|e| type_with(env, e, None))?,
            };
            type_one_layer(env, ekind, annot, hir.span())
        }
    }
}

/// Typecheck an expression and return the expression annotated with types if type-checking
/// succeeded, or an error if type-checking failed.
pub(crate) fn typecheck(hir: &Hir) -> Result<TyExpr, TypeError> {
    type_with(&TyEnv::new(), hir, None)
}

/// Like `typecheck`, but additionally checks that the expression's type matches the provided type.
pub(crate) fn typecheck_with(hir: &Hir, ty: Hir) -> Result<TyExpr, TypeError> {
    let ty = typecheck(&ty)?.eval(&TyEnv::new());
    type_with(&TyEnv::new(), hir, Some(ty))
}
