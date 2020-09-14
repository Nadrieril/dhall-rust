use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;

use crate::builtins::Builtin;
use crate::error::{ErrorBuilder, TypeError};
use crate::operations::{BinOp, OpKind};
use crate::semantics::{
    merge_maps, mk_span_err, mkerr, Binder, Closure, Hir, HirKind, Nir,
    NirKind, Tir, TyEnv, Type,
};
use crate::syntax::{Const, ExprKind, Span};

fn check_rectymerge(
    span: &Span,
    env: &TyEnv,
    x: Nir,
    y: Nir,
) -> Result<(), TypeError> {
    let kts_x = match x.kind() {
        NirKind::RecordType(kts) => kts,
        _ => {
            return mk_span_err(
                span.clone(),
                "RecordTypeMergeRequiresRecordType",
            )
        }
    };
    let kts_y = match y.kind() {
        NirKind::RecordType(kts) => kts,
        _ => {
            return mk_span_err(
                span.clone(),
                "RecordTypeMergeRequiresRecordType",
            )
        }
    };
    for (k, tx) in kts_x {
        if let Some(ty) = kts_y.get(k) {
            // TODO: store Type in RecordType ?
            check_rectymerge(span, env, tx.clone(), ty.clone())?;
        }
    }
    Ok(())
}

fn typecheck_binop(
    env: &TyEnv,
    span: Span,
    op: BinOp,
    l: &Tir<'_>,
    r: &Tir<'_>,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| mk_span_err(span.clone(), msg);
    use BinOp::*;
    use NirKind::{ListType, RecordType};

    Ok(match op {
        RightBiasedRecordMerge => {
            let x_type = l.ty();
            let y_type = r.ty();

            // Extract the LHS record type
            let kts_x = match x_type.kind() {
                RecordType(kts) => kts,
                _ => return span_err("MustCombineRecord"),
            };
            // Extract the RHS record type
            let kts_y = match y_type.kind() {
                RecordType(kts) => kts,
                _ => return span_err("MustCombineRecord"),
            };

            // Union the two records, prefering
            // the values found in the RHS.
            let kts = merge_maps(kts_x, kts_y, |_, _, r_t| r_t.clone());

            let u = max(l.ty().ty(), r.ty().ty());
            Nir::from_kind(RecordType(kts)).to_type(u)
        }
        RecursiveRecordMerge => {
            check_rectymerge(&span, env, l.ty().to_nir(), r.ty().to_nir())?;

            let hir = Hir::new(
                HirKind::Expr(ExprKind::Op(OpKind::BinOp(
                    RecursiveRecordTypeMerge,
                    l.ty().to_hir(env.as_varenv()),
                    r.ty().to_hir(env.as_varenv()),
                ))),
                span.clone(),
            );
            let x_u = l.ty().ty();
            let y_u = r.ty().ty();
            Type::new(hir.eval(env), max(x_u, y_u))
        }
        RecursiveRecordTypeMerge => {
            check_rectymerge(&span, env, l.eval(env), r.eval(env))?;

            // A RecordType's type is always a const
            let xk = l.ty().as_const().unwrap();
            let yk = r.ty().as_const().unwrap();
            Type::from_const(max(xk, yk))
        }
        ListAppend => {
            match l.ty().kind() {
                ListType(..) => {}
                _ => return span_err("BinOpTypeMismatch"),
            }

            if l.ty() != r.ty() {
                return span_err("BinOpTypeMismatch");
            }

            l.ty().clone()
        }
        Equivalence => {
            if l.ty() != r.ty() {
                return span_err("EquivalenceTypeMismatch");
            }
            if l.ty().ty().as_const() != Some(Const::Type) {
                return span_err("EquivalenceArgumentsMustBeTerms");
            }

            Type::from_const(Const::Type)
        }
        op => {
            let t = Type::from_builtin(match op {
                BoolAnd | BoolOr | BoolEQ | BoolNE => Builtin::Bool,
                NaturalPlus | NaturalTimes => Builtin::Natural,
                TextAppend => Builtin::Text,
                ListAppend
                | RightBiasedRecordMerge
                | RecursiveRecordMerge
                | RecursiveRecordTypeMerge
                | Equivalence => unreachable!(),
                ImportAlt => unreachable!("ImportAlt leftover in tck"),
            });

            if *l.ty() != t {
                return span_err("BinOpTypeMismatch");
            }

            if *r.ty() != t {
                return span_err("BinOpTypeMismatch");
            }

            t
        }
    })
}

fn typecheck_merge(
    env: &TyEnv,
    span: Span,
    record: &Tir<'_>,
    scrut: &Tir<'_>,
    type_annot: Option<&Tir<'_>>,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| mk_span_err(span.clone(), msg);
    use NirKind::{OptionalType, PiClosure, RecordType, UnionType};

    let record_type = record.ty();
    let handlers = match record_type.kind() {
        RecordType(kts) => kts,
        _ => return span_err("Merge1ArgMustBeRecord"),
    };

    let scrut_type = scrut.ty();
    let variants = match scrut_type.kind() {
        UnionType(kts) => Cow::Borrowed(kts),
        OptionalType(ty) => {
            let mut kts = HashMap::new();
            kts.insert("None".into(), None);
            kts.insert("Some".into(), Some(ty.clone()));
            Cow::Owned(kts)
        }
        _ => return span_err("Merge2ArgMustBeUnionOrOptional"),
    };

    let mut inferred_type = None;
    for (x, handler_type) in handlers {
        let handler_return_type: Type = match variants.get(x) {
            // Union alternative with type
            Some(Some(variant_type)) => match handler_type.kind() {
                PiClosure { closure, annot, .. } => {
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
                                    "the handler for `{}` expects a value of \
                                     type: `{}`",
                                    x,
                                    annot.to_expr_tyenv(env)
                                ),
                            )
                            .span_err(
                                scrut.span(),
                                format!(
                                    "but the corresponding variant has type: \
                                     `{}`",
                                    variant_type.to_expr_tyenv(env)
                                ),
                            )
                            .format(),
                        );
                    }

                    // TODO: this actually doesn't check anything yet
                    match closure.remove_binder() {
                        Ok(v) => Type::new_infer_universe(env, v.clone())?,
                        Err(()) => {
                            return span_err("MergeReturnTypeIsDependent")
                        }
                    }
                }
                _ => {
                    return mkerr(
                        ErrorBuilder::new(format!(
                            "merge handler is not a function"
                        ))
                        .span_err(span, format!("in this merge expression"))
                        .span_err(
                            record.span(),
                            format!(
                                "the handler for `{}` has type: `{}`",
                                x,
                                handler_type.to_expr_tyenv(env)
                            ),
                        )
                        .span_help(
                            scrut.span(),
                            format!(
                                "the corresponding variant has type: `{}`",
                                variant_type.to_expr_tyenv(env)
                            ),
                        )
                        .help(format!(
                            "a handler for this variant must be a function \
                             that takes an input of type: `{}`",
                            variant_type.to_expr_tyenv(env)
                        ))
                        .format(),
                    )
                }
            },
            // Union alternative without type
            Some(None) => Type::new_infer_universe(env, handler_type.clone())?,
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

    let type_annot = type_annot
        .as_ref()
        .map(|t| t.eval_to_type(env))
        .transpose()?;
    Ok(match (inferred_type, type_annot) {
        (Some(t1), Some(t2)) => {
            if t1 != t2 {
                return span_err("MergeAnnotMismatch");
            }
            t1
        }
        (Some(t), None) => t,
        (None, Some(t)) => t,
        (None, None) => return span_err("MergeEmptyNeedsAnnotation"),
    })
}

pub fn typecheck_operation(
    env: &TyEnv,
    span: Span,
    opkind: &OpKind<Tir<'_>>,
) -> Result<Type, TypeError> {
    let span_err = |msg: &str| mk_span_err(span.clone(), msg);
    use NirKind::{ListType, PiClosure, RecordType, UnionType};
    use OpKind::*;

    Ok(match opkind {
        App(f, arg) => {
            match f.ty().kind() {
                // TODO: store Type in closure
                PiClosure { annot, closure, .. } => {
                    if arg.ty().as_nir() != annot {
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
                    Type::new_infer_universe(env, closure.apply(arg_nf))?
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
        BinOp(o, l, r) => typecheck_binop(env, span, *o, l, r)?,
        BoolIf(x, y, z) => {
            if *x.ty().kind() != NirKind::from_builtin(Builtin::Bool) {
                return span_err("InvalidPredicate");
            }
            if y.ty().ty().as_const() != Some(Const::Type) {
                return span_err("IfBranchMustBeTerm");
            }
            if y.ty() != z.ty() {
                return span_err("IfBranchMismatch");
            }

            y.ty().clone()
        }
        Merge(record, scrut, type_annot) => {
            typecheck_merge(env, span, record, scrut, type_annot.as_ref())?
        }
        ToMap(record, annot) => {
            if record.ty().ty().as_const() != Some(Const::Type) {
                return span_err("`toMap` only accepts records of type `Type`");
            }
            let record_t = record.ty();
            let kts = match record_t.kind() {
                RecordType(kts) => kts,
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
                let annot_val = annot.eval_to_type(env)?;

                let err_msg = "The type of `toMap x` must be of the form \
                               `List { mapKey : Text, mapValue : T }`";
                let arg = match annot_val.kind() {
                    ListType(t) => t,
                    _ => return span_err(err_msg),
                };
                let kts = match arg.kind() {
                    RecordType(kts) => kts,
                    _ => return span_err(err_msg),
                };
                if kts.len() != 2 {
                    return span_err(err_msg);
                }
                match kts.get("mapKey") {
                    Some(t) if *t == Nir::from_builtin(Builtin::Text) => {}
                    _ => return span_err(err_msg),
                }
                match kts.get("mapValue") {
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
                kts.insert("mapKey".into(), Nir::from_builtin(Builtin::Text));
                kts.insert("mapValue".into(), entry_type);
                let output_type: Type = Nir::from_builtin(Builtin::List)
                    .app(Nir::from_kind(RecordType(kts)))
                    .to_type(Const::Type);
                if let Some(annot) = annot {
                    let annot_val = annot.eval_to_type(env)?;
                    if output_type != annot_val {
                        return span_err("Annotation mismatch");
                    }
                }
                output_type
            }
        }
        Field(scrut, x) => {
            match scrut.ty().kind() {
                RecordType(kts) => match kts.get(x) {
                    Some(val) => Type::new_infer_universe(env, val.clone())?,
                    None => return span_err("MissingRecordField"),
                },
                NirKind::Const(_) => {
                    let scrut = scrut.eval_to_type(env)?;
                    match scrut.kind() {
                        UnionType(kts) => match kts.get(x) {
                            // Constructor has type T -> < x: T, ... >
                            Some(Some(ty)) => Nir::from_kind(PiClosure {
                                binder: Binder::new(x.clone()),
                                annot: ty.clone(),
                                closure: Closure::new_constant(scrut.to_nir()),
                            })
                            .to_type(scrut.ty()),
                            Some(None) => scrut,
                            None => return span_err("MissingUnionField"),
                        },
                        _ => return span_err("NotARecord"),
                    }
                }
                _ => return span_err("NotARecord"),
            }
        }
        Projection(record, labels) => {
            let record_type = record.ty();
            let kts = match record_type.kind() {
                RecordType(kts) => kts,
                _ => return span_err("ProjectionMustBeRecord"),
            };

            let mut new_kts = HashMap::new();
            for l in labels {
                match kts.get(l) {
                    None => return span_err("ProjectionMissingEntry"),
                    Some(t) => {
                        new_kts.insert(l.clone(), t.clone());
                    }
                };
            }

            Type::new_infer_universe(env, Nir::from_kind(RecordType(new_kts)))?
        }
        ProjectionByExpr(record, selection) => {
            let record_type = record.ty();
            let rec_kts = match record_type.kind() {
                RecordType(kts) => kts,
                _ => return span_err("ProjectionMustBeRecord"),
            };

            let selection_val = selection.eval_to_type(env)?;
            let sel_kts = match selection_val.kind() {
                RecordType(kts) => kts,
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
        Completion(..) | With(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    })
}
