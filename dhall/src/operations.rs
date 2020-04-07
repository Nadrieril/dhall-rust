use itertools::Itertools;
use std::borrow::Cow;
use std::cmp::max;
use std::collections::{BTreeSet, HashMap};
use std::iter::once;

use crate::builtins::Builtin;
use crate::error::{ErrorBuilder, TypeError};
use crate::semantics::{
    merge_maps, mk_span_err, mkerr, ret_kind, ret_op, ret_ref, Binder, Closure,
    Hir, HirKind, Nir, NirKind, Ret, TextLit, Tir, TyEnv, Type,
};
use crate::syntax::{trivial_result, Const, ExprKind, Label, NumKind, Span};

// Definition order must match precedence order for
// pretty-printing to work correctly
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    /// `x ? y`
    ImportAlt,
    /// `x || y`
    BoolOr,
    /// `x + y`
    NaturalPlus,
    /// `x ++ y`
    TextAppend,
    /// `x # y`
    ListAppend,
    /// `x && y`
    BoolAnd,
    /// `x ∧ y`
    RecursiveRecordMerge,
    /// `x ⫽ y`
    RightBiasedRecordMerge,
    /// `x ⩓ y`
    RecursiveRecordTypeMerge,
    /// `x * y`
    NaturalTimes,
    /// `x == y`
    BoolEQ,
    /// `x != y`
    BoolNE,
    /// x === y
    Equivalence,
}

/// Operations
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpKind<SubExpr> {
    ///  `f a`
    App(SubExpr, SubExpr),
    /// Binary operations
    BinOp(BinOp, SubExpr, SubExpr),
    ///  `if x then y else z`
    BoolIf(SubExpr, SubExpr, SubExpr),
    ///  `merge x y : t`
    Merge(SubExpr, SubExpr, Option<SubExpr>),
    ///  `toMap x : t`
    ToMap(SubExpr, Option<SubExpr>),
    ///  `e.x`
    Field(SubExpr, Label),
    ///  `e.{ x, y, z }`
    Projection(SubExpr, BTreeSet<Label>),
    ///  `e.(t)`
    ProjectionByExpr(SubExpr, SubExpr),
    ///  `x::y`
    Completion(SubExpr, SubExpr),
}

impl<SE> OpKind<SE> {
    pub fn traverse_ref<'a, SE2, Err>(
        &'a self,
        mut f: impl FnMut(&'a SE) -> Result<SE2, Err>,
    ) -> Result<OpKind<SE2>, Err> {
        // Can't use closures because of borrowing rules
        macro_rules! expr {
            ($e:expr) => {
                f($e)?
            };
        }
        macro_rules! opt {
            ($e:expr) => {
                $e.as_ref().map(|e| Ok(expr!(e))).transpose()?
            };
        }

        use OpKind::*;
        Ok(match self {
            App(f, a) => App(expr!(f), expr!(a)),
            BinOp(o, x, y) => BinOp(*o, expr!(x), expr!(y)),
            BoolIf(b, t, f) => BoolIf(expr!(b), expr!(t), expr!(f)),
            Merge(x, y, t) => Merge(expr!(x), expr!(y), opt!(t)),
            ToMap(x, t) => ToMap(expr!(x), opt!(t)),
            Field(e, l) => Field(expr!(e), l.clone()),
            Projection(e, ls) => Projection(expr!(e), ls.clone()),
            ProjectionByExpr(e, x) => ProjectionByExpr(expr!(e), expr!(x)),
            Completion(e, x) => Completion(expr!(e), expr!(x)),
        })
    }

    pub fn map_ref<'a, SE2>(
        &'a self,
        mut f: impl FnMut(&'a SE) -> SE2,
    ) -> OpKind<SE2> {
        trivial_result(self.traverse_ref(|x| Ok(f(x))))
    }
}

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
                match kts.get(&"mapKey".into()) {
                    Some(t) if *t == Nir::from_builtin(Builtin::Text) => {}
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
                RecordType(kts) => match kts.get(&x) {
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
        Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    })
}

fn normalize_binop(o: BinOp, x: &Nir, y: &Nir) -> Ret {
    use BinOp::*;
    use NirKind::{EmptyListLit, NEListLit, Num, RecordLit, RecordType};
    use NumKind::{Bool, Natural};

    match (o, x.kind(), y.kind()) {
        (BoolAnd, Num(Bool(true)), _) => ret_ref(y),
        (BoolAnd, _, Num(Bool(true))) => ret_ref(x),
        (BoolAnd, Num(Bool(false)), _) => ret_kind(Num(Bool(false))),
        (BoolAnd, _, Num(Bool(false))) => ret_kind(Num(Bool(false))),
        (BoolAnd, _, _) if x == y => ret_ref(x),
        (BoolOr, Num(Bool(true)), _) => ret_kind(Num(Bool(true))),
        (BoolOr, _, Num(Bool(true))) => ret_kind(Num(Bool(true))),
        (BoolOr, Num(Bool(false)), _) => ret_ref(y),
        (BoolOr, _, Num(Bool(false))) => ret_ref(x),
        (BoolOr, _, _) if x == y => ret_ref(x),
        (BoolEQ, Num(Bool(true)), _) => ret_ref(y),
        (BoolEQ, _, Num(Bool(true))) => ret_ref(x),
        (BoolEQ, Num(Bool(x)), Num(Bool(y))) => ret_kind(Num(Bool(x == y))),
        (BoolEQ, _, _) if x == y => ret_kind(Num(Bool(true))),
        (BoolNE, Num(Bool(false)), _) => ret_ref(y),
        (BoolNE, _, Num(Bool(false))) => ret_ref(x),
        (BoolNE, Num(Bool(x)), Num(Bool(y))) => ret_kind(Num(Bool(x != y))),
        (BoolNE, _, _) if x == y => ret_kind(Num(Bool(false))),

        (NaturalPlus, Num(Natural(0)), _) => ret_ref(y),
        (NaturalPlus, _, Num(Natural(0))) => ret_ref(x),
        (NaturalPlus, Num(Natural(x)), Num(Natural(y))) => {
            ret_kind(Num(Natural(x + y)))
        }
        (NaturalTimes, Num(Natural(0)), _) => ret_kind(Num(Natural(0))),
        (NaturalTimes, _, Num(Natural(0))) => ret_kind(Num(Natural(0))),
        (NaturalTimes, Num(Natural(1)), _) => ret_ref(y),
        (NaturalTimes, _, Num(Natural(1))) => ret_ref(x),
        (NaturalTimes, Num(Natural(x)), Num(Natural(y))) => {
            ret_kind(Num(Natural(x * y)))
        }

        (ListAppend, EmptyListLit(_), _) => ret_ref(y),
        (ListAppend, _, EmptyListLit(_)) => ret_ref(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => {
            ret_kind(NEListLit(xs.iter().chain(ys.iter()).cloned().collect()))
        }

        (TextAppend, NirKind::TextLit(x), _) if x.is_empty() => ret_ref(y),
        (TextAppend, _, NirKind::TextLit(y)) if y.is_empty() => ret_ref(x),
        (TextAppend, NirKind::TextLit(x), NirKind::TextLit(y)) => {
            ret_kind(NirKind::TextLit(x.concat(y)))
        }
        (TextAppend, NirKind::TextLit(x), _) => ret_kind(NirKind::TextLit(
            x.concat(&TextLit::interpolate(y.clone())),
        )),
        (TextAppend, _, NirKind::TextLit(y)) => ret_kind(NirKind::TextLit(
            TextLit::interpolate(x.clone()).concat(y),
        )),

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            ret_ref(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            ret_ref(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            ret_kind(RecordLit(kvs))
        }
        (RightBiasedRecordMerge, _, _) if x == y => ret_ref(y),

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            ret_ref(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            ret_ref(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |_, v1, v2| {
                Nir::from_partial_expr(ExprKind::Op(OpKind::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                )))
            });
            ret_kind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, RecordType(kts_x), RecordType(kts_y)) => {
            let kts = merge_maps(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Nir, r: &Nir| {
                    Nir::from_partial_expr(ExprKind::Op(OpKind::BinOp(
                        RecursiveRecordTypeMerge,
                        l.clone(),
                        r.clone(),
                    )))
                },
            );
            ret_kind(RecordType(kts))
        }

        (Equivalence, _, _) => {
            ret_kind(NirKind::Equivalence(x.clone(), y.clone()))
        }

        _ => ret_op(OpKind::BinOp(o, x.clone(), y.clone())),
    }
}

fn normalize_field(v: &Nir, field: &Label) -> Ret {
    use self::BinOp::{RecursiveRecordMerge, RightBiasedRecordMerge};
    use NirKind::{Op, RecordLit, UnionConstructor, UnionType};
    use OpKind::{BinOp, Field, Projection};
    let nothing_to_do = || ret_op(Field(v.clone(), field.clone()));

    match v.kind() {
        RecordLit(kvs) => match kvs.get(field) {
            Some(r) => ret_ref(r),
            None => nothing_to_do(),
        },
        UnionType(kts) => {
            ret_kind(UnionConstructor(field.clone(), kts.clone()))
        }
        Op(Projection(x, _)) => normalize_field(x, field),
        Op(BinOp(RightBiasedRecordMerge, x, y)) => match (x.kind(), y.kind()) {
            (_, RecordLit(kvs)) => match kvs.get(field) {
                Some(r) => ret_ref(r),
                None => normalize_field(x, field),
            },
            (RecordLit(kvs), _) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RightBiasedRecordMerge,
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                        y.clone(),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(y, field),
            },
            _ => nothing_to_do(),
        },
        Op(BinOp(RecursiveRecordMerge, x, y)) => match (x.kind(), y.kind()) {
            (RecordLit(kvs), _) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RecursiveRecordMerge,
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                        y.clone(),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(y, field),
            },
            (_, RecordLit(kvs)) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RecursiveRecordMerge,
                        x.clone(),
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(x, field),
            },
            _ => nothing_to_do(),
        },
        _ => nothing_to_do(),
    }
}

pub fn normalize_operation(opkind: &OpKind<Nir>) -> Ret {
    use self::BinOp::RightBiasedRecordMerge;
    use NirKind::{
        EmptyListLit, EmptyOptionalLit, NEListLit, NEOptionalLit, Num, Op,
        RecordLit, RecordType, UnionConstructor, UnionLit,
    };
    use NumKind::Bool;
    use OpKind::*;
    let nothing_to_do = || ret_op(opkind.clone());

    match opkind {
        App(v, a) => ret_kind(v.app_to_kind(a.clone())),
        BinOp(o, x, y) => normalize_binop(*o, x, y),
        BoolIf(b, e1, e2) => {
            match b.kind() {
                Num(Bool(true)) => ret_ref(e1),
                Num(Bool(false)) => ret_ref(e2),
                _ => {
                    match (e1.kind(), e2.kind()) {
                        // Simplify `if b then True else False`
                        (Num(Bool(true)), Num(Bool(false))) => ret_ref(b),
                        _ if e1 == e2 => ret_ref(e1),
                        _ => nothing_to_do(),
                    }
                }
            }
        }
        Merge(handlers, variant, _) => match handlers.kind() {
            RecordLit(kvs) => match variant.kind() {
                UnionConstructor(l, _) => match kvs.get(l) {
                    Some(h) => ret_ref(h),
                    None => nothing_to_do(),
                },
                UnionLit(l, v, _) => match kvs.get(l) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => nothing_to_do(),
                },
                EmptyOptionalLit(_) => match kvs.get(&"None".into()) {
                    Some(h) => ret_ref(h),
                    None => nothing_to_do(),
                },
                NEOptionalLit(v) => match kvs.get(&"Some".into()) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => nothing_to_do(),
                },
                _ => nothing_to_do(),
            },
            _ => nothing_to_do(),
        },
        ToMap(v, annot) => match v.kind() {
            RecordLit(kvs) if kvs.is_empty() => {
                match annot.as_ref().map(|v| v.kind()) {
                    Some(NirKind::ListType(t)) => {
                        ret_kind(EmptyListLit(t.clone()))
                    }
                    _ => nothing_to_do(),
                }
            }
            RecordLit(kvs) => ret_kind(NEListLit(
                kvs.iter()
                    .sorted_by_key(|(k, _)| *k)
                    .map(|(k, v)| {
                        let mut rec = HashMap::new();
                        rec.insert("mapKey".into(), Nir::from_text(k));
                        rec.insert("mapValue".into(), v.clone());
                        Nir::from_kind(NirKind::RecordLit(rec))
                    })
                    .collect(),
            )),
            _ => nothing_to_do(),
        },
        Field(v, field) => normalize_field(v, field),
        Projection(_, ls) if ls.is_empty() => {
            ret_kind(RecordLit(HashMap::new()))
        }
        Projection(v, ls) => match v.kind() {
            RecordLit(kvs) => ret_kind(RecordLit(
                ls.iter()
                    .filter_map(|l| kvs.get(l).map(|x| (l.clone(), x.clone())))
                    .collect(),
            )),
            Op(Projection(v2, _)) => {
                normalize_operation(&Projection(v2.clone(), ls.clone()))
            }
            Op(BinOp(RightBiasedRecordMerge, l, r)) => match r.kind() {
                RecordLit(kvs) => {
                    let r_keys = kvs.keys().cloned().collect();
                    normalize_operation(&BinOp(
                        RightBiasedRecordMerge,
                        Nir::from_partial_expr(ExprKind::Op(Projection(
                            l.clone(),
                            ls.difference(&r_keys).cloned().collect(),
                        ))),
                        Nir::from_partial_expr(ExprKind::Op(Projection(
                            r.clone(),
                            ls.intersection(&r_keys).cloned().collect(),
                        ))),
                    ))
                }
                _ => nothing_to_do(),
            },
            _ => nothing_to_do(),
        },
        ProjectionByExpr(v, t) => match t.kind() {
            RecordType(kts) => normalize_operation(&Projection(
                v.clone(),
                kts.keys().cloned().collect(),
            )),
            _ => nothing_to_do(),
        },
        Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    }
}
