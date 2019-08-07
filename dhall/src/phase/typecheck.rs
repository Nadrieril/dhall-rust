use std::collections::HashMap;

use dhall_proc_macros as dhall;
use dhall_syntax::{
    rc, Builtin, Const, Expr, ExprF, InterpolatedTextContents, Label, Span,
    SubExpr, X,
};

use crate::core::context::{NormalizationContext, TypecheckContext};
use crate::core::thunk::{Thunk, TypeThunk};
use crate::core::value::Value;
use crate::core::var::{Shift, Subst};
use crate::error::{TypeError, TypeMessage};
use crate::phase::{Normalized, Resolved, Type, Typed};

macro_rules! ensure_equal {
    ($x:expr, $y:expr, $err:expr $(,)*) => {
        if $x.to_value() != $y.to_value() {
            return Err($err);
        }
    };
}

// Ensure the provided type has type `Type`
macro_rules! ensure_simple_type {
    ($x:expr, $err:expr $(,)*) => {{
        match $x.get_type()?.as_const() {
            Some(dhall_syntax::Const::Type) => {}
            _ => return Err($err),
        }
    }};
}

fn tck_pi_type(
    ctx: &TypecheckContext,
    x: Label,
    tx: Type,
    te: Type,
) -> Result<Typed, TypeError> {
    use crate::error::TypeMessage::*;
    let ctx2 = ctx.insert_type(&x, tx.clone());

    let ka = match tx.get_type()?.as_const() {
        Some(k) => k,
        _ => {
            return Err(TypeError::new(
                ctx,
                InvalidInputType(tx.to_normalized()),
            ))
        }
    };

    let kb = match te.get_type()?.as_const() {
        Some(k) => k,
        _ => {
            return Err(TypeError::new(
                &ctx2,
                InvalidOutputType(te.get_type()?.to_normalized()),
            ))
        }
    };

    let k = match function_check(ka, kb) {
        Ok(k) => k,
        Err(()) => {
            return Err(TypeError::new(
                ctx,
                NoDependentTypes(
                    tx.to_normalized(),
                    te.get_type()?.to_normalized(),
                ),
            ))
        }
    };

    Ok(Typed::from_thunk_and_type(
        Value::Pi(x.into(), TypeThunk::from_type(tx), TypeThunk::from_type(te))
            .into_thunk(),
        Type::from_const(k),
    ))
}

fn tck_record_type(
    ctx: &TypecheckContext,
    kts: impl IntoIterator<Item = Result<(Label, Type), TypeError>>,
) -> Result<Typed, TypeError> {
    use crate::error::TypeMessage::*;
    use std::collections::hash_map::Entry;
    let mut new_kts = HashMap::new();
    // Check that all types are the same const
    let mut k = None;
    for e in kts {
        let (x, t) = e?;
        match (k, t.get_type()?.as_const()) {
            (None, Some(k2)) => k = Some(k2),
            (Some(k1), Some(k2)) if k1 == k2 => {}
            _ => {
                return Err(TypeError::new(
                    ctx,
                    InvalidFieldType(x.clone(), t.clone()),
                ))
            }
        }
        let entry = new_kts.entry(x.clone());
        match &entry {
            Entry::Occupied(_) => {
                return Err(TypeError::new(ctx, RecordTypeDuplicateField))
            }
            Entry::Vacant(_) => {
                entry.or_insert_with(|| TypeThunk::from_type(t.clone()))
            }
        };
    }
    // An empty record type has type Type
    let k = k.unwrap_or(dhall_syntax::Const::Type);

    Ok(Typed::from_thunk_and_type(
        Value::RecordType(new_kts).into_thunk(),
        Type::from_const(k),
    ))
}

fn tck_union_type(
    ctx: &TypecheckContext,
    kts: impl IntoIterator<Item = Result<(Label, Option<Type>), TypeError>>,
) -> Result<Typed, TypeError> {
    use crate::error::TypeMessage::*;
    use std::collections::hash_map::Entry;
    let mut new_kts = HashMap::new();
    // Check that all types are the same const
    let mut k = None;
    for e in kts {
        let (x, t) = e?;
        if let Some(t) = &t {
            match (k, t.get_type()?.as_const()) {
                (None, Some(k2)) => k = Some(k2),
                (Some(k1), Some(k2)) if k1 == k2 => {}
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        InvalidFieldType(x.clone(), t.clone()),
                    ))
                }
            }
        }
        let entry = new_kts.entry(x.clone());
        match &entry {
            Entry::Occupied(_) => {
                return Err(TypeError::new(ctx, UnionTypeDuplicateField))
            }
            Entry::Vacant(_) => entry.or_insert_with(|| {
                t.as_ref().map(|t| TypeThunk::from_type(t.clone()))
            }),
        };
    }

    // An empty union type has type Type;
    // an union type with only unary variants also has type Type
    let k = k.unwrap_or(dhall_syntax::Const::Type);

    Ok(Typed::from_thunk_and_type(
        Value::UnionType(new_kts).into_thunk(),
        Type::from_const(k),
    ))
}

fn function_check(a: Const, b: Const) -> Result<Const, ()> {
    use dhall_syntax::Const::*;
    match (a, b) {
        (_, Type) => Ok(Type),
        (Kind, Kind) => Ok(Kind),
        (Sort, Sort) => Ok(Sort),
        (Sort, Kind) => Ok(Sort),
        _ => Err(()),
    }
}

pub fn type_of_const(c: Const) -> Result<Type, TypeError> {
    match c {
        Const::Type => Ok(Type::from_const(Const::Kind)),
        Const::Kind => Ok(Type::from_const(Const::Sort)),
        Const::Sort => {
            Err(TypeError::new(&TypecheckContext::new(), TypeMessage::Sort))
        }
    }
}

fn type_of_builtin(b: Builtin) -> Expr<X, X> {
    use dhall_syntax::Builtin::*;
    match b {
        Bool | Natural | Integer | Double | Text => dhall::expr!(Type),
        List | Optional => dhall::expr!(
            Type -> Type
        ),

        NaturalFold => dhall::expr!(
            Natural ->
            forall (natural: Type) ->
            forall (succ: natural -> natural) ->
            forall (zero: natural) ->
            natural
        ),
        NaturalBuild => dhall::expr!(
            (forall (natural: Type) ->
                forall (succ: natural -> natural) ->
                forall (zero: natural) ->
                natural) ->
            Natural
        ),
        NaturalIsZero | NaturalEven | NaturalOdd => dhall::expr!(
            Natural -> Bool
        ),
        NaturalToInteger => dhall::expr!(Natural -> Integer),
        NaturalShow => dhall::expr!(Natural -> Text),

        IntegerToDouble => dhall::expr!(Integer -> Double),
        IntegerShow => dhall::expr!(Integer -> Text),
        DoubleShow => dhall::expr!(Double -> Text),
        TextShow => dhall::expr!(Text -> Text),

        ListBuild => dhall::expr!(
            forall (a: Type) ->
            (forall (list: Type) ->
                forall (cons: a -> list -> list) ->
                forall (nil: list) ->
                list) ->
            List a
        ),
        ListFold => dhall::expr!(
            forall (a: Type) ->
            List a ->
            forall (list: Type) ->
            forall (cons: a -> list -> list) ->
            forall (nil: list) ->
            list
        ),
        ListLength => dhall::expr!(forall (a: Type) -> List a -> Natural),
        ListHead | ListLast => {
            dhall::expr!(forall (a: Type) -> List a -> Optional a)
        }
        ListIndexed => dhall::expr!(
            forall (a: Type) ->
            List a ->
            List { index: Natural, value: a }
        ),
        ListReverse => dhall::expr!(
            forall (a: Type) -> List a -> List a
        ),

        OptionalBuild => dhall::expr!(
            forall (a: Type) ->
            (forall (optional: Type) ->
                forall (just: a -> optional) ->
                forall (nothing: optional) ->
                optional) ->
            Optional a
        ),
        OptionalFold => dhall::expr!(
            forall (a: Type) ->
            Optional a ->
            forall (optional: Type) ->
            forall (just: a -> optional) ->
            forall (nothing: optional) ->
            optional
        ),
        OptionalNone => dhall::expr!(
            forall (a: Type) -> Optional a
        ),
    }
}

/// Takes an expression that is meant to contain a Type
/// and turn it into a type, typechecking it along the way.
pub fn mktype(
    ctx: &TypecheckContext,
    e: SubExpr<Span, Normalized>,
) -> Result<Type, TypeError> {
    Ok(type_with(ctx, e)?.to_type())
}

pub fn builtin_to_type(b: Builtin) -> Result<Type, TypeError> {
    mktype(&TypecheckContext::new(), SubExpr::from_builtin(b))
}

/// Intermediary return type
enum Ret {
    /// Returns the contained value as is
    RetWhole(Typed),
    /// Use the contained Type as the type of the input expression
    RetTypeOnly(Type),
}

/// Type-check an expression and return the expression alongside its type if type-checking
/// succeeded, or an error if type-checking failed.
/// Some normalization is done while typechecking, so the returned expression might be partially
/// normalized as well.
fn type_with(
    ctx: &TypecheckContext,
    e: SubExpr<Span, Normalized>,
) -> Result<Typed, TypeError> {
    use dhall_syntax::ExprF::{Annot, Embed, Lam, Let, Pi, Var};

    use Ret::*;
    Ok(match e.as_ref() {
        Lam(x, t, b) => {
            let tx = mktype(ctx, t.clone())?;
            let ctx2 = ctx.insert_type(x, tx.clone());
            let b = type_with(&ctx2, b.clone())?;
            let v = Value::Lam(
                x.clone().into(),
                TypeThunk::from_type(tx.clone()),
                b.to_thunk(),
            );
            let tb = b.get_type()?.into_owned();
            let t = tck_pi_type(ctx, x.clone(), tx, tb)?.to_type();
            Typed::from_thunk_and_type(Thunk::from_value(v), t)
        }
        Pi(x, ta, tb) => {
            let ta = mktype(ctx, ta.clone())?;
            let ctx2 = ctx.insert_type(x, ta.clone());
            let tb = mktype(&ctx2, tb.clone())?;
            return tck_pi_type(ctx, x.clone(), ta, tb);
        }
        Let(x, t, v, e) => {
            let v = if let Some(t) = t {
                t.rewrap(Annot(v.clone(), t.clone()))
            } else {
                v.clone()
            };

            let v = type_with(ctx, v)?;
            return type_with(&ctx.insert_value(x, v.clone())?, e.clone());
        }
        Embed(p) => p.clone().into_typed(),
        Var(var) => match ctx.lookup(&var) {
            Some(typed) => typed,
            None => {
                return Err(TypeError::new(
                    ctx,
                    TypeMessage::UnboundVariable(var.clone()),
                ))
            }
        },
        _ => {
            // Typecheck recursively all subexpressions
            let expr =
                e.as_ref().traverse_ref_with_special_handling_of_binders(
                    |e| type_with(ctx, e.clone()),
                    |_, _| unreachable!(),
                    |_| unreachable!(),
                )?;
            let ret = type_last_layer(ctx, &expr)?;
            match ret {
                RetTypeOnly(typ) => {
                    let expr = expr.map_ref_simple(|typed| typed.to_thunk());
                    Typed::from_thunk_and_type(
                        Thunk::from_partial_expr(expr),
                        typ,
                    )
                }
                RetWhole(tt) => tt,
            }
        }
    })
}

/// When all sub-expressions have been typed, check the remaining toplevel
/// layer.
fn type_last_layer(
    ctx: &TypecheckContext,
    e: &ExprF<Typed, X>,
) -> Result<Ret, TypeError> {
    use crate::error::TypeMessage::*;
    use dhall_syntax::BinOp::*;
    use dhall_syntax::Builtin::*;
    use dhall_syntax::ExprF::*;
    use Ret::*;
    let mkerr = |msg: TypeMessage| TypeError::new(ctx, msg);

    match e {
        Lam(_, _, _) | Pi(_, _, _) | Let(_, _, _, _) | Embed(_) | Var(_) => {
            unreachable!()
        }
        App(f, a) => {
            let tf = f.get_type()?;
            let (x, tx, tb) = match &tf.to_value() {
                Value::Pi(x, tx, tb) => (x.clone(), tx.to_type(), tb.to_type()),
                _ => return Err(mkerr(NotAFunction(f.clone()))),
            };
            ensure_equal!(a.get_type()?, &tx, {
                mkerr(TypeMismatch(f.clone(), tx.to_normalized(), a.clone()))
            });

            Ok(RetTypeOnly(tb.subst_shift(&x.into(), &a)))
        }
        Annot(x, t) => {
            let t = t.to_type();
            ensure_equal!(
                &t,
                x.get_type()?,
                mkerr(AnnotMismatch(x.clone(), t.to_normalized()))
            );
            Ok(RetTypeOnly(x.get_type()?.into_owned()))
        }
        BoolIf(x, y, z) => {
            ensure_equal!(
                x.get_type()?,
                &builtin_to_type(Bool)?,
                mkerr(InvalidPredicate(x.clone())),
            );

            ensure_simple_type!(
                y.get_type()?,
                mkerr(IfBranchMustBeTerm(true, y.clone())),
            );

            ensure_simple_type!(
                z.get_type()?,
                mkerr(IfBranchMustBeTerm(false, z.clone())),
            );

            ensure_equal!(
                y.get_type()?,
                z.get_type()?,
                mkerr(IfBranchMismatch(y.clone(), z.clone()))
            );

            Ok(RetTypeOnly(y.get_type()?.into_owned()))
        }
        EmptyListLit(t) => {
            let t = t.to_type();
            match &t.to_value() {
                Value::AppliedBuiltin(dhall_syntax::Builtin::List, args)
                    if args.len() == 1 => {}
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        InvalidListType(t.to_normalized()),
                    ))
                }
            }
            Ok(RetTypeOnly(t))
        }
        NEListLit(xs) => {
            let mut iter = xs.iter().enumerate();
            let (_, x) = iter.next().unwrap();
            for (i, y) in iter {
                ensure_equal!(
                    x.get_type()?,
                    y.get_type()?,
                    mkerr(InvalidListElement(
                        i,
                        x.get_type()?.to_normalized(),
                        y.clone()
                    ))
                );
            }
            let t = x.get_type()?;
            ensure_simple_type!(
                t,
                TypeError::new(ctx, InvalidListType(t.to_normalized())),
            );

            Ok(RetTypeOnly(
                Typed::from_thunk_and_type(
                    Value::from_builtin(dhall_syntax::Builtin::List)
                        .app(t.to_value())
                        .into_thunk(),
                    Type::from_const(dhall_syntax::Const::Type),
                )
                .to_type(),
            ))
        }
        SomeLit(x) => {
            let t = x.get_type()?.into_owned();
            ensure_simple_type!(
                t,
                TypeError::new(ctx, InvalidOptionalType(t.to_normalized())),
            );

            Ok(RetTypeOnly(
                Typed::from_thunk_and_type(
                    Value::from_builtin(dhall_syntax::Builtin::Optional)
                        .app(t.to_value())
                        .into_thunk(),
                    Type::from_const(dhall_syntax::Const::Type),
                )
                .to_type(),
            ))
        }
        RecordType(kts) => Ok(RetWhole(tck_record_type(
            ctx,
            kts.iter().map(|(x, t)| Ok((x.clone(), t.to_type()))),
        )?)),
        UnionType(kts) => Ok(RetWhole(tck_union_type(
            ctx,
            kts.iter()
                .map(|(x, t)| Ok((x.clone(), t.as_ref().map(|t| t.to_type())))),
        )?)),
        RecordLit(kvs) => Ok(RetTypeOnly(
            tck_record_type(
                ctx,
                kvs.iter()
                    .map(|(x, v)| Ok((x.clone(), v.get_type()?.into_owned()))),
            )?
            .into_type(),
        )),
        Field(r, x) => {
            match &r.get_type()?.to_value() {
                Value::RecordType(kts) => match kts.get(&x) {
                    Some(tth) => {
                        Ok(RetTypeOnly(tth.to_type()))
                    },
                    None => Err(mkerr(MissingRecordField(x.clone(),
                                        r.clone()))),
                },
                // TODO: branch here only when r.get_type() is a Const
                _ => {
                    let r = r.to_type();
                    match &r.to_value() {
                        Value::UnionType(kts) => match kts.get(&x) {
                            // Constructor has type T -> < x: T, ... >
                            Some(Some(t)) => {
                                // TODO: avoid capture
                                Ok(RetTypeOnly(
                                    tck_pi_type(
                                        ctx,
                                        "_".into(),
                                        t.to_type(),
                                        r.clone(),
                                    )?.to_type()
                                ))
                            },
                            Some(None) => {
                                Ok(RetTypeOnly(r.clone()))
                            },
                            None => {
                                Err(mkerr(MissingUnionField(
                                    x.clone(),
                                    r.to_normalized(),
                                )))
                            },
                        },
                        _ => {
                            Err(mkerr(NotARecord(
                                x.clone(),
                                r.to_normalized()
                            )))
                        },
                    }
                }
                // _ => Err(mkerr(NotARecord(
                //     x,
                //     r.to_type()?.to_normalized(),
                // ))),
            }
        }
        Const(c) => Ok(RetWhole(Typed::from_const(*c))),
        Builtin(b) => {
            Ok(RetTypeOnly(mktype(ctx, rc(type_of_builtin(*b)).absurd())?))
        }
        BoolLit(_) => Ok(RetTypeOnly(builtin_to_type(Bool)?)),
        NaturalLit(_) => Ok(RetTypeOnly(builtin_to_type(Natural)?)),
        IntegerLit(_) => Ok(RetTypeOnly(builtin_to_type(Integer)?)),
        DoubleLit(_) => Ok(RetTypeOnly(builtin_to_type(Double)?)),
        TextLit(interpolated) => {
            let text_type = builtin_to_type(Text)?;
            for contents in interpolated.iter() {
                use InterpolatedTextContents::Expr;
                if let Expr(x) = contents {
                    ensure_equal!(
                        x.get_type()?,
                        &text_type,
                        mkerr(InvalidTextInterpolation(x.clone())),
                    );
                }
            }
            Ok(RetTypeOnly(text_type))
        }
        BinOp(RightBiasedRecordMerge, l, r) => {
            use crate::phase::normalize::merge_maps;

            let l_type = l.get_type()?;
            let l_kind = l_type.get_type()?;
            let r_type = r.get_type()?;
            let r_kind = r_type.get_type()?;

            // Check the equality of kinds.
            // This is to disallow expression such as:
            // "{ x = Text } // { y = 1 }"
            ensure_equal!(
                l_kind,
                r_kind,
                mkerr(RecordMismatch(l.clone(), r.clone())),
            );

            // Extract the LHS record type
            let kts_x = match l_type.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(MustCombineRecord(l.clone()))),
            };

            // Extract the RHS record type
            let kts_y = match r_type.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(MustCombineRecord(r.clone()))),
            };

            // Union the two records, prefering
            // the values found in the RHS.
            let kts = merge_maps(&kts_x, &kts_y, |_, r_t| r_t.clone());

            // Construct the final record type from the union
            Ok(RetTypeOnly(
                tck_record_type(
                    ctx,
                    kts.iter().map(|(x, v)| Ok((x.clone(), v.to_type()))),
                )?
                .into_type(),
            ))
        }
        BinOp(RecursiveRecordMerge, l, r) => {
            // A recursive function to dig down into
            // records of records when merging.
            fn combine_record_types(
                ctx: &TypecheckContext,
                kts_l: HashMap<Label, TypeThunk>,
                kts_r: HashMap<Label, TypeThunk>,
            ) -> Result<Typed, TypeError> {
                use crate::phase::normalize::outer_join;

                // If the Label exists for both records and Type for the values
                // are records themselves, then we hit the recursive case.
                // Otherwise we have a field collision.
                let combine = |k: &Label,
                               inner_l: &TypeThunk,
                               inner_r: &TypeThunk|
                 -> Result<Typed, TypeError> {
                    match (inner_l.to_value(), inner_r.to_value()) {
                        (
                            Value::RecordType(inner_l_kvs),
                            Value::RecordType(inner_r_kvs),
                        ) => {
                            combine_record_types(ctx, inner_l_kvs, inner_r_kvs)
                        }
                        (_, _) => {
                            Err(TypeError::new(ctx, FieldCollision(k.clone())))
                        }
                    }
                };

                let kts: HashMap<Label, Result<Typed, TypeError>> = outer_join(
                    |l| Ok(l.to_type()),
                    |r| Ok(r.to_type()),
                    |k: &Label, l: &TypeThunk, r: &TypeThunk| combine(k, l, r),
                    &kts_l,
                    &kts_r,
                );

                Ok(tck_record_type(
                    ctx,
                    kts.into_iter().map(|(x, v)| v.map(|r| (x.clone(), r))),
                )?
                .into_type())
            };

            let l_type = l.get_type()?;
            let l_kind = l_type.get_type()?;
            let r_type = r.get_type()?;
            let r_kind = r_type.get_type()?;

            // Check the equality of kinds.
            // This is to disallow expression such as:
            // "{ x = Text } // { y = 1 }"
            ensure_equal!(
                l_kind,
                r_kind,
                mkerr(RecordMismatch(l.clone(), r.clone())),
            );

            // Extract the LHS record type
            let kts_x = match l_type.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(MustCombineRecord(l.clone()))),
            };

            // Extract the RHS record type
            let kts_y = match r_type.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(MustCombineRecord(r.clone()))),
            };

            combine_record_types(ctx, kts_x, kts_y).map(|r| RetTypeOnly(r))
        }
        BinOp(RecursiveRecordTypeMerge, l, r) => {
            // A recursive function to dig down into
            // records of records when merging.
            fn combine_record_types(
                ctx: &TypecheckContext,
                kts_l: HashMap<Label, TypeThunk>,
                kts_r: HashMap<Label, TypeThunk>,
            ) -> Result<Typed, TypeError> {
                use crate::phase::normalize::intersection_with_key;

                // If the Label exists for both records and Type for the values
                // are records themselves, then we hit the recursive case.
                // Otherwise we have a field collision.
                let combine = |k: &Label,
                               kts_l_inner: &TypeThunk,
                               kts_r_inner: &TypeThunk|
                 -> Result<Typed, TypeError> {
                    match (kts_l_inner.to_value(), kts_r_inner.to_value()) {
                        (
                            Value::RecordType(kvs_l_inner),
                            Value::RecordType(kvs_r_inner),
                        ) => {
                            combine_record_types(ctx, kvs_l_inner, kvs_r_inner)
                        }
                        (_, _) => {
                            Err(TypeError::new(ctx, FieldCollision(k.clone())))
                        }
                    }
                };

                let kts = intersection_with_key(
                    |k: &Label, l: &TypeThunk, r: &TypeThunk| combine(k, l, r),
                    &kts_l,
                    &kts_r,
                );

                Ok(tck_record_type(
                    ctx,
                    kts.into_iter().map(|(x, v)| v.map(|r| (x.clone(), r))),
                )?
                .into_type())
            };

            // Extract the Const of the LHS
            let k_l = match l.get_type()?.to_value() {
                Value::Const(k) => k,
                _ => {
                    return Err(mkerr(RecordTypeMergeRequiresRecordType(
                        l.clone(),
                    )))
                }
            };

            // Extract the Const of the RHS
            let k_r = match r.get_type()?.to_value() {
                Value::Const(k) => k,
                _ => {
                    return Err(mkerr(RecordTypeMergeRequiresRecordType(
                        r.clone(),
                    )))
                }
            };

            // Const values must match for the Records
            let k = if k_l == k_r {
                k_l
            } else {
                return Err(mkerr(RecordTypeMismatch(
                    Typed::from_const(k_l),
                    Typed::from_const(k_r),
                    l.clone(),
                    r.clone(),
                )));
            };

            // Extract the LHS record type
            let kts_x = match l.to_value() {
                Value::RecordType(kts) => kts,
                _ => {
                    return Err(mkerr(RecordTypeMergeRequiresRecordType(
                        l.clone(),
                    )))
                }
            };

            // Extract the RHS record type
            let kts_y = match r.to_value() {
                Value::RecordType(kts) => kts,
                _ => {
                    return Err(mkerr(RecordTypeMergeRequiresRecordType(
                        r.clone(),
                    )))
                }
            };

            // Ensure that the records combine without a type error
            // and if not output the final Const value.
            combine_record_types(ctx, kts_x, kts_y)
                .and(Ok(RetTypeOnly(Typed::from_const(k))))
        }
        BinOp(o @ ListAppend, l, r) => {
            match l.get_type()?.to_value() {
                Value::AppliedBuiltin(List, _) => {}
                _ => return Err(mkerr(BinOpTypeMismatch(*o, l.clone()))),
            }

            ensure_equal!(
                l.get_type()?,
                r.get_type()?,
                mkerr(BinOpTypeMismatch(*o, r.clone()))
            );

            Ok(RetTypeOnly(l.get_type()?.into_owned()))
        }
        BinOp(o, l, r) => {
            let t = builtin_to_type(match o {
                BoolAnd => Bool,
                BoolOr => Bool,
                BoolEQ => Bool,
                BoolNE => Bool,
                NaturalPlus => Natural,
                NaturalTimes => Natural,
                TextAppend => Text,
                ListAppend => unreachable!(),
                RightBiasedRecordMerge => unreachable!(),
                RecursiveRecordMerge => unreachable!(),
                RecursiveRecordTypeMerge => unreachable!(),
                ImportAlt => unreachable!("There should remain no import alternatives in a resolved expression"),
            })?;

            ensure_equal!(
                l.get_type()?,
                &t,
                mkerr(BinOpTypeMismatch(*o, l.clone()))
            );

            ensure_equal!(
                r.get_type()?,
                &t,
                mkerr(BinOpTypeMismatch(*o, r.clone()))
            );

            Ok(RetTypeOnly(t))
        }
        Merge(record, union, type_annot) => {
            let handlers = match record.get_type()?.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(Merge1ArgMustBeRecord(record.clone()))),
            };

            let variants = match union.get_type()?.to_value() {
                Value::UnionType(kts) => kts,
                _ => return Err(mkerr(Merge2ArgMustBeUnion(union.clone()))),
            };

            let mut inferred_type = None;
            for (x, handler) in handlers.iter() {
                let handler_return_type = match variants.get(x) {
                    // Union alternative with type
                    Some(Some(variant_type)) => {
                        let variant_type = variant_type.to_type();
                        let handler_type = handler.to_type();
                        let (x, tx, tb) = match &handler_type.to_value() {
                            Value::Pi(x, tx, tb) => {
                                (x.clone(), tx.to_type(), tb.to_type())
                            }
                            _ => return Err(mkerr(NotAFunction(handler_type))),
                        };

                        ensure_equal!(&variant_type, &tx, {
                            mkerr(TypeMismatch(
                                handler_type,
                                tx.to_normalized(),
                                variant_type,
                            ))
                        });

                        // Extract `tb` from under the `x` binder. Fails is `x` was free in `tb`.
                        match tb.over_binder(x) {
                            Some(x) => x,
                            None => {
                                return Err(mkerr(
                                    MergeHandlerReturnTypeMustNotBeDependent,
                                ))
                            }
                        }
                    }
                    // Union alternative without type
                    Some(None) => handler.to_type(),
                    None => {
                        return Err(mkerr(MergeHandlerMissingVariant(
                            x.clone(),
                        )))
                    }
                };
                match &inferred_type {
                    None => inferred_type = Some(handler_return_type),
                    Some(t) => {
                        ensure_equal!(
                            t,
                            &handler_return_type,
                            mkerr(MergeHandlerTypeMismatch)
                        );
                    }
                }
            }
            for x in variants.keys() {
                if !handlers.contains_key(x) {
                    return Err(mkerr(MergeVariantMissingHandler(x.clone())));
                }
            }

            match (inferred_type, type_annot) {
                (Some(ref t1), Some(t2)) => {
                    let t2 = t2.to_type();
                    ensure_equal!(t1, &t2, mkerr(MergeAnnotMismatch));
                    Ok(RetTypeOnly(t2))
                }
                (Some(t), None) => Ok(RetTypeOnly(t)),
                (None, Some(t)) => Ok(RetTypeOnly(t.to_type())),
                (None, None) => Err(mkerr(MergeEmptyNeedsAnnotation)),
            }
        }
        Projection(record, labels) => {
            let trecord = record.get_type()?;
            let kts = match trecord.to_value() {
                Value::RecordType(kts) => kts,
                _ => return Err(mkerr(ProjectionMustBeRecord)),
            };

            let mut new_kts = HashMap::new();
            for l in labels {
                match kts.get(l) {
                    None => return Err(mkerr(ProjectionMissingEntry)),
                    Some(t) => new_kts.insert(l.clone(), t.clone()),
                };
            }

            Ok(RetTypeOnly(
                Typed::from_thunk_and_type(
                    Value::RecordType(new_kts).into_thunk(),
                    trecord.get_type()?.into_owned(),
                )
                .to_type(),
            ))
        }
    }
}

/// `typeOf` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
fn type_of(e: SubExpr<Span, Normalized>) -> Result<Typed, TypeError> {
    let ctx = TypecheckContext::new();
    let e = type_with(&ctx, e)?;
    // Ensure `e` has a type (i.e. `e` is not `Sort`)
    e.get_type()?;
    Ok(e)
}

pub fn typecheck(e: Resolved) -> Result<Typed, TypeError> {
    type_of(e.0)
}

pub fn typecheck_with(e: Resolved, ty: &Type) -> Result<Typed, TypeError> {
    let expr: SubExpr<_, _> = e.0;
    let ty: SubExpr<_, _> = ty.to_expr().absurd();
    type_of(expr.rewrap(ExprF::Annot(expr.clone(), ty)))
}
pub fn skip_typecheck(e: Resolved) -> Typed {
    Typed::from_thunk_untyped(Thunk::new(NormalizationContext::new(), e.0))
}
