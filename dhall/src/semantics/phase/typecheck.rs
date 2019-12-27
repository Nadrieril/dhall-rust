use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;

use crate::error::{TypeError, TypeMessage};
use crate::semantics::core::context::TyCtx;
use crate::semantics::core::value::Value;
use crate::semantics::core::value::ValueKind;
use crate::semantics::core::var::{Shift, Subst};
use crate::semantics::phase::normalize::merge_maps;
use crate::semantics::phase::Normalized;
use crate::syntax;
use crate::syntax::{
    Builtin, Const, Expr, ExprKind, InterpolatedTextContents, Label, Span,
    UnspannedExpr,
};

fn tck_pi_type(
    ctx: &TyCtx,
    x: Label,
    tx: Value,
    te: Value,
) -> Result<Value, TypeError> {
    use TypeMessage::*;
    let ctx2 = ctx.insert_type(&x, tx.clone());

    let ka = match tx.get_type()?.as_const() {
        Some(k) => k,
        _ => return Err(TypeError::new(ctx, InvalidInputType(tx))),
    };

    let kb = match te.get_type()?.as_const() {
        Some(k) => k,
        _ => {
            return Err(TypeError::new(
                &ctx2,
                InvalidOutputType(te.get_type()?),
            ))
        }
    };

    let k = function_check(ka, kb);

    Ok(Value::from_kind_and_type(
        ValueKind::Pi(x.into(), tx, te),
        Value::from_const(k),
    ))
}

fn tck_record_type(
    ctx: &TyCtx,
    kts: impl IntoIterator<Item = Result<(Label, Value), TypeError>>,
) -> Result<Value, TypeError> {
    use std::collections::hash_map::Entry;
    use TypeMessage::*;
    let mut new_kts = HashMap::new();
    // An empty record type has type Type
    let mut k = Const::Type;
    for e in kts {
        let (x, t) = e?;
        // Construct the union of the contained `Const`s
        match t.get_type()?.as_const() {
            Some(k2) => k = max(k, k2),
            None => return Err(TypeError::new(ctx, InvalidFieldType(x, t))),
        }
        // Check for duplicated entries
        let entry = new_kts.entry(x);
        match &entry {
            Entry::Occupied(_) => {
                return Err(TypeError::new(ctx, RecordTypeDuplicateField))
            }
            Entry::Vacant(_) => entry.or_insert_with(|| t),
        };
    }

    Ok(Value::from_kind_and_type(
        ValueKind::RecordType(new_kts),
        Value::from_const(k),
    ))
}

fn tck_union_type<Iter>(ctx: &TyCtx, kts: Iter) -> Result<Value, TypeError>
where
    Iter: IntoIterator<Item = Result<(Label, Option<Value>), TypeError>>,
{
    use std::collections::hash_map::Entry;
    use TypeMessage::*;
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
                        InvalidFieldType(x, t.clone()),
                    ))
                }
            }
        }
        let entry = new_kts.entry(x);
        match &entry {
            Entry::Occupied(_) => {
                return Err(TypeError::new(ctx, UnionTypeDuplicateField))
            }
            Entry::Vacant(_) => entry.or_insert_with(|| t),
        };
    }

    // An empty union type has type Type;
    // an union type with only unary variants also has type Type
    let k = k.unwrap_or(Const::Type);

    Ok(Value::from_kind_and_type(
        ValueKind::UnionType(new_kts),
        Value::from_const(k),
    ))
}

fn function_check(a: Const, b: Const) -> Const {
    if b == Const::Type {
        Const::Type
    } else {
        max(a, b)
    }
}

pub(crate) fn const_to_value(c: Const) -> Value {
    let v = ValueKind::Const(c);
    match c {
        Const::Type => {
            Value::from_kind_and_type(v, const_to_value(Const::Kind))
        }
        Const::Kind => {
            Value::from_kind_and_type(v, const_to_value(Const::Sort))
        }
        Const::Sort => Value::const_sort(),
    }
}

pub fn rc<E>(x: UnspannedExpr<E>) -> Expr<E> {
    Expr::new(x, Span::Artificial)
}

// Ad-hoc macro to help construct the types of builtins
macro_rules! make_type {
    (Type) => { ExprKind::Const(Const::Type) };
    (Bool) => { ExprKind::Builtin(Builtin::Bool) };
    (Natural) => { ExprKind::Builtin(Builtin::Natural) };
    (Integer) => { ExprKind::Builtin(Builtin::Integer) };
    (Double) => { ExprKind::Builtin(Builtin::Double) };
    (Text) => { ExprKind::Builtin(Builtin::Text) };
    ($var:ident) => {
        ExprKind::Var(syntax::V(stringify!($var).into(), 0))
    };
    (Optional $ty:ident) => {
        ExprKind::App(
            rc(ExprKind::Builtin(Builtin::Optional)),
            rc(make_type!($ty))
        )
    };
    (List $($rest:tt)*) => {
        ExprKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            rc(make_type!($($rest)*))
        )
    };
    ({ $($label:ident : $ty:ident),* }) => {{
        let mut kts = syntax::map::DupTreeMap::new();
        $(
            kts.insert(
                Label::from(stringify!($label)),
                rc(make_type!($ty)),
            );
        )*
        ExprKind::RecordType(kts)
    }};
    ($ty:ident -> $($rest:tt)*) => {
        ExprKind::Pi(
            "_".into(),
            rc(make_type!($ty)),
            rc(make_type!($($rest)*))
        )
    };
    (($($arg:tt)*) -> $($rest:tt)*) => {
        ExprKind::Pi(
            "_".into(),
            rc(make_type!($($arg)*)),
            rc(make_type!($($rest)*))
        )
    };
    (forall ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
        ExprKind::Pi(
            stringify!($var).into(),
            rc(make_type!($($ty)*)),
            rc(make_type!($($rest)*))
        )
    };
}

fn type_of_builtin<E>(b: Builtin) -> Expr<E> {
    use syntax::Builtin::*;
    rc(match b {
        Bool | Natural | Integer | Double | Text => make_type!(Type),
        List | Optional => make_type!(
            Type -> Type
        ),

        NaturalFold => make_type!(
            Natural ->
            forall (natural: Type) ->
            forall (succ: natural -> natural) ->
            forall (zero: natural) ->
            natural
        ),
        NaturalBuild => make_type!(
            (forall (natural: Type) ->
                forall (succ: natural -> natural) ->
                forall (zero: natural) ->
                natural) ->
            Natural
        ),
        NaturalIsZero | NaturalEven | NaturalOdd => make_type!(
            Natural -> Bool
        ),
        NaturalToInteger => make_type!(Natural -> Integer),
        NaturalShow => make_type!(Natural -> Text),
        NaturalSubtract => make_type!(Natural -> Natural -> Natural),

        IntegerToDouble => make_type!(Integer -> Double),
        IntegerShow => make_type!(Integer -> Text),
        IntegerNegate => make_type!(Integer -> Integer),
        IntegerClamp => make_type!(Integer -> Natural),

        DoubleShow => make_type!(Double -> Text),
        TextShow => make_type!(Text -> Text),

        ListBuild => make_type!(
            forall (a: Type) ->
            (forall (list: Type) ->
                forall (cons: a -> list -> list) ->
                forall (nil: list) ->
                list) ->
            List a
        ),
        ListFold => make_type!(
            forall (a: Type) ->
            (List a) ->
            forall (list: Type) ->
            forall (cons: a -> list -> list) ->
            forall (nil: list) ->
            list
        ),
        ListLength => make_type!(forall (a: Type) -> (List a) -> Natural),
        ListHead | ListLast => {
            make_type!(forall (a: Type) -> (List a) -> Optional a)
        }
        ListIndexed => make_type!(
            forall (a: Type) ->
            (List a) ->
            List { index: Natural, value: a }
        ),
        ListReverse => make_type!(
            forall (a: Type) -> (List a) -> List a
        ),

        OptionalBuild => make_type!(
            forall (a: Type) ->
            (forall (optional: Type) ->
                forall (just: a -> optional) ->
                forall (nothing: optional) ->
                optional) ->
            Optional a
        ),
        OptionalFold => make_type!(
            forall (a: Type) ->
            (Optional a) ->
            forall (optional: Type) ->
            forall (just: a -> optional) ->
            forall (nothing: optional) ->
            optional
        ),
        OptionalNone => make_type!(
            forall (A: Type) -> Optional A
        ),
    })
}

pub(crate) fn builtin_to_value(b: Builtin) -> Value {
    Value::from_kind_and_type(
        ValueKind::from_builtin(b),
        typecheck(type_of_builtin(b)).unwrap(),
    )
}

/// Type-check an expression and return the expression alongside its type if type-checking
/// succeeded, or an error if type-checking failed.
/// Some normalization is done while typechecking, so the returned expression might be partially
/// normalized as well.
fn type_with(ctx: &TyCtx, e: Expr<Normalized>) -> Result<Value, TypeError> {
    use syntax::ExprKind::{Annot, Embed, Lam, Let, Pi, Var};
    let span = e.span();

    match e.as_ref() {
        Lam(var, annot, body) => {
            let annot = type_with(ctx, annot.clone())?;
            annot.normalize_nf();
            let ctx2 = ctx.insert_type(var, annot.clone());
            let body = type_with(&ctx2, body.clone())?;
            let body_type = body.get_type()?;
            Ok(Value::from_kind_and_type(
                ValueKind::Lam(var.clone().into(), annot.clone(), body),
                tck_pi_type(ctx, var.clone(), annot, body_type)?,
            ))
        }
        Pi(x, ta, tb) => {
            let ta = type_with(ctx, ta.clone())?;
            let ctx2 = ctx.insert_type(x, ta.clone());
            let tb = type_with(&ctx2, tb.clone())?;
            tck_pi_type(ctx, x.clone(), ta, tb)
        }
        Let(x, t, v, e) => {
            let v = if let Some(t) = t {
                t.rewrap(Annot(v.clone(), t.clone()))
            } else {
                v.clone()
            };

            let v = type_with(ctx, v)?;
            type_with(&ctx.insert_value(x, v.clone())?, e.clone())
        }
        Embed(p) => Ok(p.clone().into_typed().into_value()),
        Var(var) => match ctx.lookup(&var) {
            Some(typed) => Ok(typed.clone()),
            None => {
                Err(TypeError::new(ctx, TypeMessage::UnboundVariable(span)))
            }
        },
        e => {
            // Typecheck recursively all subexpressions
            let expr = e.traverse_ref_with_special_handling_of_binders(
                |e| type_with(ctx, e.clone()),
                |_, _| unreachable!(),
            )?;
            type_last_layer(ctx, expr, span)
        }
    }
}

/// When all sub-expressions have been typed, check the remaining toplevel
/// layer.
fn type_last_layer(
    ctx: &TyCtx,
    e: ExprKind<Value, Normalized>,
    span: Span,
) -> Result<Value, TypeError> {
    use syntax::BinOp::*;
    use syntax::Builtin::*;
    use syntax::Const::Type;
    use syntax::ExprKind::*;
    use TypeMessage::*;
    let mkerr = |msg: TypeMessage| Err(TypeError::new(ctx, msg));

    /// Intermediary return type
    enum Ret {
        /// Returns the contained value as is
        RetWhole(Value),
        /// Returns the input expression `e` with the contained value as its type
        RetTypeOnly(Value),
    }
    use Ret::*;

    let ret = match &e {
        Import(_) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        Lam(_, _, _) | Pi(_, _, _) | Let(_, _, _, _) | Embed(_) | Var(_) => {
            unreachable!()
        }
        App(f, a) => {
            let tf = f.get_type()?;
            let tf_borrow = tf.as_whnf();
            let (x, tx, tb) = match &*tf_borrow {
                ValueKind::Pi(x, tx, tb) => (x, tx, tb),
                _ => return mkerr(NotAFunction(f.clone())),
            };
            if &a.get_type()? != tx {
                return mkerr(TypeMismatch(f.clone(), tx.clone(), a.clone()));
            }

            let ret = tb.subst_shift(&x.into(), a);
            ret.normalize_nf();
            RetTypeOnly(ret)
        }
        Annot(x, t) => {
            if &x.get_type()? != t {
                return mkerr(AnnotMismatch(x.clone(), t.clone()));
            }
            RetWhole(x.clone())
        }
        Assert(t) => {
            match &*t.as_whnf() {
                ValueKind::Equivalence(x, y) if x == y => {}
                ValueKind::Equivalence(x, y) => {
                    return mkerr(AssertMismatch(x.clone(), y.clone()))
                }
                _ => return mkerr(AssertMustTakeEquivalence),
            }
            RetTypeOnly(t.clone())
        }
        BoolIf(x, y, z) => {
            if *x.get_type()?.as_whnf() != ValueKind::from_builtin(Bool) {
                return mkerr(InvalidPredicate(x.clone()));
            }

            if y.get_type()?.get_type()?.as_const() != Some(Type) {
                return mkerr(IfBranchMustBeTerm(true, y.clone()));
            }

            if z.get_type()?.get_type()?.as_const() != Some(Type) {
                return mkerr(IfBranchMustBeTerm(false, z.clone()));
            }

            if y.get_type()? != z.get_type()? {
                return mkerr(IfBranchMismatch(y.clone(), z.clone()));
            }

            RetTypeOnly(y.get_type()?)
        }
        EmptyListLit(t) => {
            match &*t.as_whnf() {
                ValueKind::AppliedBuiltin(syntax::Builtin::List, args)
                    if args.len() == 1 => {}
                _ => return mkerr(InvalidListType(t.clone())),
            }
            RetTypeOnly(t.clone())
        }
        NEListLit(xs) => {
            let mut iter = xs.iter().enumerate();
            let (_, x) = iter.next().unwrap();
            for (i, y) in iter {
                if x.get_type()? != y.get_type()? {
                    return mkerr(InvalidListElement(
                        i,
                        x.get_type()?,
                        y.clone(),
                    ));
                }
            }
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Type) {
                return mkerr(InvalidListType(t));
            }

            RetTypeOnly(Value::from_builtin(syntax::Builtin::List).app(t))
        }
        SomeLit(x) => {
            let t = x.get_type()?;
            if t.get_type()?.as_const() != Some(Type) {
                return mkerr(InvalidOptionalType(t));
            }

            RetTypeOnly(Value::from_builtin(syntax::Builtin::Optional).app(t))
        }
        RecordType(kts) => RetWhole(tck_record_type(
            ctx,
            kts.iter().map(|(x, t)| Ok((x.clone(), t.clone()))),
        )?),
        UnionType(kts) => RetWhole(tck_union_type(
            ctx,
            kts.iter().map(|(x, t)| Ok((x.clone(), t.clone()))),
        )?),
        RecordLit(kvs) => RetTypeOnly(tck_record_type(
            ctx,
            kvs.iter().map(|(x, v)| Ok((x.clone(), v.get_type()?))),
        )?),
        Field(r, x) => {
            match &*r.get_type()?.as_whnf() {
                ValueKind::RecordType(kts) => match kts.get(&x) {
                    Some(tth) => {
                        RetTypeOnly(tth.clone())
                    },
                    None => return mkerr(MissingRecordField(x.clone(),
                                        r.clone())),
                },
                // TODO: branch here only when r.get_type() is a Const
                _ => {
                    match &*r.as_whnf() {
                        ValueKind::UnionType(kts) => match kts.get(&x) {
                            // Constructor has type T -> < x: T, ... >
                            Some(Some(t)) => {
                                RetTypeOnly(
                                    tck_pi_type(
                                        ctx,
                                        x.clone(),
                                        t.clone(),
                                        r.under_binder(x),
                                    )?
                                )
                            },
                            Some(None) => {
                                RetTypeOnly(r.clone())
                            },
                            None => {
                                return mkerr(MissingUnionField(
                                    x.clone(),
                                    r.clone(),
                                ))
                            },
                        },
                        _ => {
                            return mkerr(NotARecord(
                                x.clone(),
                                r.clone()
                            ))
                        },
                    }
                }
                // _ => mkerr(NotARecord(
                //     x,
                //     r?,
                // )),
            }
        }
        Const(c) => RetWhole(const_to_value(*c)),
        Builtin(b) => RetWhole(builtin_to_value(*b)),
        BoolLit(_) => RetTypeOnly(builtin_to_value(Bool)),
        NaturalLit(_) => RetTypeOnly(builtin_to_value(Natural)),
        IntegerLit(_) => RetTypeOnly(builtin_to_value(Integer)),
        DoubleLit(_) => RetTypeOnly(builtin_to_value(Double)),
        TextLit(interpolated) => {
            let text_type = builtin_to_value(Text);
            for contents in interpolated.iter() {
                use InterpolatedTextContents::Expr;
                if let Expr(x) = contents {
                    if x.get_type()? != text_type {
                        return mkerr(InvalidTextInterpolation(x.clone()));
                    }
                }
            }
            RetTypeOnly(text_type)
        }
        BinOp(RightBiasedRecordMerge, l, r) => {
            let l_type = l.get_type()?;
            let r_type = r.get_type()?;

            // Extract the LHS record type
            let l_type_borrow = l_type.as_whnf();
            let kts_x = match &*l_type_borrow {
                ValueKind::RecordType(kts) => kts,
                _ => return mkerr(MustCombineRecord(l.clone())),
            };

            // Extract the RHS record type
            let r_type_borrow = r_type.as_whnf();
            let kts_y = match &*r_type_borrow {
                ValueKind::RecordType(kts) => kts,
                _ => return mkerr(MustCombineRecord(r.clone())),
            };

            // Union the two records, prefering
            // the values found in the RHS.
            let kts = merge_maps::<_, _, _, !>(kts_x, kts_y, |_, _, r_t| {
                Ok(r_t.clone())
            })?;

            // Construct the final record type from the union
            RetTypeOnly(tck_record_type(
                ctx,
                kts.into_iter().map(|(x, v)| Ok((x.clone(), v))),
            )?)
        }
        BinOp(RecursiveRecordMerge, l, r) => RetTypeOnly(type_last_layer(
            ctx,
            ExprKind::BinOp(
                RecursiveRecordTypeMerge,
                l.get_type()?,
                r.get_type()?,
            ),
            Span::Artificial,
        )?),
        BinOp(RecursiveRecordTypeMerge, l, r) => {
            // Extract the LHS record type
            let borrow_l = l.as_whnf();
            let kts_x = match &*borrow_l {
                ValueKind::RecordType(kts) => kts,
                _ => {
                    return mkerr(RecordTypeMergeRequiresRecordType(l.clone()))
                }
            };

            // Extract the RHS record type
            let borrow_r = r.as_whnf();
            let kts_y = match &*borrow_r {
                ValueKind::RecordType(kts) => kts,
                _ => {
                    return mkerr(RecordTypeMergeRequiresRecordType(r.clone()))
                }
            };

            // Ensure that the records combine without a type error
            let kts = merge_maps(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Value, r: &Value| {
                    type_last_layer(
                        ctx,
                        ExprKind::BinOp(
                            RecursiveRecordTypeMerge,
                            l.clone(),
                            r.clone(),
                        ),
                        Span::Artificial,
                    )
                },
            )?;

            RetWhole(tck_record_type(ctx, kts.into_iter().map(Ok))?)
        }
        BinOp(o @ ListAppend, l, r) => {
            match &*l.get_type()?.as_whnf() {
                ValueKind::AppliedBuiltin(List, _) => {}
                _ => return mkerr(BinOpTypeMismatch(*o, l.clone())),
            }

            if l.get_type()? != r.get_type()? {
                return mkerr(BinOpTypeMismatch(*o, r.clone()));
            }

            RetTypeOnly(l.get_type()?)
        }
        BinOp(Equivalence, l, r) => {
            if l.get_type()?.get_type()?.as_const() != Some(Type) {
                return mkerr(EquivalenceArgumentMustBeTerm(true, l.clone()));
            }
            if r.get_type()?.get_type()?.as_const() != Some(Type) {
                return mkerr(EquivalenceArgumentMustBeTerm(false, r.clone()));
            }

            if l.get_type()? != r.get_type()? {
                return mkerr(EquivalenceTypeMismatch(r.clone(), l.clone()));
            }

            RetWhole(Value::from_kind_and_type(
                ValueKind::Equivalence(l.clone(), r.clone()),
                Value::from_const(Type),
            ))
        }
        BinOp(o, l, r) => {
            let t = builtin_to_value(match o {
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
                Equivalence => unreachable!(),
            });

            if l.get_type()? != t {
                return mkerr(BinOpTypeMismatch(*o, l.clone()));
            }

            if r.get_type()? != t {
                return mkerr(BinOpTypeMismatch(*o, r.clone()));
            }

            RetTypeOnly(t)
        }
        Merge(record, union, type_annot) => {
            let record_type = record.get_type()?;
            let record_borrow = record_type.as_whnf();
            let handlers = match &*record_borrow {
                ValueKind::RecordType(kts) => kts,
                _ => return mkerr(Merge1ArgMustBeRecord(record.clone())),
            };

            let union_type = union.get_type()?;
            let union_borrow = union_type.as_whnf();
            let variants = match &*union_borrow {
                ValueKind::UnionType(kts) => Cow::Borrowed(kts),
                ValueKind::AppliedBuiltin(syntax::Builtin::Optional, args)
                    if args.len() == 1 =>
                {
                    let ty = &args[0];
                    let mut kts = HashMap::new();
                    kts.insert("None".into(), None);
                    kts.insert("Some".into(), Some(ty.clone()));
                    Cow::Owned(kts)
                }
                _ => {
                    return mkerr(Merge2ArgMustBeUnionOrOptional(union.clone()))
                }
            };

            let mut inferred_type = None;
            for (x, handler_type) in handlers {
                let handler_return_type =
                    match variants.get(x) {
                        // Union alternative with type
                        Some(Some(variant_type)) => {
                            let handler_type_borrow = handler_type.as_whnf();
                            let (x, tx, tb) = match &*handler_type_borrow {
                                ValueKind::Pi(x, tx, tb) => (x, tx, tb),
                                _ => {
                                    return mkerr(NotAFunction(
                                        handler_type.clone(),
                                    ))
                                }
                            };

                            if variant_type != tx {
                                return mkerr(TypeMismatch(
                                    handler_type.clone(),
                                    tx.clone(),
                                    variant_type.clone(),
                                ));
                            }

                            // Extract `tb` from under the `x` binder. Fails is `x` was free in `tb`.
                            match tb.over_binder(x) {
                                Some(x) => x,
                                None => return mkerr(
                                    MergeHandlerReturnTypeMustNotBeDependent,
                                ),
                            }
                        }
                        // Union alternative without type
                        Some(None) => handler_type.clone(),
                        None => {
                            return mkerr(MergeHandlerMissingVariant(x.clone()))
                        }
                    };
                match &inferred_type {
                    None => inferred_type = Some(handler_return_type),
                    Some(t) => {
                        if t != &handler_return_type {
                            return mkerr(MergeHandlerTypeMismatch);
                        }
                    }
                }
            }
            for x in variants.keys() {
                if !handlers.contains_key(x) {
                    return mkerr(MergeVariantMissingHandler(x.clone()));
                }
            }

            match (inferred_type, type_annot.as_ref()) {
                (Some(t1), Some(t2)) => {
                    if &t1 != t2 {
                        return mkerr(MergeAnnotMismatch);
                    }
                    RetTypeOnly(t1)
                }
                (Some(t), None) => RetTypeOnly(t),
                (None, Some(t)) => RetTypeOnly(t.clone()),
                (None, None) => return mkerr(MergeEmptyNeedsAnnotation),
            }
        }
        ToMap(_, _) => unimplemented!("toMap"),
        Projection(record, labels) => {
            let record_type = record.get_type()?;
            let record_type_borrow = record_type.as_whnf();
            let kts = match &*record_type_borrow {
                ValueKind::RecordType(kts) => kts,
                _ => return mkerr(ProjectionMustBeRecord),
            };

            let mut new_kts = HashMap::new();
            for l in labels {
                match kts.get(l) {
                    None => return mkerr(ProjectionMissingEntry),
                    Some(t) => {
                        use std::collections::hash_map::Entry;
                        match new_kts.entry(l.clone()) {
                            Entry::Occupied(_) => {
                                return mkerr(ProjectionDuplicateField)
                            }
                            Entry::Vacant(e) => e.insert(t.clone()),
                        }
                    }
                };
            }

            RetTypeOnly(Value::from_kind_and_type(
                ValueKind::RecordType(new_kts),
                record_type.get_type()?,
            ))
        }
        ProjectionByExpr(_, _) => unimplemented!("selection by expression"),
        Completion(_, _) => unimplemented!("record completion"),
    };

    Ok(match ret {
        RetTypeOnly(typ) => Value::from_kind_and_type_and_span(
            ValueKind::PartialExpr(e),
            typ,
            span,
        ),
        RetWhole(v) => v.with_span(span),
    })
}

/// `type_of` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
pub(crate) fn typecheck(e: Expr<Normalized>) -> Result<Value, TypeError> {
    type_with(&TyCtx::new(), e)
}

pub(crate) fn typecheck_with(
    expr: Expr<Normalized>,
    ty: Expr<Normalized>,
) -> Result<Value, TypeError> {
    typecheck(expr.rewrap(ExprKind::Annot(expr.clone(), ty)))
}
