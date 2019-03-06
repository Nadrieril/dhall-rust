#![allow(non_snake_case)]
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::fmt;

use dhall_core::context::Context;
use dhall_core::core;
use dhall_core::core::Builtin::*;
use dhall_core::core::Const::*;
use dhall_core::core::Expr::*;
use dhall_core::core::{app, pi};
use dhall_core::core::{bx, shift, subst, Expr, V, X};
use dhall_normalize::{normalize};

use self::TypeMessage::*;

fn axiom<'i, S: Clone>(
    c: core::Const,
) -> Result<core::Const, TypeError<'i, S>> {
    match c {
        Type => Ok(Kind),
        Kind => Err(TypeError::new(&Context::new(), &Const(Kind), Untyped)),
    }
}

fn rule(a: core::Const, b: core::Const) -> Result<core::Const, ()> {
    match (a, b) {
        (Type, Kind) => Err(()),
        (Kind, Kind) => Ok(Kind),
        (Type, Type) | (Kind, Type) => Ok(Type),
    }
}

fn match_vars(vl: &V, vr: &V, ctx: &[(&str, &str)]) -> bool {
    let xxs = ctx.get(0).map(|x| (x, ctx.split_at(1).1));
    match (vl, vr, xxs) {
        (&V(xL, nL), &V(xR, nR), None) => xL == xR && nL == nR,
        (&V(xL, 0), &V(xR, 0), Some((&(xL2, xR2), _)))
            if xL == xL2 && xR == xR2 =>
        {
            true
        }
        (&V(xL, nL), &V(xR, nR), Some((&(xL2, xR2), xs))) => {
            let nL2 = if xL == xL2 { nL - 1 } else { nL };
            let nR2 = if xR == xR2 { nR - 1 } else { nR };
            match_vars(&V(xL, nL2), &V(xR, nR2), xs)
        }
    }
}

fn prop_equal<S, T>(eL0: &Expr<S, X>, eR0: &Expr<T, X>) -> bool
where
    S: Clone + ::std::fmt::Debug,
    T: Clone + ::std::fmt::Debug,
{
    fn go<'i, S, T>(
        ctx: &mut Vec<(&'i str, &'i str)>,
        el: &'i Expr<'i, S, X>,
        er: &'i Expr<'i, T, X>,
    ) -> bool
    where
        S: Clone + ::std::fmt::Debug,
        T: Clone + ::std::fmt::Debug,
    {
        match (el, er) {
            (&Const(Type), &Const(Type)) | (&Const(Kind), &Const(Kind)) => true,
            (&Var(ref vL), &Var(ref vR)) => match_vars(vL, vR, &*ctx),
            (&Pi(xL, ref tL, ref bL), &Pi(xR, ref tR, ref bR)) => {
                //ctx <- State.get
                let eq1 = go(ctx, tL, tR);
                if eq1 {
                    //State.put ((xL, xR):ctx)
                    ctx.push((xL, xR));
                    let eq2 = go(ctx, bL, bR);
                    //State.put ctx
                    let _ = ctx.pop();
                    eq2
                } else {
                    false
                }
            }
            (&App(ref fL, ref aL), &App(ref fR, ref aR)) => {
                if go(ctx, fL, fR) {
                    go(ctx, aL, aR)
                } else {
                    false
                }
            }
            (&Builtin(a), &Builtin(b)) => a == b,
            (&Record(ref ktsL0), &Record(ref ktsR0)) => {
                if ktsL0.len() != ktsR0.len() {
                    return false;
                }
                /*
                let go ((kL, tL):ktsL) ((kR, tR):ktsR)
                        | kL == kR = do
                            b <- go tL tR
                            if b
                                then go ktsL ktsR
                                else return False
                    go [] [] = return True
                    go _  _  = return False
                */
                /*
                for ((kL, tL), (kR, tR)) in ktsL0.iter().zip(ktsR0.iter()) {
                    if kL == kR {
                        if !go(ctx, tL, tR) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
                */
                !ktsL0
                    .iter()
                    .zip(ktsR0.iter())
                    .any(|((kL, tL), (kR, tR))| kL != kR || !go(ctx, tL, tR))
            }
            (&Union(ref ktsL0), &Union(ref ktsR0)) => {
                if ktsL0.len() != ktsR0.len() {
                    return false;
                }
                /*
                    let loop ((kL, tL):ktsL) ((kR, tR):ktsR)
                            | kL == kR = do
                                b <- go tL tR
                                if b
                                    then loop ktsL ktsR
                                    else return False
                        loop [] [] = return True
                        loop _  _  = return False
                    loop (Data.Map.toList ktsL0) (Data.Map.toList ktsR0)
                */
                !ktsL0
                    .iter()
                    .zip(ktsR0.iter())
                    .any(|((kL, tL), (kR, tR))| kL != kR || !go(ctx, tL, tR))
            }
            (_, _) => false,
        }
    }
    let mut ctx = vec![];
    go::<S, T>(&mut ctx, &normalize(eL0), &normalize(eR0))
}

fn op2_type<'i, S, EF>(
    ctx: &Context<'i, Expr<'i, S, X>>,
    e: &Expr<'i, S, X>,
    t: core::Builtin,
    ef: EF,
    l: &Expr<'i, S, X>,
    r: &Expr<'i, S, X>,
) -> Result<Expr<'i, S, X>, TypeError<'i, S>>
where
    S: Clone + ::std::fmt::Debug + 'i,
    EF: FnOnce(Expr<'i, S, X>, Expr<'i, S, X>) -> TypeMessage<'i, S>,
{
    let tl = normalize(&type_with(ctx, l)?);
    match tl {
        Builtin(lt) if lt == t => {}
        _ => return Err(TypeError::new(ctx, e, ef((*l).clone(), tl))),
    }

    let tr = normalize(&type_with(ctx, r)?);
    match tr {
        Builtin(rt) if rt == t => {}
        _ => return Err(TypeError::new(ctx, e, ef((*r).clone(), tr))),
    }

    Ok(Builtin(t))
}

/// Type-check an expression and return the expression'i type if type-checking
/// suceeds or an error if type-checking fails
///
/// `type_with` does not necessarily normalize the type since full normalization
/// is not necessary for just type-checking.  If you actually care about the
/// returned type then you may want to `normalize` it afterwards.
pub fn type_with<'i, S>(
    ctx: &Context<'i, Expr<'i, S, X>>,
    e: &Expr<'i, S, X>,
) -> Result<Expr<'i, S, X>, TypeError<'i, S>>
where
    S: Clone + ::std::fmt::Debug + 'i,
{
    use dhall_core::BinOp::*;
    match *e {
        Const(c) => axiom(c).map(Const), //.map(Cow::Owned),
        Var(V(x, n)) => {
            ctx.lookup(x, n)
                .cloned()
                //.map(Cow::Borrowed)
                .ok_or_else(|| TypeError::new(ctx, e, UnboundVariable))
        }
        Lam(x, ref tA, ref b) => {
            let ctx2 = ctx
                .insert(x, (**tA).clone())
                .map(|e| core::shift(1, V(x, 0), e));
            let tB = type_with(&ctx2, b)?;
            let p = Pi(x, tA.clone(), bx(tB));
            let _ = type_with(ctx, &p)?;
            //Ok(Cow::Owned(p))
            Ok(p)
        }
        Pi(x, ref tA, ref tB) => {
            let tA2 = normalize::<S, S, X>(&type_with(ctx, tA)?);
            let kA = match tA2 {
                Const(k) => k,
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        InvalidInputType((**tA).clone()),
                    ));
                }
            };

            let ctx2 = ctx
                .insert(x, (**tA).clone())
                .map(|e| core::shift(1, V(x, 0), e));
            let tB = normalize(&type_with(&ctx2, tB)?);
            let kB = match tB {
                Const(k) => k,
                _ => {
                    return Err(TypeError::new(&ctx2, e, InvalidOutputType(tB)));
                }
            };

            match rule(kA, kB) {
                Err(()) => Err(TypeError::new(
                    ctx,
                    e,
                    NoDependentTypes((**tA).clone(), tB),
                )),
                Ok(k) => Ok(Const(k)),
            }
        }
        App(ref f, ref a) => {
            let tf = normalize(&type_with(ctx, f)?);
            let (x, tA, tB) = match tf {
                Pi(x, tA, tB) => (x, tA, tB),
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        NotAFunction((**f).clone(), tf),
                    ));
                }
            };
            let tA2 = type_with(ctx, a)?;
            if prop_equal(&tA, &tA2) {
                let vx0 = V(x, 0);
                let a2 = shift::<S, S, X>(1, vx0, a);
                let tB2 = subst(vx0, &a2, &tB);
                let tB3 = shift::<S, S, X>(-1, vx0, &tB2);
                Ok(tB3)
            } else {
                let nf_A = normalize(&tA);
                let nf_A2 = normalize(&tA2);
                Err(TypeError::new(
                    ctx,
                    e,
                    TypeMismatch((**f).clone(), nf_A, (**a).clone(), nf_A2),
                ))
            }
        }
        Let(f, ref mt, ref r, ref b) => {
            let tR = type_with(ctx, r)?;
            let ttR = normalize::<S, S, X>(&type_with(ctx, &tR)?);
            let kR = match ttR {
                Const(k) => k,
                // Don't bother to provide a `let`-specific version of this error
                // message because this should never happen anyway
                _ => return Err(TypeError::new(ctx, e, InvalidInputType(tR))),
            };

            let ctx2 = ctx.insert(f, tR.clone());
            let tB = type_with(&ctx2, b)?;
            let ttB = normalize::<S, S, X>(&type_with(ctx, &tB)?);
            let kB = match ttB {
                Const(k) => k,
                // Don't bother to provide a `let`-specific version of this error
                // message because this should never happen anyway
                _ => return Err(TypeError::new(ctx, e, InvalidOutputType(tB))),
            };

            if let Err(()) = rule(kR, kB) {
                return Err(TypeError::new(ctx, e, NoDependentLet(tR, tB)));
            }

            if let Some(ref t) = *mt {
                let nf_t = normalize(t);
                let nf_tR = normalize(&tR);
                if !prop_equal(&nf_tR, &nf_t) {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        AnnotMismatch((**r).clone(), nf_t, nf_tR),
                    ));
                }
            }

            Ok(tB)
        }
        Annot(ref x, ref t) => {
            // This is mainly just to check that `t` is not `Kind`
            let _ = type_with(ctx, t)?;

            let t2 = type_with(ctx, x)?;
            if prop_equal(t, &t2) {
                Ok((**t).clone())
            } else {
                let nf_t = normalize(t);
                let nf_t2 = normalize(&t2);
                Err(TypeError::new(
                    ctx,
                    e,
                    AnnotMismatch((**x).clone(), nf_t, nf_t2),
                ))
            }
        }
        BoolLit(_) => Ok(Builtin(Bool)),
        BinOp(BoolAnd, ref l, ref r) => op2_type(ctx, e, Bool, CantAnd, l, r),
        BinOp(BoolOr, ref l, ref r) => op2_type(ctx, e, Bool, CantOr, l, r),
        BinOp(BoolEQ, ref l, ref r) => op2_type(ctx, e, Bool, CantEQ, l, r),
        BinOp(BoolNE, ref l, ref r) => op2_type(ctx, e, Bool, CantNE, l, r),
        BoolIf(ref x, ref y, ref z) => {
            let tx = normalize(&type_with(ctx, x)?);
            match tx {
                Builtin(Bool) => {}
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        InvalidPredicate((**x).clone(), tx),
                    ));
                }
            }
            let ty = normalize(&type_with(ctx, y)?);
            let tty = normalize(&type_with(ctx, &ty)?);
            match tty {
                Const(Type) => {}
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        IfBranchMustBeTerm(true, (**y).clone(), ty, tty),
                    ));
                }
            }

            let tz = normalize(&type_with(ctx, z)?);
            let ttz = normalize(&type_with(ctx, &tz)?);
            match ttz {
                Const(Type) => {}
                _ => {
                    return Err(TypeError::new(
                        ctx,
                        e,
                        IfBranchMustBeTerm(false, (**z).clone(), tz, ttz),
                    ));
                }
            }

            if !prop_equal(&ty, &tz) {
                return Err(TypeError::new(
                    ctx,
                    e,
                    IfBranchMismatch((**y).clone(), (**z).clone(), ty, tz),
                ));
            }
            Ok(ty)
        }
        NaturalLit(_) => Ok(Builtin(Natural)),
        Builtin(NaturalFold) => Ok(pi(
            "_",
            Natural,
            pi(
                "natural",
                Const(Type),
                pi(
                    "succ",
                    pi("_", "natural", "natural"),
                    pi("zero", "natural", "natural"),
                ),
            ),
        )),
        Builtin(NaturalBuild) => Ok(pi(
            "_",
            pi(
                "natural",
                Const(Type),
                pi(
                    "succ",
                    pi("_", "natural", "natural"),
                    pi("zero", "natural", "natural"),
                ),
            ),
            Natural,
        )),
        Builtin(NaturalIsZero) | Builtin(NaturalEven) | Builtin(NaturalOdd) => {
            Ok(pi("_", Natural, Bool))
        }
        BinOp(NaturalPlus, ref l, ref r) => {
            op2_type(ctx, e, Natural, CantAdd, l, r)
        }
        BinOp(NaturalTimes, ref l, ref r) => {
            op2_type(ctx, e, Natural, CantMultiply, l, r)
        }
        IntegerLit(_) => Ok(Builtin(Integer)),
        DoubleLit(_) => Ok(Builtin(Double)),
        TextLit(_) => Ok(Builtin(Text)),
        BinOp(TextAppend, ref l, ref r) => {
            op2_type(ctx, e, Text, CantTextAppend, l, r)
        }
        ListLit(ref t, ref xs) => {
            let mut iter = xs.iter().enumerate();
            let t: Box<Expr<_, _>> = match t {
                Some(t) => t.clone(),
                None => {
                    let (_, first_x) = iter.next().unwrap();
                    bx(type_with(ctx, first_x)?)
                }
            };

            let s = normalize::<_, S, _>(&type_with(ctx, &t)?);
            match s {
                Const(Type) => {}
                _ => return Err(TypeError::new(ctx, e, InvalidListType(*t))),
            }
            for (i, x) in iter {
                let t2 = type_with(ctx, x)?;
                if !prop_equal(&t, &t2) {
                    let nf_t = normalize(&t);
                    let nf_t2 = normalize(&t2);
                    return Err(TypeError::new(
                        ctx,
                        e,
                        InvalidListElement(i, nf_t, x.clone(), nf_t2),
                    ));
                }
            }
            Ok(App(bx(Builtin(List)), t))
        }
        Builtin(ListBuild) => Ok(pi(
            "a",
            Const(Type),
            pi(
                "_",
                pi(
                    "list",
                    Const(Type),
                    pi(
                        "cons",
                        pi("_", "a", pi("_", "list", "list")),
                        pi("nil", "list", "list"),
                    ),
                ),
                app(List, "a"),
            ),
        )),
        Builtin(ListFold) => Ok(pi(
            "a",
            Const(Type),
            pi(
                "_",
                app(List, "a"),
                pi(
                    "list",
                    Const(Type),
                    pi(
                        "cons",
                        pi("_", "a", pi("_", "list", "list")),
                        pi("nil", "list", "list"),
                    ),
                ),
            ),
        )),
        Builtin(ListLength) => {
            Ok(pi("a", Const(Type), pi("_", app(List, "a"), Natural)))
        }
        Builtin(ListHead) | Builtin(ListLast) => Ok(pi(
            "a",
            Const(Type),
            pi("_", app(List, "a"), app(Optional, "a")),
        )),
        Builtin(ListIndexed) => {
            let mut m = BTreeMap::new();
            m.insert("index", Builtin(Natural));
            m.insert("value", Expr::from("a"));
            Ok(pi(
                "a",
                Const(Type),
                pi("_", app(List, "a"), app(List, Record(m))),
            ))
        }
        Builtin(ListReverse) => Ok(pi(
            "a",
            Const(Type),
            pi("_", app(List, "a"), app(List, "a")),
        )),
        OptionalLit(ref t, ref xs) => {
            let mut iter = xs.iter();
            let t: Box<Expr<_, _>> = match t {
                Some(t) => t.clone(),
                None => {
                    let first_x = iter.next().unwrap();
                    bx(type_with(ctx, first_x)?)
                }
            };

            let s = normalize::<_, S, _>(&type_with(ctx, &t)?);
            match s {
                Const(Type) => {}
                _ => {
                    return Err(TypeError::new(ctx, e, InvalidOptionalType(*t)));
                }
            }
            let n = xs.len();
            if 2 <= n {
                return Err(TypeError::new(ctx, e, InvalidOptionalLiteral(n)));
            }
            for x in iter {
                let t2 = type_with(ctx, x)?;
                if !prop_equal(&t, &t2) {
                    let nf_t = normalize(&t);
                    let nf_t2 = normalize(&t2);
                    return Err(TypeError::new(
                        ctx,
                        e,
                        InvalidOptionalElement(nf_t, x.clone(), nf_t2),
                    ));
                }
            }
            Ok(App(bx(Builtin(Optional)), t))
        }
        Builtin(OptionalFold) => Ok(pi(
            "a",
            Const(Type),
            pi(
                "_",
                app(Optional, "a"),
                pi(
                    "optional",
                    Const(Type),
                    pi(
                        "just",
                        pi("_", "a", "optional"),
                        pi("nothing", "optional", "optional"),
                    ),
                ),
            ),
        )),
        Builtin(List) | Builtin(Optional) => {
            Ok(pi("_", Const(Type), Const(Type)))
        }
        Builtin(Bool) | Builtin(Natural) | Builtin(Integer)
        | Builtin(Double) | Builtin(Text) => Ok(Const(Type)),
        Record(ref kts) => {
            for (k, t) in kts {
                let s = normalize::<S, S, X>(&type_with(ctx, t)?);
                match s {
                    Const(Type) => {}
                    _ => {
                        return Err(TypeError::new(
                            ctx,
                            e,
                            InvalidFieldType((*k).to_owned(), (*t).clone()),
                        ));
                    }
                }
            }
            Ok(Const(Type))
        }
        RecordLit(ref kvs) => {
            let kts = kvs
                .iter()
                .map(|(&k, v)| {
                    let t = type_with(ctx, v)?;
                    let s = normalize::<S, S, X>(&type_with(ctx, &t)?);
                    match s {
                        Const(Type) => {}
                        _ => {
                            return Err(TypeError::new(
                                ctx,
                                e,
                                InvalidField((*k).to_owned(), (*v).clone()),
                            ));
                        }
                    }
                    Ok((k, t))
                })
                .collect::<Result<_, _>>()?;
            Ok(Record(kts))
        }
        /*
        type_with ctx e@(Union     kts   ) = do
            let process (k, t) = do
                    s <- fmap Dhall.Core.normalize (type_with ctx t)
                    case s of
                        Const Type -> return ()
                        _          -> Left (TypeError ctx e (InvalidAlternativeType k t))
            mapM_ process (Data.Map.toList kts)
            return (Const Type)
        type_with ctx e@(UnionLit k v kts) = do
            case Data.Map.lookup k kts of
                Just _  -> Left (TypeError ctx e (DuplicateAlternative k))
                Nothing -> return ()
            t <- type_with ctx v
            let union = Union (Data.Map.insert k t kts)
            _ <- type_with ctx union
            return union
        type_with ctx e@(Combine kvsX kvsY) = do
            tKvsX <- fmap Dhall.Core.normalize (type_with ctx kvsX)
            ktsX  <- case tKvsX of
                Record kts -> return kts
                _          -> Left (TypeError ctx e (MustCombineARecord kvsX tKvsX))

            tKvsY <- fmap Dhall.Core.normalize (type_with ctx kvsY)
            ktsY  <- case tKvsY of
                Record kts -> return kts
                _          -> Left (TypeError ctx e (MustCombineARecord kvsY tKvsY))

            let combineTypes ktsL ktsR = do
                    let ks =
                            Data.Set.union (Data.Map.keysSet ktsL) (Data.Map.keysSet ktsR)
                    kts <- forM (toList ks) (\k -> do
                        case (Data.Map.lookup k ktsL, Data.Map.lookup k ktsR) of
                            (Just (Record ktsL'), Just (Record ktsR')) -> do
                                t <- combineTypes ktsL' ktsR'
                                return (k, t)
                            (Nothing, Just t) -> do
                                return (k, t)
                            (Just t, Nothing) -> do
                                return (k, t)
                            _ -> do
                                Left (TypeError ctx e (FieldCollision k)) )
                    return (Record (Data.Map.fromList kts))

            combineTypes ktsX ktsY
        type_with ctx e@(Merge kvsX kvsY t) = do
            tKvsX <- fmap Dhall.Core.normalize (type_with ctx kvsX)
            ktsX  <- case tKvsX of
                Record kts -> return kts
                _          -> Left (TypeError ctx e (MustMergeARecord kvsX tKvsX))
            let ksX = Data.Map.keysSet ktsX

            tKvsY <- fmap Dhall.Core.normalize (type_with ctx kvsY)
            ktsY  <- case tKvsY of
                Union kts -> return kts
                _         -> Left (TypeError ctx e (MustMergeUnion kvsY tKvsY))
            let ksY = Data.Map.keysSet ktsY

            let diffX = Data.Set.difference ksX ksY
            let diffY = Data.Set.difference ksY ksX

            if Data.Set.null diffX
                then return ()
                else Left (TypeError ctx e (UnusedHandler diffX))

            let process (kY, tY) = do
                    case Data.Map.lookup kY ktsX of
                        Nothing  -> Left (TypeError ctx e (MissingHandler diffY))
                        Just tX  ->
                            case tX of
                                Pi _ tY' t' -> do
                                    if prop_equal tY tY'
                                        then return ()
                                        else Left (TypeError ctx e (HandlerInputTypeMismatch kY tY tY'))
                                    if prop_equal t t'
                                        then return ()
                                        else Left (TypeError ctx e (HandlerOutputTypeMismatch kY t t'))
                                _ -> Left (TypeError ctx e (HandlerNotAFunction kY tX))
            mapM_ process (Data.Map.toList ktsY)
            return t
            */
        Field(ref r, x) => {
            let t = normalize(&type_with(ctx, r)?);
            match t {
                Record(ref kts) => kts.get(x).cloned().ok_or_else(|| {
                    TypeError::new(
                        ctx,
                        e,
                        MissingField(x.to_owned(), t.clone()),
                    )
                }),
                _ => Err(TypeError::new(
                    ctx,
                    e,
                    NotARecord(x.to_owned(), (**r).clone(), t.clone()),
                )),
            }
        }
        /*
        type_with ctx   (Note s e'       ) = case type_with ctx e' of
            Left (TypeError ctx2 (Note s' e'') m) -> Left (TypeError ctx2 (Note s' e'') m)
            Left (TypeError ctx2          e''  m) -> Left (TypeError ctx2 (Note s  e'') m)
            Right r                               -> Right r
        */
        Embed(p) => match p {},
        _ => panic!("Unimplemented typecheck case: {:?}", e),
    }
}

/// `typeOf` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
pub fn type_of<'i, S: Clone + ::std::fmt::Debug + 'i>(
    e: &Expr<'i, S, X>,
) -> Result<Expr<'i, S, X>, TypeError<'i, S>> {
    let ctx = Context::new();
    type_with(&ctx, e) //.map(|e| e.into_owned())
}

/// The specific type error
#[derive(Debug)]
pub enum TypeMessage<'i, S> {
    UnboundVariable,
    InvalidInputType(Expr<'i, S, X>),
    InvalidOutputType(Expr<'i, S, X>),
    NotAFunction(Expr<'i, S, X>, Expr<'i, S, X>),
    TypeMismatch(
        Expr<'i, S, X>,
        Expr<'i, S, X>,
        Expr<'i, S, X>,
        Expr<'i, S, X>,
    ),
    AnnotMismatch(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    Untyped,
    InvalidListElement(usize, Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    InvalidListType(Expr<'i, S, X>),
    InvalidOptionalElement(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    InvalidOptionalLiteral(usize),
    InvalidOptionalType(Expr<'i, S, X>),
    InvalidPredicate(Expr<'i, S, X>, Expr<'i, S, X>),
    IfBranchMismatch(
        Expr<'i, S, X>,
        Expr<'i, S, X>,
        Expr<'i, S, X>,
        Expr<'i, S, X>,
    ),
    IfBranchMustBeTerm(bool, Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    InvalidField(String, Expr<'i, S, X>),
    InvalidFieldType(String, Expr<'i, S, X>),
    InvalidAlternative(String, Expr<'i, S, X>),
    InvalidAlternativeType(String, Expr<'i, S, X>),
    DuplicateAlternative(String),
    MustCombineARecord(Expr<'i, S, X>, Expr<'i, S, X>),
    FieldCollision(String),
    MustMergeARecord(Expr<'i, S, X>, Expr<'i, S, X>),
    MustMergeUnion(Expr<'i, S, X>, Expr<'i, S, X>),
    UnusedHandler(HashSet<String>),
    MissingHandler(HashSet<String>),
    HandlerInputTypeMismatch(String, Expr<'i, S, X>, Expr<'i, S, X>),
    HandlerOutputTypeMismatch(String, Expr<'i, S, X>, Expr<'i, S, X>),
    HandlerNotAFunction(String, Expr<'i, S, X>),
    NotARecord(String, Expr<'i, S, X>, Expr<'i, S, X>),
    MissingField(String, Expr<'i, S, X>),
    CantAnd(Expr<'i, S, X>, Expr<'i, S, X>),
    CantOr(Expr<'i, S, X>, Expr<'i, S, X>),
    CantEQ(Expr<'i, S, X>, Expr<'i, S, X>),
    CantNE(Expr<'i, S, X>, Expr<'i, S, X>),
    CantTextAppend(Expr<'i, S, X>, Expr<'i, S, X>),
    CantAdd(Expr<'i, S, X>, Expr<'i, S, X>),
    CantMultiply(Expr<'i, S, X>, Expr<'i, S, X>),
    NoDependentLet(Expr<'i, S, X>, Expr<'i, S, X>),
    NoDependentTypes(Expr<'i, S, X>, Expr<'i, S, X>),
}

/// A structured type error that includes context
#[derive(Debug)]
pub struct TypeError<'i, S> {
    pub context: Context<'i, Expr<'i, S, X>>,
    pub current: Expr<'i, S, X>,
    pub type_message: TypeMessage<'i, S>,
}

impl<'i, S: Clone> TypeError<'i, S> {
    pub fn new(
        context: &Context<'i, Expr<'i, S, X>>,
        current: &Expr<'i, S, X>,
        type_message: TypeMessage<'i, S>,
    ) -> Self {
        TypeError {
            context: context.clone(),
            current: current.clone(),
            type_message: type_message,
        }
    }
}

impl<'i, S: fmt::Debug> ::std::error::Error for TypeMessage<'i, S> {
    fn description(&self) -> &str {
        match *self {
            UnboundVariable => "Unbound variable",
            InvalidInputType(_) => "Invalid function input",
            InvalidOutputType(_) => "Invalid function output",
            NotAFunction(_, _) => "Not a function",
            TypeMismatch(_, _, _, _) => "Wrong type of function argument",
            _ => "Unhandled error",
        }
    }
}

impl<'i, S> fmt::Display for TypeMessage<'i, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            UnboundVariable => {
                f.write_str(include_str!("errors/UnboundVariable.txt"))
            }
            TypeMismatch(ref e0, ref e1, ref e2, ref e3) => {
                let template = include_str!("errors/TypeMismatch.txt");
                let s = template
                    .replace("$txt0", &format!("{}", e0))
                    .replace("$txt1", &format!("{}", e1))
                    .replace("$txt2", &format!("{}", e2))
                    .replace("$txt3", &format!("{}", e3));
                f.write_str(&s)
            }
            _ => f.write_str("Unhandled error message"),
        }
    }
}
