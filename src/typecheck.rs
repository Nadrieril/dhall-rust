#![allow(non_snake_case)]
use std::collections::HashSet;

use context::Context;
use core;
use core::{Expr, V, X, bx, normalize, shift, subst};
use core::{pi, app};
use core::Expr::*;
use core::Const::*;

use self::TypeMessage::*;

fn axiom<'i, S: Clone>(c: core::Const) -> Result<core::Const, TypeError<'i, S>> {
    match c {
        Type => Ok(Kind),
        Kind => Err(TypeError::new(&Context::new(), &Const(Kind), Untyped)),
    }
}

fn rule(a: core::Const, b: core::Const) -> Result<core::Const, ()> {
    match (a, b) {
        (Type, Kind) => Err(()),
        (Type, Type) => Ok(Type),
        (Kind, Kind) => Ok(Kind),
        (Kind, Type) => Ok(Type),
    }
}

fn match_vars(vl: &V, vr: &V, ctx: &[(&str, &str)]) -> bool {
    let xxs = ctx.get(0).map(|x| (x, ctx.split_at(1).1));
    match (vl, vr, xxs) {
        (&V(ref xL, nL), &V(ref xR, nR), None) => xL == xR && nL == nR,
        (&V(ref xL, 0), &V(ref xR, 0), Some((&(ref xL2, ref xR2), _))) if xL == xL2 && xR == xR2 => true,
        (&V(ref xL, nL), &V(ref xR, nR), Some((&(ref xL2, ref xR2), xs))) => {
            let nL2 = if *xL == xL2.as_ref() { nL - 1 } else { nL };
            let nR2 = if *xR == xR2.as_ref() { nR - 1 } else { nR };
            match_vars(&V(xL.clone(), nL2), &V(xR.clone(), nR2), xs)
        }
    }
}

fn prop_equal<S, T>(eL0: &Expr<S, X>, eR0: &Expr<T, X>) -> bool
    where S: Clone + ::std::fmt::Debug,
          T: Clone + ::std::fmt::Debug
{
    fn go<'i, S, T>(ctx: &mut Vec<(&'i str, &'i str)>, el: &'i Expr<'i, S, X>, er: &'i Expr<'i, T, X>) -> bool
        where S: Clone + ::std::fmt::Debug,
              T: Clone + ::std::fmt::Debug
    {
        match (el, er) {
            (&Const(Type), &Const(Type)) => true,
            (&Const(Kind), &Const(Kind)) => true,
            (&Var(ref vL), &Var(ref vR)) => match_vars(vL, vR, &*ctx),
            (&Pi(ref xL, ref tL, ref bL), &Pi(ref xR, ref tR, ref bR)) => {
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
            (&App(ref fL, ref aL), &App(ref fR, ref aR)) =>
                if go(ctx, fL, fR) { go(ctx, aL, aR) } else { false },
            (&Bool, &Bool) => true,
            (&Natural, &Natural) => true,
            (&Integer, &Integer) => true,
            (&Double, &Double) => true,
            (&Text, &Text) => true,
            (&List, &List) => true,
            (&Optional, &Optional) => true,
            (&Record(ref _ktsL0), &Record(ref _ktsR0)) => unimplemented!(),
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
            (&Union(ref _ktsL0), &Union(ref _ktsR0)) => unimplemented!(),
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
            (_, _) => false,
        }
    }
    let mut ctx = vec![];
    go::<S, T>(&mut ctx, &normalize(eL0.clone()), &normalize(eR0.clone()))
}


/// Type-check an expression and return the expression'i type if type-checking
/// suceeds or an error if type-checking fails
///
/// `type_with` does not necessarily normalize the type since full normalization
/// is not necessary for just type-checking.  If you actually care about the
/// returned type then you may want to `normalize` it afterwards.
pub fn type_with<'i, S>(ctx: &Context<'i, Expr<'i, S, X>>,
                        e: &Expr<'i, S, X>)
                        -> Result<Expr<'i, S, X>, TypeError<'i, S>>
    where S: Clone + ::std::fmt::Debug + 'i
{
    match e {
        &Const(c) => axiom(c).map(Const), //.map(Cow::Owned),
        &Var(V(ref x, n)) => {
            ctx.lookup(x, n)
                .cloned()
                //.map(Cow::Borrowed)
                .ok_or_else(|| TypeError::new(ctx, &e, UnboundVariable))
        }
        &Lam(ref x, ref tA, ref b) => {
            let ctx2 = ctx.insert(x.clone(), (**tA).clone()).map(|e| core::shift(1, V(x.clone(), 0), e.clone()));
            let tB = type_with(&ctx2, b)?;
            let p = Pi(x.clone(), tA.clone(), bx(tB));
            let _ = type_with(ctx, &p)?;
            //Ok(Cow::Owned(p))
            Ok(p)
        }
        &Pi(ref x, ref tA, ref tB) => {
            let tA2 = normalize::<S, S, X>(type_with(ctx, tA)?);
            let kA = match tA2 {
                Const(k) => k,
                _        => return Err(TypeError::new(ctx, e, InvalidInputType((**tA).clone()))),
            };

            let ctx2 = ctx.insert(x.clone(), (**tA).clone()).map(|e| core::shift(1, V(x.clone(), 0), e.clone()));
            let tB = normalize(type_with(&ctx2, tB)?);
            let kB = match tB {
                Const(k) => k,
                _        => return Err(TypeError::new(&ctx2, e, InvalidOutputType(tB))),
            };

            match rule(kA, kB) {
                Err(()) => Err(TypeError::new(ctx, e, NoDependentTypes((**tA).clone(), tB))),
                Ok(k) => Ok(Const(k)),
            }
        }
        &App(ref f, ref a) => {
            let tf = normalize(type_with(ctx, f)?);
            let (x, tA, tB) = match tf {
                Pi(x, tA, tB) => (x, tA, tB),
                _             => return Err(TypeError::new(ctx, e, NotAFunction((**f).clone(), tf))),
            };
            let tA2 = type_with(ctx, a)?;
            if prop_equal(&tA, &tA2) {
                let vx0 = V(x, 0);
                let a2  = shift::<S, S, X>( 1, vx0.clone(), (**a).clone());
                let tB2 = subst(vx0.clone(), a2, (*tB).clone());
                let tB3 = shift::<S, S, X>(-1, vx0, tB2);
                Ok(tB3)
            } else {
                let nf_A  = normalize(*tA);
                let nf_A2 = normalize(tA2);
                Err(TypeError::new(ctx, e, TypeMismatch((**f).clone(), nf_A, (**a).clone(), nf_A2)))
            }
        }
        &Let(ref f, ref mt, ref r, ref b) => {
            let tR  = type_with(ctx, r)?;
            let ttR = normalize::<S, S, X>(type_with(ctx, &tR)?);
            let kR  = match ttR {
                Const(k) => k,
                // Don't bother to provide a `let`-specific version of this error
                // message because this should never happen anyway
                _        => return Err(TypeError::new(ctx, &e, InvalidInputType(tR))),
            };

            let ctx2 = ctx.insert(f.clone(), tR.clone());
            let tB  = type_with(&ctx2, b)?;
            let ttB = normalize::<S, S, X>(type_with(ctx, &tB)?);
            let kB  = match ttB {
                Const(k) => k,
                // Don't bother to provide a `let`-specific version of this error
                // message because this should never happen anyway
                _        => return Err(TypeError::new(ctx, &e, InvalidOutputType(tB))),
            };

            if let Err(()) = rule(kR, kB) {
                return Err(TypeError::new(ctx, &e, NoDependentLet(tR, tB)));
            }

            if let &Some(ref t) = mt {
                let nf_t  = normalize((**t).clone());
                let nf_tR = normalize(tR.clone());
                if !prop_equal(&nf_tR, &nf_t) {
                    return Err(TypeError::new(ctx, &e, AnnotMismatch((**r).clone(), nf_t, nf_tR)));
                }
            }

            Ok(tB)
        }
/*
type_with ctx e@(Annot x t       ) = do
    -- This is mainly just to check that `t` is not `Kind`
    _ <- type_with ctx t

    t' <- type_with ctx x
    if prop_equal t t'
        then do
            return t
        else do
            let nf_t  = Dhall.Core.normalize t
            let nf_t' = Dhall.Core.normalize t'
            Left (TypeError ctx e (AnnotMismatch x nf_t nf_t'))
*/
        &Bool => Ok(Const(Type)),
        &BoolLit(_) => Ok(Bool),
        &BoolAnd(ref l, ref r) => {
            let tl = normalize(type_with(ctx, l)?);
            match tl {
                Bool => {}
                _    => return Err(TypeError::new(ctx, e, CantAnd((**l).clone(), tl))),
            }

            let tr = normalize(type_with(ctx, r)?);
            match tr {
                Bool => {}
                _    => return Err(TypeError::new(ctx, e, CantAnd((**r).clone(), tr))),
            }

            Ok(Bool)
        }
    /*
type_with ctx e@(BoolOr  l r     ) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantOr l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantOr r tr))

    return Bool
type_with ctx e@(BoolEQ  l r     ) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantEQ l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantEQ r tr))

    return Bool
type_with ctx e@(BoolNE  l r     ) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantNE l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Bool -> return ()
        _    -> Left (TypeError ctx e (CantNE r tr))

    return Bool
type_with ctx e@(BoolIf x y z    ) = do
    tx <- fmap Dhall.Core.normalize (type_with ctx x)
    case tx of
        Bool -> return ()
        _    -> Left (TypeError ctx e (InvalidPredicate x tx))
    ty  <- fmap Dhall.Core.normalize (type_with ctx y )
    tty <- fmap Dhall.Core.normalize (type_with ctx ty)
    case tty of
        Const Type -> return ()
        _          -> Left (TypeError ctx e (IfBranchMustBeTerm True y ty tty))

    tz <- fmap Dhall.Core.normalize (type_with ctx z)
    ttz <- fmap Dhall.Core.normalize (type_with ctx tz)
    case ttz of
        Const Type -> return ()
        _          -> Left (TypeError ctx e (IfBranchMustBeTerm False z tz ttz))

    if prop_equal ty tz
        then return ()
        else Left (TypeError ctx e (IfBranchMismatch y z ty tz))
    return ty
        */
    &Natural => Ok(Const(Type)),
    &NaturalLit(_) => Ok(Natural),
    /*
type_with _      NaturalFold       = do
    return
        (Pi "_" Natural
            (Pi "natural" (Const Type)
                (Pi "succ" (Pi "_" "natural" "natural")
                    (Pi "zero" "natural" "natural") ) ) )
type_with _      NaturalBuild      = do
    return
        (Pi "_"
            (Pi "natural" (Const Type)
                (Pi "succ" (Pi "_" "natural" "natural")
                    (Pi "zero" "natural" "natural") ) )
            Natural )
        */
    &NaturalIsZero => Ok(pi("_", Natural, Bool)),
    &NaturalEven => Ok(pi("_", Natural, Bool)),
    &NaturalOdd => Ok(pi("_", Natural, Bool)),
    /*
type_with ctx e@(NaturalPlus  l r) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Natural -> return ()
        _       -> Left (TypeError ctx e (CantAdd l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Natural -> return ()
        _       -> Left (TypeError ctx e (CantAdd r tr))
    return Natural
type_with ctx e@(NaturalTimes l r) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Natural -> return ()
        _       -> Left (TypeError ctx e (CantMultiply l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Natural -> return ()
        _       -> Left (TypeError ctx e (CantMultiply r tr))
    return Natural
    */
    &Integer => Ok(Const(Type)),
    &IntegerLit(_) => Ok(Integer),
    &Double => Ok(Const(Type)),
    &DoubleLit(_) => Ok(Double),
    &Text => Ok(Const(Type)),
    &TextLit(_) => Ok(Text),
    /*
type_with ctx e@(TextAppend l r  ) = do
    tl <- fmap Dhall.Core.normalize (type_with ctx l)
    case tl of
        Text -> return ()
        _    -> Left (TypeError ctx e (CantTextAppend l tl))

    tr <- fmap Dhall.Core.normalize (type_with ctx r)
    case tr of
        Text -> return ()
        _    -> Left (TypeError ctx e (CantTextAppend r tr))
    return Text
    */
    &List => Ok(pi("_", Const(Type), Const(Type))),
    /*
type_with ctx e@(ListLit t xs    ) = do
    s <- fmap Dhall.Core.normalize (type_with ctx t)
    case s of
        Const Type -> return ()
        _ -> Left (TypeError ctx e (InvalidListType t))
    flip Data.Vector.imapM_ xs (\i x -> do
        t' <- type_with ctx x
        if prop_equal t t'
            then return ()
            else do
                let nf_t  = Dhall.Core.normalize t
                let nf_t' = Dhall.Core.normalize t'
                Left (TypeError ctx e (InvalidListElement i nf_t x nf_t')) )
    return (App List t)
                */
    &ListBuild =>
        Ok(pi("a", Const(Type),
            pi("_",
                pi("list", Const(Type),
                    pi("cons", pi("_", "a", pi("_", "list", "list")),
                        pi("nil", "list", "list"))),
                app(List, "a")))),
    &ListFold =>
        Ok(pi("a", Const(Type),
            pi("_", app(List, "a"),
                pi("list", Const(Type),
                    pi("cons", pi("_", "a", pi("_", "list", "list")),
                        pi("nil", "list", "list")))))),
    &ListLength =>
        Ok(pi("a", Const(Type), pi("_", app(List, "a"), Natural))),
    &ListHead =>
        Ok(pi("a", Const(Type), pi("_", app(List, "a"), app(Optional, "a")))),
    &ListLast =>
        Ok(pi("a", Const(Type), pi("_", app(List, "a"), app(Optional, "a")))),
        /*
type_with _      ListIndexed       = do
    let kts = [("index", Natural), ("value", "a")]
    return
        (Pi "a" (Const Type)
            (Pi "_" (App List "a")
                (App List (Record (Data.Map.fromList kts))) ) )
type_with _      ListReverse       = do
    return (Pi "a" (Const Type) (Pi "_" (App List "a") (App List "a")))
type_with _      Optional          = do
    return (Pi "_" (Const Type) (Const Type))
type_with ctx e@(OptionalLit t xs) = do
    s <- fmap Dhall.Core.normalize (type_with ctx t)
    case s of
        Const Type -> return ()
        _ -> Left (TypeError ctx e (InvalidOptionalType t))
    let n = Data.Vector.length xs
    if 2 <= n
        then Left (TypeError ctx e (InvalidOptionalLiteral n))
        else return ()
    forM_ xs (\x -> do
        t' <- type_with ctx x
        if prop_equal t t'
            then return ()
            else do
                let nf_t  = Dhall.Core.normalize t
                let nf_t' = Dhall.Core.normalize t'
                Left (TypeError ctx e (InvalidOptionalElement nf_t x nf_t')) )
    return (App Optional t)
type_with _      OptionalFold      = do
    return
        (Pi "a" (Const Type)
            (Pi "_" (App Optional "a")
                (Pi "optional" (Const Type)
                    (Pi "just" (Pi "_" "a" "optional")
                        (Pi "nothing" "optional" "optional") ) ) ) )
type_with ctx e@(Record    kts   ) = do
    let process (k, t) = do
            s <- fmap Dhall.Core.normalize (type_with ctx t)
            case s of
                Const Type -> return ()
                _          -> Left (TypeError ctx e (InvalidFieldType k t))
    mapM_ process (Data.Map.toList kts)
    return (Const Type)
type_with ctx e@(RecordLit kvs   ) = do
    let process (k, v) = do
            t <- type_with ctx v
            s <- fmap Dhall.Core.normalize (type_with ctx t)
            case s of
                Const Type -> return ()
                _          -> Left (TypeError ctx e (InvalidField k v))
            return (k, t)
    kts <- mapM process (Data.Map.toAscList kvs)
    return (Record (Data.Map.fromAscList kts))
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
type_with ctx e@(Field r x       ) = do
    t <- fmap Dhall.Core.normalize (type_with ctx r)
    case t of
        Record kts ->
            case Data.Map.lookup x kts of
                Just t' -> return t'
                Nothing -> Left (TypeError ctx e (MissingField x t))
        _          -> Left (TypeError ctx e (NotARecord x r t))
type_with ctx   (Note s e'       ) = case type_with ctx e' of
    Left (TypeError ctx2 (Note s' e'') m) -> Left (TypeError ctx2 (Note s' e'') m)
    Left (TypeError ctx2          e''  m) -> Left (TypeError ctx2 (Note s  e'') m)
    Right r                               -> Right r
type_with _     (Embed p         ) = do
    absurd p
*/
        _ => panic!("Unimplemented typecheck case: {:?}", e),
    }
}

/// `typeOf` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
pub fn type_of<'i, S: Clone + ::std::fmt::Debug + 'i>(e: &Expr<'i, S, X>) -> Result<Expr<'i, S, X>, TypeError<'i, S>> {
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
    TypeMismatch(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    AnnotMismatch(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    Untyped,
    InvalidListElement(isize, Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    InvalidListType(Expr<'i, S, X>),
    InvalidOptionalElement(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
    InvalidOptionalLiteral(isize),
    InvalidOptionalType(Expr<'i, S, X>),
    InvalidPredicate(Expr<'i, S, X>, Expr<'i, S, X>),
    IfBranchMismatch(Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>, Expr<'i, S, X>),
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
    CantStringAppend(Expr<'i, S, X>, Expr<'i, S, X>),
    CantAdd(Expr<'i, S, X>, Expr<'i, S, X>),
    CantMultiply(Expr<'i, S, X>, Expr<'i, S, X>),
    NoDependentLet(Expr<'i, S, X>, Expr<'i, S, X>),
    NoDependentTypes(Expr<'i, S, X>, Expr<'i, S, X>),
}

/// A structured type error that includes context
#[derive(Debug)]
pub struct TypeError<'i, S> {
    context: Context<'i, Expr<'i, S, X>>,
    current: Expr<'i, S, X>,
    type_message: TypeMessage<'i, S>,
}

impl<'i, S: Clone> TypeError<'i, S> {
    pub fn new(context: &Context<'i, Expr<'i, S, X>>,
               current: &Expr<'i, S, X>,
               type_message: TypeMessage<'i, S>)
               -> Self {
        TypeError {
            context: context.clone(),
            current: current.clone(),
            type_message: type_message,
        }
    }
}
