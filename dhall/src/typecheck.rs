#![allow(non_snake_case)]
use std::collections::HashSet;
use std::fmt;

use crate::normalize::normalize;
use dhall_core;
use dhall_core::context::Context;
use dhall_core::*;
use dhall_generator as dhall;

use self::TypeMessage::*;

fn axiom<S>(c: Const) -> Result<Const, TypeError<S>> {
    use dhall_core::Const::*;
    use dhall_core::ExprF::*;
    match c {
        Type => Ok(Kind),
        Kind => Err(TypeError::new(&Context::new(), rc(Const(Kind)), Untyped)),
    }
}

fn rule(a: Const, b: Const) -> Result<Const, ()> {
    use dhall_core::Const::*;
    match (a, b) {
        (Type, Kind) => Err(()),
        (Kind, Kind) => Ok(Kind),
        (Type, Type) | (Kind, Type) => Ok(Type),
    }
}

fn match_vars(vl: &V<Label>, vr: &V<Label>, ctx: &[(Label, Label)]) -> bool {
    let mut vl = vl.clone();
    let mut vr = vr.clone();
    let mut ctx = ctx.to_vec();
    ctx.reverse();
    while let Some((xL2, xR2)) = &ctx.pop() {
        match (&vl, &vr) {
            (V(xL, 0), V(xR, 0)) if xL == xL2 && xR == xR2 => return true,
            (V(xL, nL), V(xR, nR)) => {
                let nL2 = if xL == xL2 { nL - 1 } else { *nL };
                let nR2 = if xR == xR2 { nR - 1 } else { *nR };
                vl = V(xL.clone(), nL2);
                vr = V(xR.clone(), nR2);
            }
        }
    }
    vl == vr
}

// Takes normalized expressions as input
fn prop_equal<S, T>(eL0: &Expr<S, X>, eR0: &Expr<T, X>) -> bool
where
    S: ::std::fmt::Debug,
    T: ::std::fmt::Debug,
{
    use dhall_core::ExprF::*;
    fn go<S, T>(
        ctx: &mut Vec<(Label, Label)>,
        el: &Expr<S, X>,
        er: &Expr<T, X>,
    ) -> bool
    where
        S: ::std::fmt::Debug,
        T: ::std::fmt::Debug,
    {
        match (el, er) {
            (&Const(a), &Const(b)) => a == b,
            (&Builtin(a), &Builtin(b)) => a == b,
            (&Var(ref vL), &Var(ref vR)) => match_vars(vL, vR, ctx),
            (&Pi(ref xL, ref tL, ref bL), &Pi(ref xR, ref tR, ref bR)) => {
                //ctx <- State.get
                let eq1 = go(ctx, tL.as_ref(), tR.as_ref());
                if eq1 {
                    //State.put ((xL, xR):ctx)
                    ctx.push((xL.clone(), xR.clone()));
                    let eq2 = go(ctx, bL.as_ref(), bR.as_ref());
                    //State.put ctx
                    let _ = ctx.pop();
                    eq2
                } else {
                    false
                }
            }
            (&App(ref fL, ref aL), &App(ref fR, ref aR)) => {
                go(ctx, fL.as_ref(), fR.as_ref())
                    && aL.len() == aR.len()
                    && aL
                        .iter()
                        .zip(aR.iter())
                        .all(|(aL, aR)| go(ctx, aL.as_ref(), aR.as_ref()))
            }
            (&RecordType(ref ktsL0), &RecordType(ref ktsR0)) => {
                ktsL0.len() == ktsR0.len()
                    && ktsL0.iter().zip(ktsR0.iter()).all(
                        |((kL, tL), (kR, tR))| {
                            kL == kR && go(ctx, tL.as_ref(), tR.as_ref())
                        },
                    )
            }
            (&UnionType(ref ktsL0), &UnionType(ref ktsR0)) => {
                ktsL0.len() == ktsR0.len()
                    && ktsL0.iter().zip(ktsR0.iter()).all(
                        |((kL, tL), (kR, tR))| {
                            kL == kR && go(ctx, tL.as_ref(), tR.as_ref())
                        },
                    )
            }
            (_, _) => false,
        }
    }
    let mut ctx = vec![];
    go::<S, T>(&mut ctx, eL0, eR0)
}

fn type_of_builtin<S>(b: Builtin) -> Expr<S, X> {
    use dhall_core::Builtin::*;
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
        OptionalFold => dhall::expr!(
            forall (a: Type) ->
            Optional a ->
            forall (optional: Type) ->
            forall (just: a -> optional) ->
            forall (nothing: optional) ->
            optional
        ),
        _ => panic!("Unimplemented typecheck case: {:?}", b),
    }
}

/// Type-check an expression and return the expression'i type if type-checking
/// suceeds or an error if type-checking fails
///
/// `type_with` does not necessarily normalize the type since full normalization
/// is not necessary for just type-checking.  If you actually care about the
/// returned type then you may want to `normalize` it afterwards.
pub fn type_with<S>(
    ctx: &Context<Label, SubExpr<S, X>>,
    e: SubExpr<S, X>,
) -> Result<SubExpr<S, X>, TypeError<S>>
where
    S: ::std::fmt::Debug + Clone,
{
    use dhall_core::BinOp::*;
    use dhall_core::Builtin::*;
    use dhall_core::Const::*;
    use dhall_core::ExprF::*;
    let mkerr = |msg: TypeMessage<_>| TypeError::new(ctx, e.clone(), msg);
    let ensure_const = |x: &SubExpr<_, _>, msg: TypeMessage<_>| match x.as_ref()
    {
        Const(k) => Ok(*k),
        _ => Err(mkerr(msg)),
    };
    let ensure_is_type =
        |x: SubExpr<_, _>, msg: TypeMessage<_>| match x.as_ref() {
            Const(Type) => Ok(()),
            _ => Err(mkerr(msg)),
        };

    let ret = match e.as_ref() {
        Const(c) => axiom(*c).map(Const),
        Var(V(x, n)) => match ctx.lookup(x, *n) {
            Some(e) => Ok(e.unroll()),
            None => Err(mkerr(UnboundVariable)),
        },
        Lam(x, tA, b) => {
            let ctx2 = ctx
                .insert(x.clone(), tA.clone())
                .map(|e| shift(1, &V(x.clone(), 0), e));
            let tB = normalized_type_with(&ctx2, b.clone())?;
            let p = Pi(x.clone(), tA.clone(), tB);
            let _ = normalized_type_with(ctx, rc(p.clone()))?;
            Ok(p)
        }
        Pi(x, tA, tB) => {
            let tA2 = normalized_type_with(ctx, tA.clone())?;
            let kA = ensure_const(&tA2, InvalidInputType(tA.clone()))?;

            let ctx2 = ctx
                .insert(x.clone(), tA.clone())
                .map(|e| shift(1, &V(x.clone(), 0), e));
            let tB = normalized_type_with(&ctx2, tB.clone())?;
            let kB = match tB.as_ref() {
                Const(k) => *k,
                _ => {
                    return Err(TypeError::new(
                        &ctx2,
                        e.clone(),
                        InvalidOutputType(tB),
                    ));
                }
            };

            match rule(kA, kB) {
                Err(()) => Err(mkerr(NoDependentTypes(tA.clone(), tB))),
                Ok(_) => Ok(Const(kB)),
            }
        }
        App(f, args) => {
            // Recurse on args
            let (a, tf) = match args.split_last() {
                None => return normalized_type_with(ctx, f.clone()),
                Some((a, args)) => (
                    a,
                    normalized_type_with(
                        ctx,
                        rc(App(f.clone(), args.to_vec())),
                    )?,
                ),
            };
            let (x, tA, tB) = match tf.as_ref() {
                Pi(x, tA, tB) => (x, tA, tB),
                _ => {
                    return Err(mkerr(NotAFunction(f.clone(), tf)));
                }
            };
            let tA2 = normalized_type_with(ctx, a.clone())?;
            if prop_equal(tA.as_ref(), tA2.as_ref()) {
                let vx0 = &V(x.clone(), 0);
                Ok(subst_shift(vx0, &a, &tB).unroll())
            } else {
                Err(mkerr(TypeMismatch(f.clone(), tA.clone(), a.clone(), tA2)))
            }
        }
        Let(f, mt, r, b) => {
            let r = if let Some(t) = mt {
                rc(Annot(SubExpr::clone(r), SubExpr::clone(t)))
            } else {
                SubExpr::clone(r)
            };

            let tR = normalized_type_with(ctx, r)?;
            let ttR = normalized_type_with(ctx, tR.clone())?;
            // Don't bother to provide a `let`-specific version of this error
            // message because this should never happen anyway
            let kR = ensure_const(&ttR, InvalidInputType(tR.clone()))?;

            let ctx2 = ctx.insert(f.clone(), tR.clone());
            let tB = normalized_type_with(&ctx2, b.clone())?;
            let ttB = normalized_type_with(ctx, tB.clone())?;
            // Don't bother to provide a `let`-specific version of this error
            // message because this should never happen anyway
            let kB = ensure_const(&ttB, InvalidOutputType(tB.clone()))?;

            if let Err(()) = rule(kR, kB) {
                return Err(mkerr(NoDependentLet(tR, tB)));
            }

            Ok(tB.unroll())
        }
        Annot(x, t) => {
            // This is mainly just to check that `t` is not `Kind`
            let _ = normalized_type_with(ctx, t.clone())?;

            let t2 = normalized_type_with(ctx, x.clone())?;
            let t = normalize(t.clone());
            if prop_equal(t.as_ref(), t2.as_ref()) {
                Ok(t.unroll())
            } else {
                Err(mkerr(AnnotMismatch(x.clone(), t, t2)))
            }
        }
        BoolIf(x, y, z) => {
            let tx = normalized_type_with(ctx, x.clone())?;
            match tx.as_ref() {
                Builtin(Bool) => {}
                _ => {
                    return Err(mkerr(InvalidPredicate(x.clone(), tx)));
                }
            }
            let ty = normalized_type_with(ctx, y.clone())?;
            let tty = normalized_type_with(ctx, ty.clone())?;
            ensure_is_type(
                tty.clone(),
                IfBranchMustBeTerm(true, y.clone(), ty.clone(), tty.clone()),
            )?;

            let tz = normalized_type_with(ctx, z.clone())?;
            let ttz = normalized_type_with(ctx, tz.clone())?;
            ensure_is_type(
                ttz.clone(),
                IfBranchMustBeTerm(false, z.clone(), tz.clone(), ttz.clone()),
            )?;

            if !prop_equal(ty.as_ref(), tz.as_ref()) {
                return Err(mkerr(IfBranchMismatch(
                    y.clone(),
                    z.clone(),
                    ty,
                    tz,
                )));
            }
            Ok(ty.unroll())
        }
        EmptyListLit(t) => {
            let s = normalized_type_with(ctx, t.clone())?;
            ensure_is_type(s, InvalidListType(t.clone()))?;
            let t = normalize(SubExpr::clone(t));
            Ok(dhall::expr!(List t))
        }
        NEListLit(xs) => {
            let mut iter = xs.iter().enumerate();
            let (_, first_x) = iter.next().unwrap();
            let t = normalized_type_with(ctx, first_x.clone())?;
            let s = normalized_type_with(ctx, t.clone())?;
            ensure_is_type(s, InvalidListType(t.clone()))?;
            for (i, x) in iter {
                let t2 = normalized_type_with(ctx, x.clone())?;
                if !prop_equal(t.as_ref(), t2.as_ref()) {
                    return Err(mkerr(InvalidListElement(i, t, x.clone(), t2)));
                }
            }
            Ok(dhall::expr!(List t))
        }
        EmptyOptionalLit(t) => {
            let s = normalized_type_with(ctx, t.clone())?;
            ensure_is_type(s, InvalidOptionalType(t.clone()))?;
            let t = normalize(t.clone());
            Ok(dhall::expr!(Optional t))
        }
        NEOptionalLit(x) => {
            let t = normalized_type_with(ctx, x.clone())?;
            let s = normalized_type_with(ctx, t.clone())?;
            ensure_is_type(s, InvalidOptionalType(t.clone()))?;
            Ok(dhall::expr!(Optional t))
        }
        RecordType(kts) => {
            for (k, t) in kts {
                let s = normalized_type_with(ctx, t.clone())?;
                ensure_is_type(s, InvalidFieldType(k.clone(), t.clone()))?;
            }
            Ok(Const(Type))
        }
        RecordLit(kvs) => {
            let kts = kvs
                .iter()
                .map(|(k, v)| {
                    let t = normalized_type_with(ctx, v.clone())?;
                    let s = normalized_type_with(ctx, t.clone())?;
                    ensure_is_type(s, InvalidField(k.clone(), v.clone()))?;
                    Ok((k.clone(), t))
                })
                .collect::<Result<_, _>>()?;
            Ok(RecordType(kts))
        }
        Field(r, x) => {
            let t = normalized_type_with(ctx, r.clone())?;
            match t.as_ref() {
                RecordType(kts) => match kts.get(x) {
                    Some(e) => Ok(e.unroll()),
                    None => Err(mkerr(MissingField(x.clone(), t.clone()))),
                },
                _ => Err(mkerr(NotARecord(x.clone(), r.clone(), t.clone()))),
            }
        }
        Builtin(b) => Ok(type_of_builtin(*b)),
        BoolLit(_) => Ok(Builtin(Bool)),
        NaturalLit(_) => Ok(Builtin(Natural)),
        IntegerLit(_) => Ok(Builtin(Integer)),
        DoubleLit(_) => Ok(Builtin(Double)),
        TextLit(_) => Ok(Builtin(Text)),
        BinOp(o, l, r) => {
            let t = match o {
                BoolAnd => Bool,
                BoolOr => Bool,
                BoolEQ => Bool,
                BoolNE => Bool,
                NaturalPlus => Natural,
                NaturalTimes => Natural,
                TextAppend => Text,
                _ => panic!("Unimplemented typecheck case: {:?}", e),
            };
            let tl = normalized_type_with(ctx, l.clone())?;
            match tl.as_ref() {
                Builtin(lt) if *lt == t => {}
                _ => return Err(mkerr(BinOpTypeMismatch(*o, l.clone(), tl))),
            }

            let tr = normalized_type_with(ctx, r.clone())?;
            match tr.as_ref() {
                Builtin(rt) if *rt == t => {}
                _ => return Err(mkerr(BinOpTypeMismatch(*o, r.clone(), tr))),
            }

            Ok(Builtin(t))
        }
        Embed(p) => match *p {},
        _ => panic!("Unimplemented typecheck case: {:?}", e),
    }?;
    Ok(rc(ret))
}

pub fn normalized_type_with<S>(
    ctx: &Context<Label, SubExpr<S, X>>,
    e: SubExpr<S, X>,
) -> Result<SubExpr<S, X>, TypeError<S>>
where
    S: ::std::fmt::Debug + Clone,
{
    Ok(normalize(type_with(ctx, e)?))
}

/// `typeOf` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
pub fn type_of<S: ::std::fmt::Debug + Clone>(
    e: SubExpr<S, X>,
) -> Result<SubExpr<S, X>, TypeError<S>> {
    let ctx = Context::new();
    normalized_type_with(&ctx, e) //.map(|e| e.into_owned())
}

/// The specific type error
#[derive(Debug)]
pub enum TypeMessage<S> {
    UnboundVariable,
    InvalidInputType(SubExpr<S, X>),
    InvalidOutputType(SubExpr<S, X>),
    NotAFunction(SubExpr<S, X>, SubExpr<S, X>),
    TypeMismatch(SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    AnnotMismatch(SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    Untyped,
    InvalidListElement(usize, SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    InvalidListType(SubExpr<S, X>),
    InvalidOptionalElement(SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    InvalidOptionalLiteral(usize),
    InvalidOptionalType(SubExpr<S, X>),
    InvalidPredicate(SubExpr<S, X>, SubExpr<S, X>),
    IfBranchMismatch(
        SubExpr<S, X>,
        SubExpr<S, X>,
        SubExpr<S, X>,
        SubExpr<S, X>,
    ),
    IfBranchMustBeTerm(bool, SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    InvalidField(Label, SubExpr<S, X>),
    InvalidFieldType(Label, SubExpr<S, X>),
    InvalidAlternative(Label, SubExpr<S, X>),
    InvalidAlternativeType(Label, SubExpr<S, X>),
    DuplicateAlternative(Label),
    MustCombineARecord(SubExpr<S, X>, SubExpr<S, X>),
    FieldCollision(Label),
    MustMergeARecord(SubExpr<S, X>, SubExpr<S, X>),
    MustMergeUnion(SubExpr<S, X>, SubExpr<S, X>),
    UnusedHandler(HashSet<Label>),
    MissingHandler(HashSet<Label>),
    HandlerInputTypeMismatch(Label, SubExpr<S, X>, SubExpr<S, X>),
    HandlerOutputTypeMismatch(Label, SubExpr<S, X>, SubExpr<S, X>),
    HandlerNotAFunction(Label, SubExpr<S, X>),
    NotARecord(Label, SubExpr<S, X>, SubExpr<S, X>),
    MissingField(Label, SubExpr<S, X>),
    BinOpTypeMismatch(BinOp, SubExpr<S, X>, SubExpr<S, X>),
    NoDependentLet(SubExpr<S, X>, SubExpr<S, X>),
    NoDependentTypes(SubExpr<S, X>, SubExpr<S, X>),
}

/// A structured type error that includes context
#[derive(Debug)]
pub struct TypeError<S> {
    pub context: Context<Label, SubExpr<S, X>>,
    pub current: SubExpr<S, X>,
    pub type_message: TypeMessage<S>,
}

impl<S> TypeError<S> {
    pub fn new(
        context: &Context<Label, SubExpr<S, X>>,
        current: SubExpr<S, X>,
        type_message: TypeMessage<S>,
    ) -> Self {
        TypeError {
            context: context.clone(),
            current: current,
            type_message,
        }
    }
}

impl<S: fmt::Debug> ::std::error::Error for TypeMessage<S> {
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

impl<S> fmt::Display for TypeMessage<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            UnboundVariable => {
                f.write_str(include_str!("errors/UnboundVariable.txt"))
            }
            TypeMismatch(e0, e1, e2, e3) => {
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
