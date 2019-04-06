#![allow(non_snake_case)]
use std::collections::HashSet;
use std::fmt;

use crate::expr::*;
use dhall_core;
use dhall_core::context::Context;
use dhall_core::*;
use dhall_generator as dhall;

use self::TypeMessage::*;

impl Resolved {
    pub fn typecheck(self) -> Result<Typed, TypeError<X>> {
        // let typ = Type(Box::new(Normalized(crate::typecheck::type_of(
        //     self.0.clone(),
        // )?)));
        // Ok(Typed(self.0, typ))
        let typ = crate::typecheck::type_of_(self.0.clone())?;
        Ok(typ)
    }
}
impl Typed {
    fn as_expr(&self) -> &SubExpr<X, X> {
        &self.0
    }
    pub fn get_type(&self) -> &Type {
        &self.1
    }
}
impl Normalized {
    pub fn get_type(&self) -> &Type {
        &self.1
    }
    fn into_type(self) -> Type {
        crate::expr::Type(TypeInternal::Expr(Box::new(self)))
    }
}
impl Type {
    // pub fn as_expr(&self) -> &Normalized {
    //     &*self.0
    // }
    fn as_expr(&self) -> &SubExpr<X, X> {
        &self.as_normalized().0
    }
    fn as_normalized(&self) -> &Normalized {
        use TypeInternal::*;
        match &self.0 {
            Expr(e) => &e,
            Universe(_) => unimplemented!(),
        }
    }
    pub fn get_type(&self) -> &Type {
        self.as_normalized().get_type()
    }
}

const TYPE_OF_SORT: crate::expr::Type =
    crate::expr::Type(TypeInternal::Universe(4));

fn rule(a: Const, b: Const) -> Result<Const, ()> {
    use dhall_core::Const::*;
    match (a, b) {
        (_, Type) => Ok(Type),
        (Kind, Kind) => Ok(Kind),
        (Sort, Sort) => Ok(Sort),
        (Sort, Kind) => Ok(Sort),
        _ => Err(()),
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

fn ensure_equal<'a, S, F1, F2>(
    x: &'a Type,
    y: &'a Type,
    mkerr: F1,
    mkmsg: F2,
) -> Result<(), TypeError<S>>
where
    S: std::fmt::Debug,
    F1: FnOnce(TypeMessage<S>) -> TypeError<S>,
    F2: FnOnce() -> TypeMessage<S>,
{
    if prop_equal(x.as_expr().as_ref(), y.as_expr().as_ref()) {
        Ok(())
    } else {
        Err(mkerr(mkmsg()))
    }
}

/// Type-check an expression and return the expression's type if type-checking
/// succeeds or an error if type-checking fails
///
/// `type_with` normalizes the type since while type-checking. It expects the
/// context to contain only normalized expressions.
pub fn type_with(
    ctx: &Context<Label, SubExpr<X, X>>,
    e: SubExpr<X, X>,
) -> Result<Typed, TypeError<X>> {
    use dhall_core::BinOp::*;
    use dhall_core::Builtin::*;
    use dhall_core::Const::*;
    use dhall_core::ExprF::*;
    let mkerr = |msg: TypeMessage<_>| TypeError::new(ctx, e.clone(), msg);
    let ensure_const =
        |x: &crate::expr::Type, msg: TypeMessage<_>| match x.as_expr().as_ref()
        {
            Const(k) => Ok(*k),
            _ => Err(mkerr(msg)),
        };
    let ensure_is_type =
        |x: &crate::expr::Type, msg: TypeMessage<_>| match x.as_expr().as_ref()
        {
            Const(Type) => Ok(()),
            _ => Err(mkerr(msg)),
        };

    let mktype =
        |ctx, x: SubExpr<X, X>| Ok(type_with(ctx, x)?.normalize().into_type());

    enum Ret {
        RetType(crate::expr::Type),
        RetExpr(Expr<X, X>),
    }
    use Ret::*;
    let ret = match e.as_ref() {
        Lam(x, t, b) => {
            let t2 = mktype(ctx, t.clone())?;
            let ctx2 = ctx
                .insert(x.clone(), t2.as_expr().clone())
                .map(|e| shift(1, &V(x.clone(), 0), e));
            let b = type_with(&ctx2, b.clone())?;
            let _ = type_with(
                ctx,
                rc(Pi(x.clone(), t.clone(), b.get_type().as_expr().clone())),
            )?;
            Ok(RetExpr(Pi(
                x.clone(),
                t2.as_expr().clone(),
                b.get_type().as_expr().clone(),
            )))
        }
        Pi(x, tA, tB) => {
            let tA = mktype(ctx, tA.clone())?;
            let kA = ensure_const(
                tA.get_type(),
                InvalidInputType(tA.as_expr().clone()),
            )?;

            let ctx2 = ctx
                .insert(x.clone(), tA.as_expr().clone())
                .map(|e| shift(1, &V(x.clone(), 0), e));
            let tB = type_with(&ctx2, tB.clone())?;
            let kB = match tB.get_type().as_expr().as_ref() {
                Const(k) => *k,
                _ => {
                    return Err(TypeError::new(
                        &ctx2,
                        e.clone(),
                        InvalidOutputType(tB.get_type().clone()),
                    ));
                }
            };

            match rule(kA, kB) {
                Err(()) => Err(mkerr(NoDependentTypes(
                    tA.as_expr().clone(),
                    tB.get_type().clone(),
                ))),
                Ok(k) => Ok(RetExpr(Const(k))),
            }
        }
        Let(f, mt, r, b) => {
            let r = if let Some(t) = mt {
                rc(Annot(SubExpr::clone(r), SubExpr::clone(t)))
            } else {
                SubExpr::clone(r)
            };

            let r = type_with(ctx, r)?;
            // Don't bother to provide a `let`-specific version of this error
            // message because this should never happen anyway
            let kR = ensure_const(
                r.get_type().get_type(),
                InvalidInputType(r.get_type().as_expr().clone()),
            )?;

            let ctx2 = ctx.insert(f.clone(), r.get_type().as_expr().clone());
            let b = type_with(&ctx2, b.clone())?;
            // Don't bother to provide a `let`-specific version of this error
            // message because this should never happen anyway
            let kB = ensure_const(
                b.get_type().get_type(),
                InvalidOutputType(b.get_type().clone()),
            )?;

            if let Err(()) = rule(kR, kB) {
                return Err(mkerr(NoDependentLet(
                    r.get_type().as_expr().clone(),
                    b.get_type().as_expr().clone(),
                )));
            }

            Ok(RetType(b.get_type().clone()))
        }
        _ => match e
            .as_ref()
            .traverse_ref_simple(|e| type_with(ctx, e.clone()))?
        {
            Lam(_, _, _) => unreachable!(),
            Pi(_, _, _) => unreachable!(),
            Let(_, _, _, _) => unreachable!(),
            Const(Type) => Ok(RetExpr(Const(Kind))),
            Const(Kind) => Ok(RetExpr(Const(Sort))),
            Const(Sort) => Ok(RetType(TYPE_OF_SORT)),
            Var(V(x, n)) => match ctx.lookup(&x, n) {
                Some(e) => Ok(RetExpr(e.unroll())),
                None => Err(mkerr(UnboundVariable)),
            },
            App(f, args) => {
                let mut iter = args.into_iter();
                let mut seen_args: Vec<SubExpr<_, _>> = vec![];
                let mut tf = f.get_type().clone();
                while let Some(a) = iter.next() {
                    seen_args.push(a.0.clone());
                    let (x, tx, tb) = match tf.as_expr().as_ref() {
                        Pi(x, tx, tb) => (x, tx, tb),
                        _ => {
                            return Err(mkerr(NotAFunction(
                                rc(App(f.0.clone(), seen_args)),
                                tf,
                            )));
                        }
                    };
                    let tx = mktype(ctx, tx.clone())?;
                    ensure_equal(&tx, a.get_type(), mkerr, || {
                        TypeMismatch(
                            rc(App(f.0.clone(), seen_args.clone())),
                            tx.clone(),
                            a.clone(),
                        )
                    })?;
                    tf = mktype(ctx, subst_shift(&V(x.clone(), 0), &a.0, &tb))?;
                }
                Ok(RetType(tf))
            }
            Annot(x, t) => {
                let t = t.normalize().into_type();
                ensure_equal(&t, x.get_type(), mkerr, || {
                    AnnotMismatch(x.clone(), t.clone())
                })?;
                Ok(RetType(x.get_type().clone()))
            }
            BoolIf(x, y, z) => {
                ensure_equal(
                    x.get_type(),
                    &mktype(ctx, rc(Builtin(Bool)))?,
                    mkerr,
                    || InvalidPredicate(x.clone()),
                )?;
                ensure_is_type(
                    y.get_type().get_type(),
                    IfBranchMustBeTerm(true, y.clone()),
                )?;

                ensure_is_type(
                    z.get_type().get_type(),
                    IfBranchMustBeTerm(false, z.clone()),
                )?;

                ensure_equal(y.get_type(), z.get_type(), mkerr, || {
                    IfBranchMismatch(y.clone(), z.clone())
                })?;

                Ok(RetType(y.get_type().clone()))
            }
            EmptyListLit(t) => {
                ensure_is_type(t.get_type(), InvalidListType(t.0.clone()))?;
                let t = t.normalize().0;
                Ok(RetExpr(dhall::expr!(List t)))
            }
            NEListLit(xs) => {
                let mut iter = xs.into_iter().enumerate();
                let (_, x) = iter.next().unwrap();
                ensure_is_type(
                    x.get_type().get_type(),
                    InvalidListType(x.get_type().as_expr().clone()),
                )?;
                for (i, y) in iter {
                    ensure_equal(x.get_type(), y.get_type(), mkerr, || {
                        InvalidListElement(
                            i,
                            x.get_type().as_expr().clone(),
                            y.clone(),
                        )
                    })?;
                }
                let t = x.get_type().as_expr().clone();
                Ok(RetExpr(dhall::expr!(List t)))
            }
            EmptyOptionalLit(t) => {
                ensure_is_type(t.get_type(), InvalidOptionalType(t.0.clone()))?;
                let t = t.normalize().0;
                Ok(RetExpr(dhall::expr!(Optional t)))
            }
            NEOptionalLit(x) => {
                ensure_is_type(
                    x.get_type().get_type(),
                    InvalidOptionalType(x.get_type().as_expr().clone()),
                )?;
                let t = x.get_type().as_expr().clone();
                Ok(RetExpr(dhall::expr!(Optional t)))
            }
            RecordType(kts) => {
                for (k, t) in kts {
                    ensure_is_type(
                        t.get_type(),
                        InvalidFieldType(k.clone(), t.clone()),
                    )?;
                }
                Ok(RetExpr(Const(Type)))
            }
            RecordLit(kvs) => {
                let kts = kvs
                    .into_iter()
                    .map(|(k, v)| {
                        ensure_is_type(
                            v.get_type().get_type(),
                            InvalidField(k.clone(), v.clone()),
                        )?;
                        Ok((k.clone(), v.get_type().as_expr().clone()))
                    })
                    .collect::<Result<_, _>>()?;
                Ok(RetExpr(RecordType(kts)))
            }
            Field(r, x) => match r.get_type().as_expr().as_ref() {
                RecordType(kts) => match kts.get(&x) {
                    Some(e) => Ok(RetExpr(e.unroll())),
                    None => Err(mkerr(MissingField(x.clone(), r.clone()))),
                },
                _ => Err(mkerr(NotARecord(x.clone(), r.clone()))),
            },
            Builtin(b) => Ok(RetExpr(type_of_builtin(b))),
            BoolLit(_) => Ok(RetExpr(Builtin(Bool))),
            NaturalLit(_) => Ok(RetExpr(Builtin(Natural))),
            IntegerLit(_) => Ok(RetExpr(Builtin(Integer))),
            DoubleLit(_) => Ok(RetExpr(Builtin(Double))),
            // TODO: check type of interpolations
            TextLit(_) => Ok(RetExpr(Builtin(Text))),
            BinOp(o, l, r) => {
                let t = mktype(
                    ctx,
                    rc(Builtin(match o {
                        BoolAnd => Bool,
                        BoolOr => Bool,
                        BoolEQ => Bool,
                        BoolNE => Bool,
                        NaturalPlus => Natural,
                        NaturalTimes => Natural,
                        TextAppend => Text,
                        _ => panic!("Unimplemented typecheck case: {:?}", e),
                    })),
                )?;

                ensure_equal(l.get_type(), &t, mkerr, || {
                    BinOpTypeMismatch(o, l.clone())
                })?;

                ensure_equal(r.get_type(), &t, mkerr, || {
                    BinOpTypeMismatch(o, r.clone())
                })?;

                Ok(RetType(t))
            }
            Embed(p) => match p {},
            _ => panic!("Unimplemented typecheck case: {:?}", e),
        },
    }?;
    match ret {
        RetExpr(ret) => Ok(Typed(e, mktype(ctx, rc(ret))?)),
        RetType(typ) => Ok(Typed(e, typ)),
    }
}

/// `typeOf` is the same as `type_with` with an empty context, meaning that the
/// expression must be closed (i.e. no free variables), otherwise type-checking
/// will fail.
pub fn type_of(e: SubExpr<X, X>) -> Result<SubExpr<X, X>, TypeError<X>> {
    let ctx = Context::new();
    type_with(&ctx, e).map(|e| e.get_type().as_expr().clone())
}

pub fn type_of_(e: SubExpr<X, X>) -> Result<Typed, TypeError<X>> {
    let ctx = Context::new();
    type_with(&ctx, e)
}

/// The specific type error
#[derive(Debug)]
pub enum TypeMessage<S> {
    UnboundVariable,
    InvalidInputType(SubExpr<S, X>),
    InvalidOutputType(crate::expr::Type),
    NotAFunction(SubExpr<S, X>, crate::expr::Type),
    TypeMismatch(SubExpr<S, X>, crate::expr::Type, Typed),
    AnnotMismatch(Typed, crate::expr::Type),
    Untyped,
    InvalidListElement(usize, SubExpr<S, X>, Typed),
    InvalidListType(SubExpr<S, X>),
    InvalidOptionalElement(SubExpr<S, X>, SubExpr<S, X>, SubExpr<S, X>),
    InvalidOptionalLiteral(usize),
    InvalidOptionalType(SubExpr<S, X>),
    InvalidPredicate(Typed),
    IfBranchMismatch(Typed, Typed),
    IfBranchMustBeTerm(bool, Typed),
    InvalidField(Label, Typed),
    InvalidFieldType(Label, Typed),
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
    NotARecord(Label, Typed),
    MissingField(Label, Typed),
    BinOpTypeMismatch(BinOp, Typed),
    NoDependentLet(SubExpr<S, X>, SubExpr<S, X>),
    NoDependentTypes(SubExpr<S, X>, crate::expr::Type),
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
            TypeMismatch(_, _, _) => "Wrong type of function argument",
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
            TypeMismatch(e0, e1, e2) => {
                let template = include_str!("errors/TypeMismatch.txt");
                let s = template
                    .replace("$txt0", &format!("{}", e0))
                    .replace("$txt1", &format!("{}", e1.as_expr()))
                    .replace("$txt2", &format!("{}", e2.as_expr()))
                    .replace("$txt3", &format!("{}", e2.get_type().as_expr()));
                f.write_str(&s)
            }
            _ => f.write_str("Unhandled error message"),
        }
    }
}
