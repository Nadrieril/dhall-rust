#![allow(non_snake_case)]
use dhall_core::core::*;
use dhall_generator::dhall_expr;
use std::fmt;

/// Reduce an expression to its normal form, performing beta reduction
///
/// `normalize` does not type-check the expression.  You may want to type-check
/// expressions before normalizing them since normalization can convert an
/// ill-typed expression into a well-typed expression.
///
/// However, `normalize` will not fail if the expression is ill-typed and will
/// leave ill-typed sub-expressions unevaluated.
///
pub fn normalize<S, T, A>(e: &Expr<Label, S, A>) -> Expr<Label, T, A>
where
    S: Clone + fmt::Debug,
    T: Clone + fmt::Debug,
    A: Clone + fmt::Debug,
{
    use dhall_core::BinOp::*;
    use dhall_core::Builtin::*;
    use dhall_core::Expr::*;
    match e {
        // Matches that don't normalize everything right away
        Let(f, _, r, b) => {
            let r2 = shift::<_, S, _>(1, &V(f.clone(), 0), r);
            let b2 = subst::<_, S, _>(&V(f.clone(), 0), &r2, b);
            let b3 = shift::<_, T, _>(-1, &V(f.clone(), 0), &b2);
            normalize(&b3)
        }
        BoolIf(b, t, f) => match normalize(b) {
            BoolLit(true) => normalize(t),
            BoolLit(false) => normalize(f),
            b2 => BoolIf(bx(b2), bx(normalize(t)), bx(normalize(f))),
        },
        Annot(x, _) => normalize(x),
        Note(_, e) => normalize(e),
        App(f, a) => match normalize::<S, T, A>(f) {
            Lam(x, _A, b) => {
                // Beta reduce
                let vx0 = &V(x, 0);
                let a2 = shift::<S, S, A>(1, vx0, a);
                let b2 = subst::<S, T, A>(vx0, &a2, &b);
                let b3 = shift::<S, T, A>(-1, vx0, &b2);
                normalize(&b3)
            }
            f2 => match (f2, normalize::<S, T, A>(a)) {
                // fold/build fusion for `List`
                (App(box Builtin(ListBuild), _), App(box App(box Builtin(ListFold), _), box e2)) |
                (App(box Builtin(ListFold), _), App(box App(box Builtin(ListBuild), _), box e2)) |

                // fold/build fusion for `Optional`
                (App(box Builtin(OptionalBuild), _), App(box App(box Builtin(OptionalFold), _), box e2)) |
                (App(box Builtin(OptionalFold), _), App(box App(box Builtin(OptionalBuild), _), box e2)) |

                // fold/build fusion for `Natural`
                (Builtin(NaturalBuild), App(box Builtin(NaturalFold), box e2)) |
                (Builtin(NaturalFold), App(box Builtin(NaturalBuild), box e2)) => normalize(&e2),

            /*
                App (App (App (App NaturalFold (NaturalLit n0)) _) succ') zero ->
                    normalize (go n0)
                  where
                    go !0 = zero
                    go !n = App succ' (go (n - 1))
                App NaturalBuild k
                    | check     -> NaturalLit n
                    | otherwise -> App f' a'
                  where
                    labeled =
                        normalize (App (App (App k Natural) "Succ") "Zero")

                    n = go 0 labeled
                      where
                        go !m (App (Var "Succ") e') = go (m + 1) e'
                        go !m (Var "Zero")          = m
                        go !_  _                    = internalError text
                    check = go labeled
                      where
                        go (App (Var "Succ") e') = go e'
                        go (Var "Zero")          = True
                        go  _                    = False
                        */
                (Builtin(NaturalIsZero), NaturalLit(n)) => BoolLit(n == 0),
                (Builtin(NaturalEven), NaturalLit(n)) => BoolLit(n % 2 == 0),
                (Builtin(NaturalOdd), NaturalLit(n)) => BoolLit(n % 2 != 0),
                (Builtin(NaturalToInteger), NaturalLit(n)) => IntegerLit(n as isize),
                (Builtin(NaturalShow), NaturalLit(n)) => TextLit(n.to_string()),
                (App(box Builtin(ListBuild), a0), k) => {
                    let k = bx(k);
                    let a1 = bx(shift(1, &V("a".into(), 0), &a0));
                    normalize(&dhall_expr!(k (List a0) (λ(a : a0) -> λ(as : List a1) -> [ a ] # as) ([] : List a0)))
                }
                (App(box App(box App(box App(box Builtin(ListFold), _), box ListLit(_, xs)), _), cons), nil) => {
                    let e2: Expr<_, _, _> = xs.into_iter().rev().fold(nil, |y, ys| {
                        let y = bx(y);
                        let ys = bx(ys);
                        dhall_expr!(cons y ys)
                    });
                    normalize(&e2)
                }
                (App(f, x_), ListLit(t, ys)) => match *f {
                    Builtin(ListLength) =>
                        NaturalLit(ys.len()),
                    Builtin(ListHead) =>
                        normalize(&OptionalLit(t, ys.into_iter().take(1).collect())),
                    Builtin(ListLast) =>
                        normalize(&OptionalLit(t, ys.into_iter().last().into_iter().collect())),
                    Builtin(ListReverse) => {
                        let mut xs = ys;
                        xs.reverse();
                        normalize(&ListLit(t, xs))
                    }
                    _ => app(App(f, x_), ListLit(t, ys)),
                },
                /*
                App (App ListIndexed _) (ListLit t xs) ->
                    normalize (ListLit t' (fmap adapt (Data.Vector.indexed xs)))
                  where
                    t' = Record (Data.Map.fromList kts)
                      where
                        kts = [ ("index", Natural)
                              , ("value", t)
                              ]
                    adapt (n, x) = RecordLit (Data.Map.fromList kvs)
                      where
                        kvs = [ ("index", NaturalLit (fromIntegral n))
                              , ("value", x)
                              ]
            */
                (App(box App(box App(box App(box Builtin(OptionalFold), _), box OptionalLit(_, xs)), _), just), nothing) => {
                    let e2: Expr<_, _, _> = xs.into_iter().fold(nothing, |y, _| {
                        let y = bx(y);
                        dhall_expr!(just y)
                    });
                    normalize(&e2)
                }
                (App(box Builtin(OptionalBuild), a0), g) => {
                    let g = bx(g);
                    normalize(&dhall_expr!((g (Optional a0)) (λ(x: a0) -> [x] :  Optional a0) ([] :  Optional a0)))
                }
                (f2, a2) => app(f2, a2),
            },
        },

        // Normalize everything else before matching
        e => {
            match e.map_shallow(
                normalize,
                |_| unreachable!(),
                |x| x.clone(),
                |x| x.clone(),
            ) {
                BinOp(BoolAnd, box BoolLit(x), box BoolLit(y)) => {
                    BoolLit(x && y)
                }
                BinOp(BoolOr, box BoolLit(x), box BoolLit(y)) => {
                    BoolLit(x || y)
                }
                BinOp(BoolEQ, box BoolLit(x), box BoolLit(y)) => {
                    BoolLit(x == y)
                }
                BinOp(BoolNE, box BoolLit(x), box BoolLit(y)) => {
                    BoolLit(x != y)
                }
                BinOp(NaturalPlus, box NaturalLit(x), box NaturalLit(y)) => {
                    NaturalLit(x + y)
                }
                BinOp(NaturalTimes, box NaturalLit(x), box NaturalLit(y)) => {
                    NaturalLit(x * y)
                }
                BinOp(TextAppend, box TextLit(x), box TextLit(y)) => {
                    TextLit(x + &y)
                }
                BinOp(ListAppend, box ListLit(t1, xs), box ListLit(t2, ys)) => {
                    // Drop type annotation if the result is nonempty
                    let t = if xs.len() == 0 && ys.len() == 0 {
                        t1.or(t2)
                    } else {
                        None
                    };
                    let xs = xs.into_iter();
                    let ys = ys.into_iter();
                    ListLit(t, xs.chain(ys).collect())
                }
                // Merge(_x, _y, _t) => unimplemented!(),
                Field(box RecordLit(kvs), x) => match kvs.get(&x) {
                    Some(r) => r.clone(),
                    None => Field(bx(RecordLit(kvs)), x),
                },
                e => e,
            }
        }
    }
}
