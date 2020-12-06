use std::collections::{BTreeMap, HashMap};
use std::convert::TryInto;

use crate::operations::{BinOp, OpKind};
use crate::semantics::{
    nze, skip_resolve_expr, typecheck, Hir, HirKind, Nir, NirKind, NzEnv,
    VarEnv,
};
use crate::syntax::Const::Type;
use crate::syntax::{
    Const, Expr, ExprKind, InterpolatedText, InterpolatedTextContents, Label,
    NaiveDouble, NumKind, Span, UnspannedExpr, V,
};

/// Built-ins
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    Bool,
    Natural,
    Integer,
    Double,
    Text,
    List,
    Optional,
    OptionalNone,
    NaturalBuild,
    NaturalFold,
    NaturalIsZero,
    NaturalEven,
    NaturalOdd,
    NaturalToInteger,
    NaturalShow,
    NaturalSubtract,
    IntegerToDouble,
    IntegerShow,
    IntegerNegate,
    IntegerClamp,
    DoubleShow,
    ListBuild,
    ListFold,
    ListLength,
    ListHead,
    ListLast,
    ListIndexed,
    ListReverse,
    TextShow,
    TextReplace,
}

impl Builtin {
    pub fn parse(s: &str) -> Option<Self> {
        use Builtin::*;
        match s {
            "Bool" => Some(Bool),
            "Natural" => Some(Natural),
            "Integer" => Some(Integer),
            "Double" => Some(Double),
            "Text" => Some(Text),
            "List" => Some(List),
            "Optional" => Some(Optional),
            "None" => Some(OptionalNone),
            "Natural/build" => Some(NaturalBuild),
            "Natural/fold" => Some(NaturalFold),
            "Natural/isZero" => Some(NaturalIsZero),
            "Natural/even" => Some(NaturalEven),
            "Natural/odd" => Some(NaturalOdd),
            "Natural/toInteger" => Some(NaturalToInteger),
            "Natural/show" => Some(NaturalShow),
            "Natural/subtract" => Some(NaturalSubtract),
            "Integer/toDouble" => Some(IntegerToDouble),
            "Integer/show" => Some(IntegerShow),
            "Integer/negate" => Some(IntegerNegate),
            "Integer/clamp" => Some(IntegerClamp),
            "Double/show" => Some(DoubleShow),
            "List/build" => Some(ListBuild),
            "List/fold" => Some(ListFold),
            "List/length" => Some(ListLength),
            "List/head" => Some(ListHead),
            "List/last" => Some(ListLast),
            "List/indexed" => Some(ListIndexed),
            "List/reverse" => Some(ListReverse),
            "Text/show" => Some(TextShow),
            "Text/replace" => Some(TextReplace),
            _ => None,
        }
    }
}

/// A partially applied builtin.
/// Invariant: the evaluation of the given args must not be able to progress further
#[derive(Debug, Clone)]
pub struct BuiltinClosure<'cx> {
    env: NzEnv<'cx>,
    b: Builtin,
    /// Arguments applied to the closure so far.
    args: Vec<Nir<'cx>>,
}

impl<'cx> BuiltinClosure<'cx> {
    pub fn new(b: Builtin, env: NzEnv<'cx>) -> NirKind<'cx> {
        apply_builtin(b, Vec::new(), env)
    }
    pub fn apply(&self, a: Nir<'cx>) -> NirKind<'cx> {
        use std::iter::once;
        let args = self.args.iter().cloned().chain(once(a)).collect();
        apply_builtin(self.b, args, self.env.clone())
    }
    pub fn to_hirkind(&self, venv: VarEnv) -> HirKind<'cx> {
        HirKind::Expr(self.args.iter().fold(
            ExprKind::Builtin(self.b),
            |acc, v| {
                ExprKind::Op(OpKind::App(
                    Hir::new(HirKind::Expr(acc), Span::Artificial),
                    v.to_hir(venv),
                ))
            },
        ))
    }
}

pub fn rc(x: UnspannedExpr) -> Expr {
    Expr::new(x, Span::Artificial)
}

// Ad-hoc macro to help construct the types of builtins
macro_rules! make_type {
    (Type) => { rc(ExprKind::Const(Const::Type)) };
    (Bool) => { rc(ExprKind::Builtin(Builtin::Bool)) };
    (Natural) => { rc(ExprKind::Builtin(Builtin::Natural)) };
    (Integer) => { rc(ExprKind::Builtin(Builtin::Integer)) };
    (Double) => { rc(ExprKind::Builtin(Builtin::Double)) };
    (Text) => { rc(ExprKind::Builtin(Builtin::Text)) };
    ($var:ident) => {
        rc(ExprKind::Var(V(stringify!($var).into(), 0)))
    };
    (Optional $ty:ident) => {
        rc(ExprKind::Op(OpKind::App(
            rc(ExprKind::Builtin(Builtin::Optional)),
            make_type!($ty)
        )))
    };
    (List $($rest:tt)*) => {
        rc(ExprKind::Op(OpKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            make_type!($($rest)*)
        )))
    };
    ({ $($label:ident : $ty:ident),* }) => {{
        let mut kts = BTreeMap::new();
        $(
            kts.insert(
                Label::from(stringify!($label)),
                make_type!($ty),
            );
        )*
        rc(ExprKind::RecordType(kts))
    }};
    ($ty:ident -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            "_".into(),
            make_type!($ty),
            make_type!($($rest)*)
        ))
    };
    (($($arg:tt)*) -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            "_".into(),
            make_type!($($arg)*),
            make_type!($($rest)*)
        ))
    };
    (forall ($var:ident : $($ty:tt)*) -> $($rest:tt)*) => {
        rc(ExprKind::Pi(
            stringify!($var).into(),
            make_type!($($ty)*),
            make_type!($($rest)*)
        ))
    };
}

pub fn type_of_builtin<'cx>(b: Builtin) -> Hir<'cx> {
    use Builtin::*;
    let expr = match b {
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
        TextReplace => make_type!(
            forall (needle: Text) ->
            forall (replacement: Text) ->
            forall (haystack: Text) ->
            Text
        ),
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

        OptionalNone => make_type!(
            forall (A: Type) -> Optional A
        ),
    };
    skip_resolve_expr(&expr).unwrap()
}

// Ad-hoc macro to help construct closures
macro_rules! make_closure {
    (var($var:ident)) => {{
        rc(ExprKind::Var(V(
            Label::from(stringify!($var)).into(),
            0
        )))
    }};
    (λ($var:tt : $($ty:tt)*) -> $($body:tt)*) => {{
        let var = Label::from(stringify!($var));
        let ty = make_closure!($($ty)*);
        let body = make_closure!($($body)*);
        rc(ExprKind::Lam(var, ty, body))
    }};
    (Type) => {
        rc(ExprKind::Const(Type))
    };
    (Natural) => {
        rc(ExprKind::Builtin(Builtin::Natural))
    };
    (List $($ty:tt)*) => {{
        let ty = make_closure!($($ty)*);
        rc(ExprKind::Op(OpKind::App(
            rc(ExprKind::Builtin(Builtin::List)),
            ty
        )))
    }};
    (Some($($v:tt)*)) => {
        rc(ExprKind::SomeLit(
            make_closure!($($v)*)
        ))
    };
    (1 + $($v:tt)*) => {
        rc(ExprKind::Op(OpKind::BinOp(
            BinOp::NaturalPlus,
            make_closure!($($v)*),
            rc(ExprKind::Num(NumKind::Natural(1)))
        )))
    };
    ([ $($head:tt)* ] # $($tail:tt)*) => {{
        let head = make_closure!($($head)*);
        let tail = make_closure!($($tail)*);
        rc(ExprKind::Op(OpKind::BinOp(
            BinOp::ListAppend,
            rc(ExprKind::NEListLit(vec![head])),
            tail,
        )))
    }};
}

#[allow(clippy::cognitive_complexity)]
fn apply_builtin<'cx>(
    b: Builtin,
    args: Vec<Nir<'cx>>,
    env: NzEnv<'cx>,
) -> NirKind<'cx> {
    let cx = env.cx();
    use NirKind::*;
    use NumKind::{Bool, Double, Integer, Natural};

    // Small helper enum
    enum Ret<'cx> {
        NirKind(NirKind<'cx>),
        Nir(Nir<'cx>),
        DoneAsIs,
    }
    let make_closure = |e| {
        typecheck(cx, &skip_resolve_expr(&e).unwrap())
            .unwrap()
            .eval(env.clone())
    };

    let ret = match (b, args.as_slice()) {
        (Builtin::Bool, [])
        | (Builtin::Natural, [])
        | (Builtin::Integer, [])
        | (Builtin::Double, [])
        | (Builtin::Text, []) => Ret::NirKind(BuiltinType(b)),
        (Builtin::Optional, [t]) => Ret::NirKind(OptionalType(t.clone())),
        (Builtin::List, [t]) => Ret::NirKind(ListType(t.clone())),

        (Builtin::OptionalNone, [t]) => {
            Ret::NirKind(EmptyOptionalLit(t.clone()))
        }
        (Builtin::NaturalIsZero, [n]) => match &*n.kind() {
            Num(Natural(n)) => Ret::NirKind(Num(Bool(*n == 0))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalEven, [n]) => match &*n.kind() {
            Num(Natural(n)) => Ret::NirKind(Num(Bool(*n % 2 == 0))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalOdd, [n]) => match &*n.kind() {
            Num(Natural(n)) => Ret::NirKind(Num(Bool(*n % 2 != 0))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalToInteger, [n]) => match &*n.kind() {
            Num(Natural(n)) => Ret::NirKind(Num(Integer(*n as i64))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalShow, [n]) => match &*n.kind() {
            Num(Natural(n)) => Ret::Nir(Nir::from_text(n)),
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalSubtract, [a, b]) => match (&*a.kind(), &*b.kind()) {
            (Num(Natural(a)), Num(Natural(b))) => {
                Ret::NirKind(Num(Natural(if b > a { b - a } else { 0 })))
            }
            (Num(Natural(0)), _) => Ret::Nir(b.clone()),
            (_, Num(Natural(0))) => Ret::NirKind(Num(Natural(0))),
            _ if a == b => Ret::NirKind(Num(Natural(0))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::IntegerShow, [n]) => match &*n.kind() {
            Num(Integer(n)) => {
                let s = if *n < 0 {
                    n.to_string()
                } else {
                    format!("+{}", n)
                };
                Ret::Nir(Nir::from_text(s))
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::IntegerToDouble, [n]) => match &*n.kind() {
            Num(Integer(n)) => {
                Ret::NirKind(Num(Double(NaiveDouble::from(*n as f64))))
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::IntegerNegate, [n]) => match &*n.kind() {
            Num(Integer(n)) => Ret::NirKind(Num(Integer(-n))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::IntegerClamp, [n]) => match &*n.kind() {
            Num(Integer(n)) => {
                Ret::NirKind(Num(Natural((*n).try_into().unwrap_or(0))))
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::DoubleShow, [n]) => match &*n.kind() {
            Num(Double(n)) => Ret::Nir(Nir::from_text(n)),
            _ => Ret::DoneAsIs,
        },
        (Builtin::TextShow, [v]) => match &*v.kind() {
            TextLit(tlit) => {
                if let Some(s) = tlit.as_text() {
                    // Printing InterpolatedText takes care of all the escaping
                    let txt: InterpolatedText<Expr> =
                        std::iter::once(InterpolatedTextContents::Text(s))
                            .collect();
                    Ret::Nir(Nir::from_text(txt))
                } else {
                    Ret::DoneAsIs
                }
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::TextReplace, [needle, replacement, haystack]) => {
            // Helper to match a Nir as a text literal
            fn nir_to_string(n: &Nir) -> Option<String> {
                match &*n.kind() {
                    TextLit(n_lit) => n_lit.as_text(),
                    _ => None,
                }
            }

            // The needle needs to be fully evaluated as Text otherwise no
            // progress can be made
            match nir_to_string(needle) {
                // When the needle is empty the haystack is returned untouched
                Some(n) if n.is_empty() => Ret::Nir(haystack.clone()),
                Some(n) => {
                    // The haystack needs to be fully evaluated as Text otherwise no
                    // progress can be made
                    if let Some(h) = nir_to_string(haystack) {
                        // Fast case when replacement is fully evaluated
                        if let Some(r) = nir_to_string(replacement) {
                            Ret::Nir(Nir::from_text(h.replace(&n, &r)))
                        } else {
                            use itertools::Itertools;

                            let parts = h.split(&n).map(|s| {
                                InterpolatedTextContents::Text(s.to_string())
                            });
                            let replacement = InterpolatedTextContents::Expr(
                                replacement.clone(),
                            );

                            Ret::Nir(Nir::from_kind(NirKind::TextLit(
                                nze::nir::TextLit::new(
                                    parts.intersperse(replacement),
                                ),
                            )))
                        }
                    } else {
                        Ret::DoneAsIs
                    }
                }
                _ => Ret::DoneAsIs,
            }
        }
        (Builtin::ListLength, [_, l]) => match &*l.kind() {
            EmptyListLit(_) => Ret::NirKind(Num(Natural(0))),
            NEListLit(xs) => Ret::NirKind(Num(Natural(xs.len() as u64))),
            _ => Ret::DoneAsIs,
        },
        (Builtin::ListHead, [_, l]) => match &*l.kind() {
            EmptyListLit(n) => Ret::NirKind(EmptyOptionalLit(n.clone())),
            NEListLit(xs) => {
                Ret::NirKind(NEOptionalLit(xs.iter().next().unwrap().clone()))
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::ListLast, [_, l]) => match &*l.kind() {
            EmptyListLit(n) => Ret::NirKind(EmptyOptionalLit(n.clone())),
            NEListLit(xs) => Ret::NirKind(NEOptionalLit(
                xs.iter().rev().next().unwrap().clone(),
            )),
            _ => Ret::DoneAsIs,
        },
        (Builtin::ListReverse, [_, l]) => match &*l.kind() {
            EmptyListLit(n) => Ret::NirKind(EmptyListLit(n.clone())),
            NEListLit(xs) => {
                Ret::NirKind(NEListLit(xs.iter().rev().cloned().collect()))
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::ListIndexed, [t, l]) => {
            match l.kind() {
                EmptyListLit(_) | NEListLit(_) => {
                    // Construct the returned record type: { index: Natural, value: t }
                    let mut kts = HashMap::new();
                    kts.insert(
                        "index".into(),
                        Nir::from_builtin(cx, Builtin::Natural),
                    );
                    kts.insert("value".into(), t.clone());
                    let t = Nir::from_kind(RecordType(kts));

                    // Construct the new list, with added indices
                    let list = match l.kind() {
                        EmptyListLit(_) => EmptyListLit(t),
                        NEListLit(xs) => NEListLit(
                            xs.iter()
                                .enumerate()
                                .map(|(i, e)| {
                                    let mut kvs = HashMap::new();
                                    kvs.insert(
                                        "index".into(),
                                        Nir::from_kind(Num(Natural(i as u64))),
                                    );
                                    kvs.insert("value".into(), e.clone());
                                    Nir::from_kind(RecordLit(kvs))
                                })
                                .collect(),
                        ),
                        _ => unreachable!(),
                    };
                    Ret::NirKind(list)
                }
                _ => Ret::DoneAsIs,
            }
        }
        (Builtin::ListBuild, [t, f]) => {
            let list_t = Nir::from_builtin(cx, Builtin::List).app(t.clone());
            Ret::Nir(
                f.app(list_t)
                    .app(
                        make_closure(make_closure!(
                            λ(T : Type) ->
                            λ(a : var(T)) ->
                            λ(as : List var(T)) ->
                            [ var(a) ] # var(as)
                        ))
                        .app(t.clone()),
                    )
                    .app(EmptyListLit(t.clone()).into_nir()),
            )
        }
        (Builtin::ListFold, [_, l, _, cons, nil]) => match &*l.kind() {
            EmptyListLit(_) => Ret::Nir(nil.clone()),
            NEListLit(xs) => {
                let mut v = nil.clone();
                for x in xs.iter().cloned().rev() {
                    v = cons.app(x).app(v);
                }
                Ret::Nir(v)
            }
            _ => Ret::DoneAsIs,
        },
        (Builtin::NaturalBuild, [f]) => Ret::Nir(
            f.app(Nir::from_builtin(cx, Builtin::Natural))
                .app(make_closure(make_closure!(
                    λ(x : Natural) ->
                    1 + var(x)
                )))
                .app(Num(Natural(0)).into_nir()),
        ),

        (Builtin::NaturalFold, [n, t, succ, zero]) => match &*n.kind() {
            Num(Natural(0)) => Ret::Nir(zero.clone()),
            Num(Natural(n)) => {
                let fold = Nir::from_builtin(cx, Builtin::NaturalFold)
                    .app(Num(Natural(n - 1)).into_nir())
                    .app(t.clone())
                    .app(succ.clone())
                    .app(zero.clone());
                Ret::Nir(succ.app(fold))
            }
            _ => Ret::DoneAsIs,
        },
        _ => Ret::DoneAsIs,
    };
    match ret {
        Ret::NirKind(v) => v,
        Ret::Nir(v) => v.kind().clone(),
        Ret::DoneAsIs => AppliedBuiltin(BuiltinClosure { b, args, env }),
    }
}

impl<'cx> std::cmp::PartialEq for BuiltinClosure<'cx> {
    fn eq(&self, other: &Self) -> bool {
        self.b == other.b && self.args == other.args
    }
}
impl<'cx> std::cmp::Eq for BuiltinClosure<'cx> {}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Builtin::*;
        f.write_str(match *self {
            Bool => "Bool",
            Natural => "Natural",
            Integer => "Integer",
            Double => "Double",
            Text => "Text",
            List => "List",
            Optional => "Optional",
            OptionalNone => "None",
            NaturalBuild => "Natural/build",
            NaturalFold => "Natural/fold",
            NaturalIsZero => "Natural/isZero",
            NaturalEven => "Natural/even",
            NaturalOdd => "Natural/odd",
            NaturalToInteger => "Natural/toInteger",
            NaturalShow => "Natural/show",
            NaturalSubtract => "Natural/subtract",
            IntegerToDouble => "Integer/toDouble",
            IntegerNegate => "Integer/negate",
            IntegerClamp => "Integer/clamp",
            IntegerShow => "Integer/show",
            DoubleShow => "Double/show",
            ListBuild => "List/build",
            ListFold => "List/fold",
            ListLength => "List/length",
            ListHead => "List/head",
            ListLast => "List/last",
            ListIndexed => "List/indexed",
            ListReverse => "List/reverse",
            TextShow => "Text/show",
            TextReplace => "Text/replace",
        })
    }
}
