use std::collections::HashMap;

use crate::semantics::NzEnv;
use crate::semantics::{
    Binder, BuiltinClosure, Closure, TyExpr, TyExprKind, Value, ValueKind,
};
use crate::syntax::{
    BinOp, Builtin, Const, ExprKind, InterpolatedTextContents,
};
use crate::Normalized;

pub(crate) fn apply_any(f: Value, a: Value, ty: &Value) -> ValueKind {
    let f_borrow = f.kind();
    match &*f_borrow {
        ValueKind::LamClosure { closure, .. } => {
            closure.apply(a).to_whnf_check_type(ty)
        }
        ValueKind::AppliedBuiltin(closure) => {
            closure.apply(a, f.get_type().unwrap(), ty)
        }
        ValueKind::UnionConstructor(l, kts, uniont) => ValueKind::UnionLit(
            l.clone(),
            a,
            kts.clone(),
            uniont.clone(),
            f.get_type().unwrap(),
        ),
        _ => {
            drop(f_borrow);
            ValueKind::PartialExpr(ExprKind::App(f, a))
        }
    }
}

pub(crate) fn squash_textlit(
    elts: impl Iterator<Item = InterpolatedTextContents<Value>>,
) -> Vec<InterpolatedTextContents<Value>> {
    use std::mem::replace;
    use InterpolatedTextContents::{Expr, Text};

    fn inner(
        elts: impl Iterator<Item = InterpolatedTextContents<Value>>,
        crnt_str: &mut String,
        ret: &mut Vec<InterpolatedTextContents<Value>>,
    ) {
        for contents in elts {
            match contents {
                Text(s) => crnt_str.push_str(&s),
                Expr(e) => {
                    let e_borrow = e.kind();
                    match &*e_borrow {
                        ValueKind::TextLit(elts2) => {
                            inner(elts2.iter().cloned(), crnt_str, ret)
                        }
                        _ => {
                            drop(e_borrow);
                            if !crnt_str.is_empty() {
                                ret.push(Text(replace(crnt_str, String::new())))
                            }
                            ret.push(Expr(e.clone()))
                        }
                    }
                }
            }
        }
    }

    let mut crnt_str = String::new();
    let mut ret = Vec::new();
    inner(elts, &mut crnt_str, &mut ret);
    if !crnt_str.is_empty() {
        ret.push(Text(replace(&mut crnt_str, String::new())))
    }
    ret
}

pub(crate) fn merge_maps<K, V, F, Err>(
    map1: &HashMap<K, V>,
    map2: &HashMap<K, V>,
    mut f: F,
) -> Result<HashMap<K, V>, Err>
where
    F: FnMut(&K, &V, &V) -> Result<V, Err>,
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    let mut kvs = HashMap::new();
    for (x, v2) in map2 {
        let newv = if let Some(v1) = map1.get(x) {
            f(x, v1, v2)?
        } else {
            v2.clone()
        };
        kvs.insert(x.clone(), newv);
    }
    for (x, v1) in map1 {
        // Insert only if key not already present
        kvs.entry(x.clone()).or_insert_with(|| v1.clone());
    }
    Ok(kvs)
}

// Small helper enum to avoid repetition
enum Ret<'a> {
    ValueKind(ValueKind),
    Value(Value),
    ValueRef(&'a Value),
    Expr(ExprKind<Value, Normalized>),
}

fn apply_binop<'a>(
    o: BinOp,
    x: &'a Value,
    y: &'a Value,
    ty: &Value,
) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, Equivalence, ListAppend, NaturalPlus,
        NaturalTimes, RecursiveRecordMerge, RecursiveRecordTypeMerge,
        RightBiasedRecordMerge, TextAppend,
    };
    use ValueKind::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, RecordType,
        TextLit,
    };
    let x_borrow = x.kind();
    let y_borrow = y.kind();
    Some(match (o, &*x_borrow, &*y_borrow) {
        (BoolAnd, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolAnd, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolAnd, BoolLit(false), _) => Ret::ValueKind(BoolLit(false)),
        (BoolAnd, _, BoolLit(false)) => Ret::ValueKind(BoolLit(false)),
        (BoolAnd, _, _) if x == y => Ret::ValueRef(x),
        (BoolOr, BoolLit(true), _) => Ret::ValueKind(BoolLit(true)),
        (BoolOr, _, BoolLit(true)) => Ret::ValueKind(BoolLit(true)),
        (BoolOr, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolOr, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolOr, _, _) if x == y => Ret::ValueRef(x),
        (BoolEQ, BoolLit(true), _) => Ret::ValueRef(y),
        (BoolEQ, _, BoolLit(true)) => Ret::ValueRef(x),
        (BoolEQ, BoolLit(x), BoolLit(y)) => Ret::ValueKind(BoolLit(x == y)),
        (BoolEQ, _, _) if x == y => Ret::ValueKind(BoolLit(true)),
        (BoolNE, BoolLit(false), _) => Ret::ValueRef(y),
        (BoolNE, _, BoolLit(false)) => Ret::ValueRef(x),
        (BoolNE, BoolLit(x), BoolLit(y)) => Ret::ValueKind(BoolLit(x != y)),
        (BoolNE, _, _) if x == y => Ret::ValueKind(BoolLit(false)),

        (NaturalPlus, NaturalLit(0), _) => Ret::ValueRef(y),
        (NaturalPlus, _, NaturalLit(0)) => Ret::ValueRef(x),
        (NaturalPlus, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueKind(NaturalLit(x + y))
        }
        (NaturalTimes, NaturalLit(0), _) => Ret::ValueKind(NaturalLit(0)),
        (NaturalTimes, _, NaturalLit(0)) => Ret::ValueKind(NaturalLit(0)),
        (NaturalTimes, NaturalLit(1), _) => Ret::ValueRef(y),
        (NaturalTimes, _, NaturalLit(1)) => Ret::ValueRef(x),
        (NaturalTimes, NaturalLit(x), NaturalLit(y)) => {
            Ret::ValueKind(NaturalLit(x * y))
        }

        (ListAppend, EmptyListLit(_), _) => Ret::ValueRef(y),
        (ListAppend, _, EmptyListLit(_)) => Ret::ValueRef(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => Ret::ValueKind(
            NEListLit(xs.iter().chain(ys.iter()).cloned().collect()),
        ),

        (TextAppend, TextLit(x), _) if x.is_empty() => Ret::ValueRef(y),
        (TextAppend, _, TextLit(y)) if y.is_empty() => Ret::ValueRef(x),
        (TextAppend, TextLit(x), TextLit(y)) => Ret::ValueKind(TextLit(
            squash_textlit(x.iter().chain(y.iter()).cloned()),
        )),
        (TextAppend, TextLit(x), _) => {
            use std::iter::once;
            let y = InterpolatedTextContents::Expr(y.clone());
            Ret::ValueKind(TextLit(squash_textlit(
                x.iter().cloned().chain(once(y)),
            )))
        }
        (TextAppend, _, TextLit(y)) => {
            use std::iter::once;
            let x = InterpolatedTextContents::Expr(x.clone());
            Ret::ValueKind(TextLit(squash_textlit(
                once(x).chain(y.iter().cloned()),
            )))
        }

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            Ret::ValueKind(RecordLit(kvs))
        }

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let ty_borrow = ty.kind();
            let kts = match &*ty_borrow {
                RecordType(kts) => kts,
                _ => unreachable!("Internal type error"),
            };
            let kvs = merge_maps::<_, _, _, !>(kvs1, kvs2, |k, v1, v2| {
                Ok(Value::from_kind_and_type(
                    ValueKind::PartialExpr(ExprKind::BinOp(
                        RecursiveRecordMerge,
                        v1.clone(),
                        v2.clone(),
                    )),
                    kts.get(k).expect("Internal type error").clone(),
                ))
            })?;
            Ret::ValueKind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, RecordType(kts_x), RecordType(kts_y)) => {
            let kts = merge_maps::<_, _, _, !>(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Value, r: &Value| {
                    Ok(Value::from_kind_and_type(
                        ValueKind::PartialExpr(ExprKind::BinOp(
                            RecursiveRecordTypeMerge,
                            l.clone(),
                            r.clone(),
                        )),
                        ty.clone(),
                    ))
                },
            )?;
            Ret::ValueKind(RecordType(kts))
        }

        (Equivalence, _, _) => {
            Ret::ValueKind(ValueKind::Equivalence(x.clone(), y.clone()))
        }

        _ => return None,
    })
}

pub(crate) fn normalize_one_layer(
    expr: ExprKind<Value, Normalized>,
    ty: &Value,
    env: &NzEnv,
) -> ValueKind {
    use ValueKind::{
        BoolLit, DoubleLit, EmptyOptionalLit, IntegerLit, NEListLit,
        NEOptionalLit, NaturalLit, RecordLit, RecordType, TextLit,
        UnionConstructor, UnionLit, UnionType,
    };

    let ret = match expr {
        ExprKind::Import(_) => unreachable!(
            "There should remain no imports in a resolved expression"
        ),
        // Those cases have already been completely handled in the typechecking phase (using
        // `RetWhole`), so they won't appear here.
        ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Embed(_)
        | ExprKind::Var(_) => {
            unreachable!("This case should have been handled in typecheck")
        }
        ExprKind::Annot(x, _) => Ret::Value(x),
        ExprKind::Const(c) => Ret::Value(Value::from_const(c)),
        ExprKind::Builtin(b) => Ret::Value(Value::from_builtin_env(b, env)),
        ExprKind::Assert(_) => Ret::Expr(expr),
        ExprKind::App(v, a) => Ret::Value(v.app(a)),
        ExprKind::BoolLit(b) => Ret::ValueKind(BoolLit(b)),
        ExprKind::NaturalLit(n) => Ret::ValueKind(NaturalLit(n)),
        ExprKind::IntegerLit(n) => Ret::ValueKind(IntegerLit(n)),
        ExprKind::DoubleLit(n) => Ret::ValueKind(DoubleLit(n)),
        ExprKind::SomeLit(e) => Ret::ValueKind(NEOptionalLit(e)),
        ExprKind::EmptyListLit(t) => {
            let arg = match &*t.kind() {
                ValueKind::AppliedBuiltin(BuiltinClosure {
                    b: Builtin::List,
                    args,
                    ..
                }) if args.len() == 1 => args[0].clone(),
                _ => panic!("internal type error"),
            };
            Ret::ValueKind(ValueKind::EmptyListLit(arg))
        }
        ExprKind::NEListLit(elts) => {
            Ret::ValueKind(NEListLit(elts.into_iter().collect()))
        }
        ExprKind::RecordLit(kvs) => {
            Ret::ValueKind(RecordLit(kvs.into_iter().collect()))
        }
        ExprKind::RecordType(kvs) => {
            Ret::ValueKind(RecordType(kvs.into_iter().collect()))
        }
        ExprKind::UnionType(kvs) => {
            Ret::ValueKind(UnionType(kvs.into_iter().collect()))
        }
        ExprKind::TextLit(elts) => {
            use InterpolatedTextContents::Expr;
            let elts: Vec<_> = squash_textlit(elts.into_iter());
            // Simplify bare interpolation
            if let [Expr(th)] = elts.as_slice() {
                Ret::Value(th.clone())
            } else {
                Ret::ValueKind(TextLit(elts))
            }
        }
        ExprKind::BoolIf(ref b, ref e1, ref e2) => {
            let b_borrow = b.kind();
            match &*b_borrow {
                BoolLit(true) => Ret::ValueRef(e1),
                BoolLit(false) => Ret::ValueRef(e2),
                _ => {
                    let e1_borrow = e1.kind();
                    let e2_borrow = e2.kind();
                    match (&*e1_borrow, &*e2_borrow) {
                        // Simplify `if b then True else False`
                        (BoolLit(true), BoolLit(false)) => Ret::ValueRef(b),
                        _ if e1 == e2 => Ret::ValueRef(e1),
                        _ => {
                            drop(b_borrow);
                            drop(e1_borrow);
                            drop(e2_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
            }
        }
        ExprKind::BinOp(o, ref x, ref y) => match apply_binop(o, x, y, ty) {
            Some(ret) => ret,
            None => Ret::Expr(expr),
        },

        ExprKind::Projection(_, ref ls) if ls.is_empty() => {
            Ret::ValueKind(RecordLit(HashMap::new()))
        }
        ExprKind::Projection(ref v, ref ls) => {
            let v_borrow = v.kind();
            match &*v_borrow {
                RecordLit(kvs) => Ret::ValueKind(RecordLit(
                    ls.iter()
                        .filter_map(|l| {
                            kvs.get(l).map(|x| (l.clone(), x.clone()))
                        })
                        .collect(),
                )),
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::Field(ref v, ref l) => {
            let v_borrow = v.kind();
            match &*v_borrow {
                RecordLit(kvs) => match kvs.get(l) {
                    Some(r) => Ret::Value(r.clone()),
                    None => {
                        drop(v_borrow);
                        Ret::Expr(expr)
                    }
                },
                UnionType(kts) => Ret::ValueKind(UnionConstructor(
                    l.clone(),
                    kts.clone(),
                    v.get_type().unwrap(),
                )),
                _ => {
                    drop(v_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::ProjectionByExpr(_, _) => {
            unimplemented!("selection by expression")
        }
        ExprKind::Completion(_, _) => unimplemented!("record completion"),

        ExprKind::Merge(ref handlers, ref variant, _) => {
            let handlers_borrow = handlers.kind();
            let variant_borrow = variant.kind();
            match (&*handlers_borrow, &*variant_borrow) {
                (RecordLit(kvs), UnionConstructor(l, _, _)) => match kvs.get(l)
                {
                    Some(h) => Ret::Value(h.clone()),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        Ret::Expr(expr)
                    }
                },
                (RecordLit(kvs), UnionLit(l, v, _, _, _)) => match kvs.get(l) {
                    Some(h) => Ret::Value(h.app(v.clone())),
                    None => {
                        drop(handlers_borrow);
                        drop(variant_borrow);
                        Ret::Expr(expr)
                    }
                },
                (RecordLit(kvs), EmptyOptionalLit(_)) => {
                    match kvs.get(&"None".into()) {
                        Some(h) => Ret::Value(h.clone()),
                        None => {
                            drop(handlers_borrow);
                            drop(variant_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
                (RecordLit(kvs), NEOptionalLit(v)) => {
                    match kvs.get(&"Some".into()) {
                        Some(h) => Ret::Value(h.app(v.clone())),
                        None => {
                            drop(handlers_borrow);
                            drop(variant_borrow);
                            Ret::Expr(expr)
                        }
                    }
                }
                _ => {
                    drop(handlers_borrow);
                    drop(variant_borrow);
                    Ret::Expr(expr)
                }
            }
        }
        ExprKind::ToMap(_, _) => unimplemented!("toMap"),
    };

    match ret {
        Ret::ValueKind(v) => v,
        Ret::Value(v) => v.to_whnf_check_type(ty),
        Ret::ValueRef(v) => v.to_whnf_check_type(ty),
        Ret::Expr(expr) => ValueKind::PartialExpr(expr),
    }
}

/// Normalize a ValueKind into WHNF
pub(crate) fn normalize_whnf(v: ValueKind, ty: &Value) -> ValueKind {
    match v {
        ValueKind::AppliedBuiltin(closure) => closure.ensure_whnf(ty),
        ValueKind::PartialExpr(e) => normalize_one_layer(e, ty, &NzEnv::new()),
        ValueKind::Thunk(th) => th.eval().kind().clone(),
        ValueKind::TextLit(elts) => {
            ValueKind::TextLit(squash_textlit(elts.into_iter()))
        }
        // All other cases are already in WHNF
        v => v,
    }
}

/// Normalize a TyExpr into WHNF
pub(crate) fn normalize_tyexpr_whnf(tye: &TyExpr, env: &NzEnv) -> Value {
    let ty = match tye.get_type() {
        Ok(ty) => ty,
        Err(_) => return Value::from_const(Const::Sort),
    };

    let kind = match tye.kind() {
        TyExprKind::Var(var) => return env.lookup_val(var),
        TyExprKind::Expr(ExprKind::Lam(binder, annot, body)) => {
            let annot = annot.eval(env);
            ValueKind::LamClosure {
                binder: Binder::new(binder.clone()),
                annot: annot.clone(),
                closure: Closure::new(annot, env, body.clone()),
            }
        }
        TyExprKind::Expr(ExprKind::Pi(binder, annot, body)) => {
            let annot = annot.eval(env);
            let closure = Closure::new(annot.clone(), env, body.clone());
            ValueKind::PiClosure {
                binder: Binder::new(binder.clone()),
                annot,
                closure,
            }
        }
        TyExprKind::Expr(ExprKind::Let(_, None, val, body)) => {
            let val = val.eval(env);
            return body.eval(&env.insert_value(val));
        }
        TyExprKind::Expr(e) => {
            let e = e.map_ref(|tye| tye.eval(env));
            normalize_one_layer(e, &ty, env)
        }
    };

    // dbg!(tye.kind(), env, &kind);
    Value::from_kind_and_type_whnf(kind, ty)
}
