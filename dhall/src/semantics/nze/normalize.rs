use itertools::Itertools;
use std::collections::HashMap;

use crate::semantics::NzEnv;
use crate::semantics::{
    Binder, BuiltinClosure, Closure, Hir, HirKind, TextLit, Value, ValueKind,
};
use crate::syntax::{BinOp, Builtin, ExprKind, InterpolatedTextContents};
use crate::Normalized;

pub(crate) fn apply_any(f: Value, a: Value) -> ValueKind {
    match f.kind() {
        ValueKind::LamClosure { closure, .. } => {
            closure.apply(a).kind().clone()
        }
        ValueKind::AppliedBuiltin(closure) => closure.apply(a),
        ValueKind::UnionConstructor(l, kts) => {
            ValueKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => ValueKind::PartialExpr(ExprKind::App(f, a)),
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
                Expr(e) => match e.kind() {
                    ValueKind::TextLit(elts2) => {
                        inner(elts2.iter().cloned(), crnt_str, ret)
                    }
                    _ => {
                        if !crnt_str.is_empty() {
                            ret.push(Text(replace(crnt_str, String::new())))
                        }
                        ret.push(Expr(e.clone()))
                    }
                },
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

fn apply_binop<'a>(o: BinOp, x: &'a Value, y: &'a Value) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, Equivalence, ListAppend, NaturalPlus,
        NaturalTimes, RecursiveRecordMerge, RecursiveRecordTypeMerge,
        RightBiasedRecordMerge, TextAppend,
    };
    use ValueKind::{
        BoolLit, EmptyListLit, NEListLit, NaturalLit, RecordLit, RecordType,
    };
    Some(match (o, x.kind(), y.kind()) {
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

        (TextAppend, ValueKind::TextLit(x), _) if x.is_empty() => {
            Ret::ValueRef(y)
        }
        (TextAppend, _, ValueKind::TextLit(y)) if y.is_empty() => {
            Ret::ValueRef(x)
        }
        (TextAppend, ValueKind::TextLit(x), ValueKind::TextLit(y)) => {
            Ret::ValueKind(ValueKind::TextLit(x.concat(y)))
        }
        (TextAppend, ValueKind::TextLit(x), _) => Ret::ValueKind(
            ValueKind::TextLit(x.concat(&TextLit::interpolate(y.clone()))),
        ),
        (TextAppend, _, ValueKind::TextLit(y)) => Ret::ValueKind(
            ValueKind::TextLit(TextLit::interpolate(x.clone()).concat(y)),
        ),

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
        (RightBiasedRecordMerge, _, _) if x == y => Ret::ValueRef(y),

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::ValueRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::ValueRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps::<_, _, _, !>(kvs1, kvs2, |_, v1, v2| {
                Ok(Value::from_partial_expr(ExprKind::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                )))
            })?;
            Ret::ValueKind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, RecordType(kts_x), RecordType(kts_y)) => {
            let kts = merge_maps::<_, _, _, !>(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Value, r: &Value| {
                    Ok(Value::from_partial_expr(ExprKind::BinOp(
                        RecursiveRecordTypeMerge,
                        l.clone(),
                        r.clone(),
                    )))
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
    env: &NzEnv,
) -> ValueKind {
    use ValueKind::{
        BoolLit, DoubleLit, EmptyListLit, EmptyOptionalLit, IntegerLit,
        NEListLit, NEOptionalLit, NaturalLit, PartialExpr, RecordLit,
        RecordType, UnionConstructor, UnionLit, UnionType,
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
            let arg = match t.kind() {
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
            let tlit = TextLit::new(elts.into_iter());
            // Simplify bare interpolation
            if let Some(v) = tlit.as_single_expr() {
                Ret::Value(v.clone())
            } else {
                Ret::ValueKind(ValueKind::TextLit(tlit))
            }
        }
        ExprKind::BoolIf(ref b, ref e1, ref e2) => {
            match b.kind() {
                BoolLit(true) => Ret::ValueRef(e1),
                BoolLit(false) => Ret::ValueRef(e2),
                _ => {
                    match (e1.kind(), e2.kind()) {
                        // Simplify `if b then True else False`
                        (BoolLit(true), BoolLit(false)) => Ret::ValueRef(b),
                        _ if e1 == e2 => Ret::ValueRef(e1),
                        _ => Ret::Expr(expr),
                    }
                }
            }
        }
        ExprKind::BinOp(o, ref x, ref y) => match apply_binop(o, x, y) {
            Some(ret) => ret,
            None => Ret::Expr(expr),
        },

        ExprKind::Projection(_, ref ls) if ls.is_empty() => {
            Ret::ValueKind(RecordLit(HashMap::new()))
        }
        ExprKind::Projection(ref v, ref ls) => match v.kind() {
            RecordLit(kvs) => Ret::ValueKind(RecordLit(
                ls.iter()
                    .filter_map(|l| kvs.get(l).map(|x| (l.clone(), x.clone())))
                    .collect(),
            )),
            PartialExpr(ExprKind::Projection(v2, _)) => {
                return normalize_one_layer(
                    ExprKind::Projection(v2.clone(), ls.clone()),
                    env,
                )
            }
            _ => Ret::Expr(expr),
        },
        ExprKind::Field(ref v, ref l) => match v.kind() {
            RecordLit(kvs) => match kvs.get(l) {
                Some(r) => Ret::Value(r.clone()),
                None => Ret::Expr(expr),
            },
            UnionType(kts) => {
                Ret::ValueKind(UnionConstructor(l.clone(), kts.clone()))
            }
            PartialExpr(ExprKind::BinOp(
                BinOp::RightBiasedRecordMerge,
                x,
                y,
            )) => match (x.kind(), y.kind()) {
                (_, RecordLit(kvs)) => match kvs.get(l) {
                    Some(r) => Ret::Value(r.clone()),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(x.clone(), l.clone()),
                            env,
                        )
                    }
                },
                (RecordLit(kvs), _) => match kvs.get(l) {
                    Some(r) => Ret::Expr(ExprKind::Field(
                        Value::from_kind(PartialExpr(ExprKind::BinOp(
                            BinOp::RightBiasedRecordMerge,
                            Value::from_kind(RecordLit({
                                let mut kvs = HashMap::new();
                                kvs.insert(l.clone(), r.clone());
                                kvs
                            })),
                            y.clone(),
                        ))),
                        l.clone(),
                    )),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(y.clone(), l.clone()),
                            env,
                        )
                    }
                },
                _ => Ret::Expr(expr),
            },
            PartialExpr(ExprKind::BinOp(
                BinOp::RecursiveRecordTypeMerge,
                x,
                y,
            )) => match (x.kind(), y.kind()) {
                (RecordLit(kvs), _) => match kvs.get(l) {
                    Some(_) => Ret::Expr(expr),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(y.clone(), l.clone()),
                            env,
                        )
                    }
                },
                (_, RecordLit(kvs)) => match kvs.get(l) {
                    Some(_) => Ret::Expr(expr),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(x.clone(), l.clone()),
                            env,
                        )
                    }
                },
                _ => Ret::Expr(expr),
            },
            _ => Ret::Expr(expr),
        },
        ExprKind::ProjectionByExpr(_, _) => {
            unimplemented!("selection by expression")
        }
        ExprKind::Completion(_, _) => unimplemented!("record completion"),

        ExprKind::Merge(ref handlers, ref variant, _) => {
            match handlers.kind() {
                RecordLit(kvs) => match variant.kind() {
                    UnionConstructor(l, _) => match kvs.get(l) {
                        Some(h) => Ret::Value(h.clone()),
                        None => Ret::Expr(expr),
                    },
                    UnionLit(l, v, _) => match kvs.get(l) {
                        Some(h) => Ret::Value(h.app(v.clone())),
                        None => Ret::Expr(expr),
                    },
                    EmptyOptionalLit(_) => match kvs.get(&"None".into()) {
                        Some(h) => Ret::Value(h.clone()),
                        None => Ret::Expr(expr),
                    },
                    NEOptionalLit(v) => match kvs.get(&"Some".into()) {
                        Some(h) => Ret::Value(h.app(v.clone())),
                        None => Ret::Expr(expr),
                    },
                    _ => Ret::Expr(expr),
                },
                _ => Ret::Expr(expr),
            }
        }
        ExprKind::ToMap(ref v, ref annot) => match v.kind() {
            RecordLit(kvs) if kvs.is_empty() => {
                match annot.as_ref().map(|v| v.kind()) {
                    Some(ValueKind::AppliedBuiltin(BuiltinClosure {
                        b: Builtin::List,
                        args,
                        ..
                    })) if args.len() == 1 => {
                        Ret::ValueKind(EmptyListLit(args[0].clone()))
                    }
                    _ => Ret::Expr(expr),
                }
            }
            RecordLit(kvs) => Ret::ValueKind(NEListLit(
                kvs.iter()
                    .sorted_by_key(|(k, _)| k.clone())
                    .map(|(k, v)| {
                        let mut rec = HashMap::new();
                        rec.insert("mapKey".into(), Value::from_text(k));
                        rec.insert("mapValue".into(), v.clone());
                        Value::from_kind(ValueKind::RecordLit(rec))
                    })
                    .collect(),
            )),
            _ => Ret::Expr(expr),
        },
    };

    match ret {
        Ret::ValueKind(v) => v,
        Ret::Value(v) => v.kind().clone(),
        Ret::ValueRef(v) => v.kind().clone(),
        Ret::Expr(expr) => ValueKind::PartialExpr(expr),
    }
}

/// Normalize Hir into WHNF
pub(crate) fn normalize_hir_whnf(env: &NzEnv, hir: &Hir) -> ValueKind {
    match hir.kind() {
        HirKind::Var(var) => env.lookup_val(var),
        HirKind::Expr(ExprKind::Lam(binder, annot, body)) => {
            let annot = annot.eval(env);
            ValueKind::LamClosure {
                binder: Binder::new(binder.clone()),
                annot: annot,
                closure: Closure::new(env, body.clone()),
            }
        }
        HirKind::Expr(ExprKind::Pi(binder, annot, body)) => {
            let annot = annot.eval(env);
            ValueKind::PiClosure {
                binder: Binder::new(binder.clone()),
                annot,
                closure: Closure::new(env, body.clone()),
            }
        }
        HirKind::Expr(ExprKind::Let(_, None, val, body)) => {
            let val = val.eval(env);
            body.eval(&env.insert_value_noty(val)).kind().clone()
        }
        HirKind::Expr(e) => {
            let e = e.map_ref(|hir| hir.eval(env));
            normalize_one_layer(e, env)
        }
    }
}
