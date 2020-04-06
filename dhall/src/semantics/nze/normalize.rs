use itertools::Itertools;
use std::collections::HashMap;

use crate::semantics::NzEnv;
use crate::semantics::{Binder, Closure, Hir, HirKind, Nir, NirKind, TextLit};
use crate::syntax::{
    BinOp, ExprKind, InterpolatedTextContents, Label, NumKind, OpKind,
};

pub fn apply_any(f: &Nir, a: Nir) -> NirKind {
    match f.kind() {
        NirKind::LamClosure { closure, .. } => closure.apply(a).kind().clone(),
        NirKind::AppliedBuiltin(closure) => closure.apply(a),
        NirKind::UnionConstructor(l, kts) => {
            NirKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => NirKind::PartialExpr(ExprKind::Op(OpKind::App(f.clone(), a))),
    }
}

pub fn squash_textlit(
    elts: impl Iterator<Item = InterpolatedTextContents<Nir>>,
) -> Vec<InterpolatedTextContents<Nir>> {
    use std::mem::replace;
    use InterpolatedTextContents::{Expr, Text};

    fn inner(
        elts: impl Iterator<Item = InterpolatedTextContents<Nir>>,
        crnt_str: &mut String,
        ret: &mut Vec<InterpolatedTextContents<Nir>>,
    ) {
        for contents in elts {
            match contents {
                Text(s) => crnt_str.push_str(&s),
                Expr(e) => match e.kind() {
                    NirKind::TextLit(elts2) => {
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

pub fn merge_maps<K, V, F>(
    map1: &HashMap<K, V>,
    map2: &HashMap<K, V>,
    mut f: F,
) -> HashMap<K, V>
where
    F: FnMut(&K, &V, &V) -> V,
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    let mut kvs = HashMap::new();
    for (x, v2) in map2 {
        let newv = if let Some(v1) = map1.get(x) {
            // Collision: the key is present in both maps
            f(x, v1, v2)
        } else {
            v2.clone()
        };
        kvs.insert(x.clone(), newv);
    }
    for (x, v1) in map1 {
        // Insert only if key not already present
        kvs.entry(x.clone()).or_insert_with(|| v1.clone());
    }
    kvs
}

type Ret = NirKind;

fn ret_nir(x: Nir) -> Ret {
    ret_ref(&x)
}
fn ret_kind(x: NirKind) -> Ret {
    x
}
fn ret_ref(x: &Nir) -> Ret {
    x.kind().clone()
}
fn ret_expr(x: ExprKind<Nir>) -> Ret {
    NirKind::PartialExpr(x)
}

fn normalize_binop(o: BinOp, x: &Nir, y: &Nir) -> Option<Ret> {
    use BinOp::*;
    use NirKind::{EmptyListLit, NEListLit, Num, RecordLit, RecordType};
    use NumKind::{Bool, Natural};

    Some(match (o, x.kind(), y.kind()) {
        (BoolAnd, Num(Bool(true)), _) => ret_ref(y),
        (BoolAnd, _, Num(Bool(true))) => ret_ref(x),
        (BoolAnd, Num(Bool(false)), _) => ret_kind(Num(Bool(false))),
        (BoolAnd, _, Num(Bool(false))) => ret_kind(Num(Bool(false))),
        (BoolAnd, _, _) if x == y => ret_ref(x),
        (BoolOr, Num(Bool(true)), _) => ret_kind(Num(Bool(true))),
        (BoolOr, _, Num(Bool(true))) => ret_kind(Num(Bool(true))),
        (BoolOr, Num(Bool(false)), _) => ret_ref(y),
        (BoolOr, _, Num(Bool(false))) => ret_ref(x),
        (BoolOr, _, _) if x == y => ret_ref(x),
        (BoolEQ, Num(Bool(true)), _) => ret_ref(y),
        (BoolEQ, _, Num(Bool(true))) => ret_ref(x),
        (BoolEQ, Num(Bool(x)), Num(Bool(y))) => ret_kind(Num(Bool(x == y))),
        (BoolEQ, _, _) if x == y => ret_kind(Num(Bool(true))),
        (BoolNE, Num(Bool(false)), _) => ret_ref(y),
        (BoolNE, _, Num(Bool(false))) => ret_ref(x),
        (BoolNE, Num(Bool(x)), Num(Bool(y))) => ret_kind(Num(Bool(x != y))),
        (BoolNE, _, _) if x == y => ret_kind(Num(Bool(false))),

        (NaturalPlus, Num(Natural(0)), _) => ret_ref(y),
        (NaturalPlus, _, Num(Natural(0))) => ret_ref(x),
        (NaturalPlus, Num(Natural(x)), Num(Natural(y))) => {
            ret_kind(Num(Natural(x + y)))
        }
        (NaturalTimes, Num(Natural(0)), _) => ret_kind(Num(Natural(0))),
        (NaturalTimes, _, Num(Natural(0))) => ret_kind(Num(Natural(0))),
        (NaturalTimes, Num(Natural(1)), _) => ret_ref(y),
        (NaturalTimes, _, Num(Natural(1))) => ret_ref(x),
        (NaturalTimes, Num(Natural(x)), Num(Natural(y))) => {
            ret_kind(Num(Natural(x * y)))
        }

        (ListAppend, EmptyListLit(_), _) => ret_ref(y),
        (ListAppend, _, EmptyListLit(_)) => ret_ref(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => {
            ret_kind(NEListLit(xs.iter().chain(ys.iter()).cloned().collect()))
        }

        (TextAppend, NirKind::TextLit(x), _) if x.is_empty() => ret_ref(y),
        (TextAppend, _, NirKind::TextLit(y)) if y.is_empty() => ret_ref(x),
        (TextAppend, NirKind::TextLit(x), NirKind::TextLit(y)) => {
            ret_kind(NirKind::TextLit(x.concat(y)))
        }
        (TextAppend, NirKind::TextLit(x), _) => ret_kind(NirKind::TextLit(
            x.concat(&TextLit::interpolate(y.clone())),
        )),
        (TextAppend, _, NirKind::TextLit(y)) => ret_kind(NirKind::TextLit(
            TextLit::interpolate(x.clone()).concat(y),
        )),

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            ret_ref(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            ret_ref(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            ret_kind(RecordLit(kvs))
        }
        (RightBiasedRecordMerge, _, _) if x == y => ret_ref(y),

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            ret_ref(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            ret_ref(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |_, v1, v2| {
                Nir::from_partial_expr(ExprKind::Op(OpKind::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                )))
            });
            ret_kind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, RecordType(kts_x), RecordType(kts_y)) => {
            let kts = merge_maps(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Nir, r: &Nir| {
                    Nir::from_partial_expr(ExprKind::Op(OpKind::BinOp(
                        RecursiveRecordTypeMerge,
                        l.clone(),
                        r.clone(),
                    )))
                },
            );
            ret_kind(RecordType(kts))
        }

        (Equivalence, _, _) => {
            ret_kind(NirKind::Equivalence(x.clone(), y.clone()))
        }

        _ => return None,
    })
}

fn normalize_field(v: &Nir, field: &Label) -> Option<Ret> {
    use self::BinOp::{RecursiveRecordMerge, RightBiasedRecordMerge};
    use ExprKind::Op;
    use NirKind::{PartialExpr, RecordLit, UnionConstructor, UnionType};
    use OpKind::{BinOp, Field, Projection};

    Some(match v.kind() {
        RecordLit(kvs) => match kvs.get(field) {
            Some(r) => ret_ref(r),
            None => return None,
        },
        UnionType(kts) => {
            ret_kind(UnionConstructor(field.clone(), kts.clone()))
        }
        PartialExpr(Op(Projection(x, _))) => return normalize_field(x, field),
        PartialExpr(Op(BinOp(RightBiasedRecordMerge, x, y))) => {
            match (x.kind(), y.kind()) {
                (_, RecordLit(kvs)) => match kvs.get(field) {
                    Some(r) => ret_ref(r),
                    None => return normalize_field(x, field),
                },
                (RecordLit(kvs), _) => match kvs.get(field) {
                    Some(r) => ret_expr(Op(Field(
                        Nir::from_kind(PartialExpr(Op(BinOp(
                            RightBiasedRecordMerge,
                            Nir::from_kind(RecordLit(
                                Some((field.clone(), r.clone()))
                                    .into_iter()
                                    .collect(),
                            )),
                            y.clone(),
                        )))),
                        field.clone(),
                    ))),
                    None => return normalize_field(y, field),
                },
                _ => return None,
            }
        }
        PartialExpr(Op(BinOp(RecursiveRecordMerge, x, y))) => {
            match (x.kind(), y.kind()) {
                (RecordLit(kvs), _) => match kvs.get(field) {
                    Some(r) => ret_expr(Op(Field(
                        Nir::from_kind(PartialExpr(Op(BinOp(
                            RecursiveRecordMerge,
                            Nir::from_kind(RecordLit(
                                Some((field.clone(), r.clone()))
                                    .into_iter()
                                    .collect(),
                            )),
                            y.clone(),
                        )))),
                        field.clone(),
                    ))),
                    None => return normalize_field(y, field),
                },
                (_, RecordLit(kvs)) => match kvs.get(field) {
                    Some(r) => ret_expr(Op(Field(
                        Nir::from_kind(PartialExpr(Op(BinOp(
                            RecursiveRecordMerge,
                            x.clone(),
                            Nir::from_kind(RecordLit(
                                Some((field.clone(), r.clone()))
                                    .into_iter()
                                    .collect(),
                            )),
                        )))),
                        field.clone(),
                    ))),
                    None => return normalize_field(x, field),
                },
                _ => return None,
            }
        }
        _ => return None,
    })
}

fn normalize_operation(opkind: &OpKind<Nir>) -> Option<Ret> {
    use ExprKind::Op;
    use NirKind::{
        EmptyListLit, EmptyOptionalLit, NEListLit, NEOptionalLit, Num,
        PartialExpr, RecordLit, RecordType, UnionConstructor, UnionLit,
    };
    use NumKind::Bool;
    use OpKind::*;

    Some(match opkind {
        App(v, a) => ret_kind(v.app_to_kind(a.clone())),
        BinOp(o, x, y) => return normalize_binop(*o, x, y),
        BoolIf(b, e1, e2) => {
            match b.kind() {
                Num(Bool(true)) => ret_ref(e1),
                Num(Bool(false)) => ret_ref(e2),
                _ => {
                    match (e1.kind(), e2.kind()) {
                        // Simplify `if b then True else False`
                        (Num(Bool(true)), Num(Bool(false))) => ret_ref(b),
                        _ if e1 == e2 => ret_ref(e1),
                        _ => return None,
                    }
                }
            }
        }
        Merge(handlers, variant, _) => match handlers.kind() {
            RecordLit(kvs) => match variant.kind() {
                UnionConstructor(l, _) => match kvs.get(l) {
                    Some(h) => ret_ref(h),
                    None => return None,
                },
                UnionLit(l, v, _) => match kvs.get(l) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => return None,
                },
                EmptyOptionalLit(_) => match kvs.get(&"None".into()) {
                    Some(h) => ret_ref(h),
                    None => return None,
                },
                NEOptionalLit(v) => match kvs.get(&"Some".into()) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => return None,
                },
                _ => return None,
            },
            _ => return None,
        },
        ToMap(v, annot) => match v.kind() {
            RecordLit(kvs) if kvs.is_empty() => {
                match annot.as_ref().map(|v| v.kind()) {
                    Some(NirKind::ListType(t)) => {
                        ret_kind(EmptyListLit(t.clone()))
                    }
                    _ => return None,
                }
            }
            RecordLit(kvs) => ret_kind(NEListLit(
                kvs.iter()
                    .sorted_by_key(|(k, _)| *k)
                    .map(|(k, v)| {
                        let mut rec = HashMap::new();
                        rec.insert("mapKey".into(), Nir::from_text(k));
                        rec.insert("mapValue".into(), v.clone());
                        Nir::from_kind(NirKind::RecordLit(rec))
                    })
                    .collect(),
            )),
            _ => return None,
        },
        Field(v, field) => return normalize_field(v, field),
        Projection(_, ls) if ls.is_empty() => {
            ret_kind(RecordLit(HashMap::new()))
        }
        Projection(v, ls) => match v.kind() {
            RecordLit(kvs) => ret_kind(RecordLit(
                ls.iter()
                    .filter_map(|l| kvs.get(l).map(|x| (l.clone(), x.clone())))
                    .collect(),
            )),
            PartialExpr(Op(Projection(v2, _))) => {
                return normalize_operation(&Projection(v2.clone(), ls.clone()))
            }
            _ => return None,
        },
        ProjectionByExpr(v, t) => match t.kind() {
            RecordType(kts) => {
                return normalize_operation(&Projection(
                    v.clone(),
                    kts.keys().cloned().collect(),
                ))
            }
            _ => return None,
        },
        Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    })
}

pub fn normalize_one_layer(expr: ExprKind<Nir>, env: &NzEnv) -> NirKind {
    use NirKind::{
        Const, NEListLit, NEOptionalLit, Num, RecordLit, RecordType, UnionType,
    };

    match expr {
        ExprKind::Var(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..) => {
            unreachable!("This case should have been handled in normalize_hir")
        }

        ExprKind::Const(c) => ret_kind(Const(c)),
        ExprKind::Num(l) => ret_kind(Num(l)),
        ExprKind::Builtin(b) => {
            ret_kind(NirKind::from_builtin_env(b, env.clone()))
        }
        ExprKind::TextLit(elts) => {
            let tlit = TextLit::new(elts.into_iter());
            // Simplify bare interpolation
            if let Some(v) = tlit.as_single_expr() {
                ret_ref(v)
            } else {
                ret_kind(NirKind::TextLit(tlit))
            }
        }
        ExprKind::SomeLit(e) => ret_kind(NEOptionalLit(e)),
        ExprKind::EmptyListLit(t) => {
            let arg = match t.kind() {
                NirKind::ListType(t) => t.clone(),
                _ => panic!("internal type error"),
            };
            ret_kind(NirKind::EmptyListLit(arg))
        }
        ExprKind::NEListLit(elts) => {
            ret_kind(NEListLit(elts.into_iter().collect()))
        }
        ExprKind::RecordLit(kvs) => {
            ret_kind(RecordLit(kvs.into_iter().collect()))
        }
        ExprKind::RecordType(kvs) => {
            ret_kind(RecordType(kvs.into_iter().collect()))
        }
        ExprKind::UnionType(kvs) => {
            ret_kind(UnionType(kvs.into_iter().collect()))
        }
        ExprKind::Op(ref op) => match normalize_operation(op) {
            Some(ret) => ret,
            None => ret_expr(expr),
        },
        ExprKind::Annot(x, _) => ret_nir(x),
        ExprKind::Assert(_) => ret_expr(expr),
        ExprKind::Import(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    }
}

/// Normalize Hir into WHNF
pub fn normalize_hir(env: &NzEnv, hir: &Hir) -> NirKind {
    match hir.kind() {
        HirKind::Var(var) => env.lookup_val(*var),
        HirKind::Import(hir, _) => normalize_hir(env, hir),
        HirKind::Expr(ExprKind::Lam(binder, annot, body)) => {
            let annot = annot.eval(env);
            NirKind::LamClosure {
                binder: Binder::new(binder.clone()),
                annot,
                closure: Closure::new(env, body.clone()),
            }
        }
        HirKind::Expr(ExprKind::Pi(binder, annot, body)) => {
            let annot = annot.eval(env);
            NirKind::PiClosure {
                binder: Binder::new(binder.clone()),
                annot,
                closure: Closure::new(env, body.clone()),
            }
        }
        HirKind::Expr(ExprKind::Let(_, _, val, body)) => {
            let val = val.eval(env);
            body.eval(env.insert_value(val, ())).kind().clone()
        }
        HirKind::Expr(e) => {
            let e = e.map_ref(|hir| hir.eval(env));
            normalize_one_layer(e, env)
        }
    }
}
