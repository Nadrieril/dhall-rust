use itertools::Itertools;
use std::collections::HashMap;

use crate::semantics::NzEnv;
use crate::semantics::{Binder, Closure, Hir, HirKind, Nir, NirKind, TextLit};
use crate::syntax::{BinOp, ExprKind, InterpolatedTextContents, NumKind};

pub fn apply_any(f: Nir, a: Nir) -> NirKind {
    match f.kind() {
        NirKind::LamClosure { closure, .. } => closure.apply(a).kind().clone(),
        NirKind::AppliedBuiltin(closure) => closure.apply(a),
        NirKind::UnionConstructor(l, kts) => {
            NirKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => NirKind::PartialExpr(ExprKind::App(f, a)),
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

// Small helper enum to avoid repetition
enum Ret<'a> {
    NirKind(NirKind),
    Nir(Nir),
    NirRef(&'a Nir),
    Expr(ExprKind<Nir>),
}

fn apply_binop<'a>(o: BinOp, x: &'a Nir, y: &'a Nir) -> Option<Ret<'a>> {
    use BinOp::{
        BoolAnd, BoolEQ, BoolNE, BoolOr, Equivalence, ListAppend, NaturalPlus,
        NaturalTimes, RecursiveRecordMerge, RecursiveRecordTypeMerge,
        RightBiasedRecordMerge, TextAppend,
    };
    use NirKind::{EmptyListLit, NEListLit, Num, RecordLit, RecordType};
    use NumKind::{Bool, Natural};

    Some(match (o, x.kind(), y.kind()) {
        (BoolAnd, Num(Bool(true)), _) => Ret::NirRef(y),
        (BoolAnd, _, Num(Bool(true))) => Ret::NirRef(x),
        (BoolAnd, Num(Bool(false)), _) => Ret::NirKind(Num(Bool(false))),
        (BoolAnd, _, Num(Bool(false))) => Ret::NirKind(Num(Bool(false))),
        (BoolAnd, _, _) if x == y => Ret::NirRef(x),
        (BoolOr, Num(Bool(true)), _) => Ret::NirKind(Num(Bool(true))),
        (BoolOr, _, Num(Bool(true))) => Ret::NirKind(Num(Bool(true))),
        (BoolOr, Num(Bool(false)), _) => Ret::NirRef(y),
        (BoolOr, _, Num(Bool(false))) => Ret::NirRef(x),
        (BoolOr, _, _) if x == y => Ret::NirRef(x),
        (BoolEQ, Num(Bool(true)), _) => Ret::NirRef(y),
        (BoolEQ, _, Num(Bool(true))) => Ret::NirRef(x),
        (BoolEQ, Num(Bool(x)), Num(Bool(y))) => Ret::NirKind(Num(Bool(x == y))),
        (BoolEQ, _, _) if x == y => Ret::NirKind(Num(Bool(true))),
        (BoolNE, Num(Bool(false)), _) => Ret::NirRef(y),
        (BoolNE, _, Num(Bool(false))) => Ret::NirRef(x),
        (BoolNE, Num(Bool(x)), Num(Bool(y))) => Ret::NirKind(Num(Bool(x != y))),
        (BoolNE, _, _) if x == y => Ret::NirKind(Num(Bool(false))),

        (NaturalPlus, Num(Natural(0)), _) => Ret::NirRef(y),
        (NaturalPlus, _, Num(Natural(0))) => Ret::NirRef(x),
        (NaturalPlus, Num(Natural(x)), Num(Natural(y))) => {
            Ret::NirKind(Num(Natural(x + y)))
        }
        (NaturalTimes, Num(Natural(0)), _) => Ret::NirKind(Num(Natural(0))),
        (NaturalTimes, _, Num(Natural(0))) => Ret::NirKind(Num(Natural(0))),
        (NaturalTimes, Num(Natural(1)), _) => Ret::NirRef(y),
        (NaturalTimes, _, Num(Natural(1))) => Ret::NirRef(x),
        (NaturalTimes, Num(Natural(x)), Num(Natural(y))) => {
            Ret::NirKind(Num(Natural(x * y)))
        }

        (ListAppend, EmptyListLit(_), _) => Ret::NirRef(y),
        (ListAppend, _, EmptyListLit(_)) => Ret::NirRef(x),
        (ListAppend, NEListLit(xs), NEListLit(ys)) => Ret::NirKind(NEListLit(
            xs.iter().chain(ys.iter()).cloned().collect(),
        )),

        (TextAppend, NirKind::TextLit(x), _) if x.is_empty() => Ret::NirRef(y),
        (TextAppend, _, NirKind::TextLit(y)) if y.is_empty() => Ret::NirRef(x),
        (TextAppend, NirKind::TextLit(x), NirKind::TextLit(y)) => {
            Ret::NirKind(NirKind::TextLit(x.concat(y)))
        }
        (TextAppend, NirKind::TextLit(x), _) => Ret::NirKind(NirKind::TextLit(
            x.concat(&TextLit::interpolate(y.clone())),
        )),
        (TextAppend, _, NirKind::TextLit(y)) => Ret::NirKind(NirKind::TextLit(
            TextLit::interpolate(x.clone()).concat(y),
        )),

        (RightBiasedRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::NirRef(x)
        }
        (RightBiasedRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::NirRef(y)
        }
        (RightBiasedRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let mut kvs = kvs2.clone();
            for (x, v) in kvs1 {
                // Insert only if key not already present
                kvs.entry(x.clone()).or_insert_with(|| v.clone());
            }
            Ret::NirKind(RecordLit(kvs))
        }
        (RightBiasedRecordMerge, _, _) if x == y => Ret::NirRef(y),

        (RecursiveRecordMerge, _, RecordLit(kvs)) if kvs.is_empty() => {
            Ret::NirRef(x)
        }
        (RecursiveRecordMerge, RecordLit(kvs), _) if kvs.is_empty() => {
            Ret::NirRef(y)
        }
        (RecursiveRecordMerge, RecordLit(kvs1), RecordLit(kvs2)) => {
            let kvs = merge_maps(kvs1, kvs2, |_, v1, v2| {
                Nir::from_partial_expr(ExprKind::BinOp(
                    RecursiveRecordMerge,
                    v1.clone(),
                    v2.clone(),
                ))
            });
            Ret::NirKind(RecordLit(kvs))
        }

        (RecursiveRecordTypeMerge, RecordType(kts_x), RecordType(kts_y)) => {
            let kts = merge_maps(
                kts_x,
                kts_y,
                // If the Label exists for both records, then we hit the recursive case.
                |_, l: &Nir, r: &Nir| {
                    Nir::from_partial_expr(ExprKind::BinOp(
                        RecursiveRecordTypeMerge,
                        l.clone(),
                        r.clone(),
                    ))
                },
            );
            Ret::NirKind(RecordType(kts))
        }

        (Equivalence, _, _) => {
            Ret::NirKind(NirKind::Equivalence(x.clone(), y.clone()))
        }

        _ => return None,
    })
}

#[allow(clippy::cognitive_complexity)]
pub fn normalize_one_layer(expr: ExprKind<Nir>, env: &NzEnv) -> NirKind {
    use NirKind::{
        EmptyListLit, EmptyOptionalLit, NEListLit, NEOptionalLit, Num,
        PartialExpr, RecordLit, RecordType, UnionConstructor, UnionLit,
        UnionType,
    };
    use NumKind::Bool;

    let ret = match expr {
        ExprKind::Import(..) | ExprKind::Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
        ExprKind::Var(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..) => unreachable!(
            "This case should have been handled in normalize_hir_whnf"
        ),

        ExprKind::Annot(x, _) => Ret::Nir(x),
        ExprKind::Const(c) => Ret::Nir(Nir::from_const(c)),
        ExprKind::Builtin(b) => Ret::Nir(Nir::from_builtin_env(b, env)),
        ExprKind::Assert(_) => Ret::Expr(expr),
        ExprKind::App(v, a) => Ret::Nir(v.app(a)),
        ExprKind::Num(l) => Ret::NirKind(Num(l)),
        ExprKind::SomeLit(e) => Ret::NirKind(NEOptionalLit(e)),
        ExprKind::EmptyListLit(t) => {
            let arg = match t.kind() {
                NirKind::ListType(t) => t.clone(),
                _ => panic!("internal type error"),
            };
            Ret::NirKind(NirKind::EmptyListLit(arg))
        }
        ExprKind::NEListLit(elts) => {
            Ret::NirKind(NEListLit(elts.into_iter().collect()))
        }
        ExprKind::RecordLit(kvs) => {
            Ret::NirKind(RecordLit(kvs.into_iter().collect()))
        }
        ExprKind::RecordType(kvs) => {
            Ret::NirKind(RecordType(kvs.into_iter().collect()))
        }
        ExprKind::UnionType(kvs) => {
            Ret::NirKind(UnionType(kvs.into_iter().collect()))
        }
        ExprKind::TextLit(elts) => {
            let tlit = TextLit::new(elts.into_iter());
            // Simplify bare interpolation
            if let Some(v) = tlit.as_single_expr() {
                Ret::Nir(v.clone())
            } else {
                Ret::NirKind(NirKind::TextLit(tlit))
            }
        }
        ExprKind::BoolIf(ref b, ref e1, ref e2) => {
            match b.kind() {
                Num(Bool(true)) => Ret::NirRef(e1),
                Num(Bool(false)) => Ret::NirRef(e2),
                _ => {
                    match (e1.kind(), e2.kind()) {
                        // Simplify `if b then True else False`
                        (Num(Bool(true)), Num(Bool(false))) => Ret::NirRef(b),
                        _ if e1 == e2 => Ret::NirRef(e1),
                        _ => Ret::Expr(expr),
                    }
                }
            }
        }
        ExprKind::BinOp(o, ref x, ref y) => match apply_binop(o, x, y) {
            Some(ret) => ret,
            None => Ret::Expr(expr),
        },

        ExprKind::Field(ref v, ref field) => match v.kind() {
            RecordLit(kvs) => match kvs.get(field) {
                Some(r) => Ret::Nir(r.clone()),
                None => Ret::Expr(expr),
            },
            UnionType(kts) => {
                Ret::NirKind(UnionConstructor(field.clone(), kts.clone()))
            }
            PartialExpr(ExprKind::Projection(x, _)) => {
                return normalize_one_layer(
                    ExprKind::Field(x.clone(), field.clone()),
                    env,
                )
            }
            PartialExpr(ExprKind::BinOp(
                BinOp::RightBiasedRecordMerge,
                x,
                y,
            )) => match (x.kind(), y.kind()) {
                (_, RecordLit(kvs)) => match kvs.get(field) {
                    Some(r) => Ret::Nir(r.clone()),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(x.clone(), field.clone()),
                            env,
                        )
                    }
                },
                (RecordLit(kvs), _) => match kvs.get(field) {
                    Some(r) => Ret::Expr(ExprKind::Field(
                        Nir::from_kind(PartialExpr(ExprKind::BinOp(
                            BinOp::RightBiasedRecordMerge,
                            Nir::from_kind(RecordLit(
                                Some((field.clone(), r.clone()))
                                    .into_iter()
                                    .collect(),
                            )),
                            y.clone(),
                        ))),
                        field.clone(),
                    )),
                    None => {
                        return normalize_one_layer(
                            ExprKind::Field(y.clone(), field.clone()),
                            env,
                        )
                    }
                },
                _ => Ret::Expr(expr),
            },
            PartialExpr(ExprKind::BinOp(BinOp::RecursiveRecordMerge, x, y)) => {
                match (x.kind(), y.kind()) {
                    (RecordLit(kvs), _) => match kvs.get(field) {
                        Some(r) => Ret::Expr(ExprKind::Field(
                            Nir::from_kind(PartialExpr(ExprKind::BinOp(
                                BinOp::RecursiveRecordMerge,
                                Nir::from_kind(RecordLit(
                                    Some((field.clone(), r.clone()))
                                        .into_iter()
                                        .collect(),
                                )),
                                y.clone(),
                            ))),
                            field.clone(),
                        )),
                        None => {
                            return normalize_one_layer(
                                ExprKind::Field(y.clone(), field.clone()),
                                env,
                            )
                        }
                    },
                    (_, RecordLit(kvs)) => match kvs.get(field) {
                        Some(r) => Ret::Expr(ExprKind::Field(
                            Nir::from_kind(PartialExpr(ExprKind::BinOp(
                                BinOp::RecursiveRecordMerge,
                                x.clone(),
                                Nir::from_kind(RecordLit(
                                    Some((field.clone(), r.clone()))
                                        .into_iter()
                                        .collect(),
                                )),
                            ))),
                            field.clone(),
                        )),
                        None => {
                            return normalize_one_layer(
                                ExprKind::Field(x.clone(), field.clone()),
                                env,
                            )
                        }
                    },
                    _ => Ret::Expr(expr),
                }
            }
            _ => Ret::Expr(expr),
        },
        ExprKind::Projection(_, ref ls) if ls.is_empty() => {
            Ret::NirKind(RecordLit(HashMap::new()))
        }
        ExprKind::Projection(ref v, ref ls) => match v.kind() {
            RecordLit(kvs) => Ret::NirKind(RecordLit(
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
        ExprKind::ProjectionByExpr(ref v, ref t) => match t.kind() {
            RecordType(kts) => {
                return normalize_one_layer(
                    ExprKind::Projection(
                        v.clone(),
                        kts.keys().cloned().collect(),
                    ),
                    env,
                )
            }
            _ => Ret::Expr(expr),
        },

        ExprKind::Merge(ref handlers, ref variant, _) => {
            match handlers.kind() {
                RecordLit(kvs) => match variant.kind() {
                    UnionConstructor(l, _) => match kvs.get(l) {
                        Some(h) => Ret::Nir(h.clone()),
                        None => Ret::Expr(expr),
                    },
                    UnionLit(l, v, _) => match kvs.get(l) {
                        Some(h) => Ret::Nir(h.app(v.clone())),
                        None => Ret::Expr(expr),
                    },
                    EmptyOptionalLit(_) => match kvs.get(&"None".into()) {
                        Some(h) => Ret::Nir(h.clone()),
                        None => Ret::Expr(expr),
                    },
                    NEOptionalLit(v) => match kvs.get(&"Some".into()) {
                        Some(h) => Ret::Nir(h.app(v.clone())),
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
                    Some(NirKind::ListType(t)) => {
                        Ret::NirKind(EmptyListLit(t.clone()))
                    }
                    _ => Ret::Expr(expr),
                }
            }
            RecordLit(kvs) => Ret::NirKind(NEListLit(
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
            _ => Ret::Expr(expr),
        },
    };

    match ret {
        Ret::NirKind(v) => v,
        Ret::Nir(v) => v.kind().clone(),
        Ret::NirRef(v) => v.kind().clone(),
        Ret::Expr(expr) => NirKind::PartialExpr(expr),
    }
}

/// Normalize Hir into WHNF
pub fn normalize_hir_whnf(env: &NzEnv, hir: &Hir) -> NirKind {
    match hir.kind() {
        HirKind::Var(var) => env.lookup_val(*var),
        HirKind::Import(hir, _) => normalize_hir_whnf(env, hir),
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
