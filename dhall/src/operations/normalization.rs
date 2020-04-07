use itertools::Itertools;
use std::collections::HashMap;
use std::iter::once;

use crate::operations::{BinOp, OpKind};
use crate::semantics::{
    merge_maps, ret_kind, ret_op, ret_ref, Nir, NirKind, Ret, TextLit,
};
use crate::syntax::{ExprKind, Label, NumKind};

fn normalize_binop(o: BinOp, x: &Nir, y: &Nir) -> Ret {
    use BinOp::*;
    use NirKind::{EmptyListLit, NEListLit, Num, RecordLit, RecordType};
    use NumKind::{Bool, Natural};

    match (o, x.kind(), y.kind()) {
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

        _ => ret_op(OpKind::BinOp(o, x.clone(), y.clone())),
    }
}

fn normalize_field(v: &Nir, field: &Label) -> Ret {
    use self::BinOp::{RecursiveRecordMerge, RightBiasedRecordMerge};
    use NirKind::{Op, RecordLit, UnionConstructor, UnionType};
    use OpKind::{BinOp, Field, Projection};
    let nothing_to_do = || ret_op(Field(v.clone(), field.clone()));

    match v.kind() {
        RecordLit(kvs) => match kvs.get(field) {
            Some(r) => ret_ref(r),
            None => nothing_to_do(),
        },
        UnionType(kts) => {
            ret_kind(UnionConstructor(field.clone(), kts.clone()))
        }
        Op(Projection(x, _)) => normalize_field(x, field),
        Op(BinOp(RightBiasedRecordMerge, x, y)) => match (x.kind(), y.kind()) {
            (_, RecordLit(kvs)) => match kvs.get(field) {
                Some(r) => ret_ref(r),
                None => normalize_field(x, field),
            },
            (RecordLit(kvs), _) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RightBiasedRecordMerge,
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                        y.clone(),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(y, field),
            },
            _ => nothing_to_do(),
        },
        Op(BinOp(RecursiveRecordMerge, x, y)) => match (x.kind(), y.kind()) {
            (RecordLit(kvs), _) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RecursiveRecordMerge,
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                        y.clone(),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(y, field),
            },
            (_, RecordLit(kvs)) => match kvs.get(field) {
                Some(r) => ret_op(Field(
                    Nir::from_kind(Op(BinOp(
                        RecursiveRecordMerge,
                        x.clone(),
                        Nir::from_kind(RecordLit(
                            once((field.clone(), r.clone())).collect(),
                        )),
                    ))),
                    field.clone(),
                )),
                None => normalize_field(x, field),
            },
            _ => nothing_to_do(),
        },
        _ => nothing_to_do(),
    }
}

pub fn normalize_operation(opkind: &OpKind<Nir>) -> Ret {
    use self::BinOp::RightBiasedRecordMerge;
    use NirKind::{
        EmptyListLit, EmptyOptionalLit, NEListLit, NEOptionalLit, Num, Op,
        RecordLit, RecordType, UnionConstructor, UnionLit,
    };
    use NumKind::Bool;
    use OpKind::*;
    let nothing_to_do = || ret_op(opkind.clone());

    match opkind {
        App(v, a) => ret_kind(v.app_to_kind(a.clone())),
        BinOp(o, x, y) => normalize_binop(*o, x, y),
        BoolIf(b, e1, e2) => {
            match b.kind() {
                Num(Bool(true)) => ret_ref(e1),
                Num(Bool(false)) => ret_ref(e2),
                _ => {
                    match (e1.kind(), e2.kind()) {
                        // Simplify `if b then True else False`
                        (Num(Bool(true)), Num(Bool(false))) => ret_ref(b),
                        _ if e1 == e2 => ret_ref(e1),
                        _ => nothing_to_do(),
                    }
                }
            }
        }
        Merge(handlers, variant, _) => match handlers.kind() {
            RecordLit(kvs) => match variant.kind() {
                UnionConstructor(l, _) => match kvs.get(l) {
                    Some(h) => ret_ref(h),
                    None => nothing_to_do(),
                },
                UnionLit(l, v, _) => match kvs.get(l) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => nothing_to_do(),
                },
                EmptyOptionalLit(_) => match kvs.get(&"None".into()) {
                    Some(h) => ret_ref(h),
                    None => nothing_to_do(),
                },
                NEOptionalLit(v) => match kvs.get(&"Some".into()) {
                    Some(h) => ret_kind(h.app_to_kind(v.clone())),
                    None => nothing_to_do(),
                },
                _ => nothing_to_do(),
            },
            _ => nothing_to_do(),
        },
        ToMap(v, annot) => match v.kind() {
            RecordLit(kvs) if kvs.is_empty() => {
                match annot.as_ref().map(|v| v.kind()) {
                    Some(NirKind::ListType(t)) => {
                        ret_kind(EmptyListLit(t.clone()))
                    }
                    _ => nothing_to_do(),
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
            _ => nothing_to_do(),
        },
        Field(v, field) => normalize_field(v, field),
        Projection(_, ls) if ls.is_empty() => {
            ret_kind(RecordLit(HashMap::new()))
        }
        Projection(v, ls) => match v.kind() {
            RecordLit(kvs) => ret_kind(RecordLit(
                ls.iter()
                    .filter_map(|l| kvs.get(l).map(|x| (l.clone(), x.clone())))
                    .collect(),
            )),
            Op(Projection(v2, _)) => {
                normalize_operation(&Projection(v2.clone(), ls.clone()))
            }
            Op(BinOp(RightBiasedRecordMerge, l, r)) => match r.kind() {
                RecordLit(kvs) => {
                    let r_keys = kvs.keys().cloned().collect();
                    normalize_operation(&BinOp(
                        RightBiasedRecordMerge,
                        Nir::from_partial_expr(ExprKind::Op(Projection(
                            l.clone(),
                            ls.difference(&r_keys).cloned().collect(),
                        ))),
                        Nir::from_partial_expr(ExprKind::Op(Projection(
                            r.clone(),
                            ls.intersection(&r_keys).cloned().collect(),
                        ))),
                    ))
                }
                _ => nothing_to_do(),
            },
            _ => nothing_to_do(),
        },
        ProjectionByExpr(v, t) => match t.kind() {
            RecordType(kts) => normalize_operation(&Projection(
                v.clone(),
                kts.keys().cloned().collect(),
            )),
            _ => nothing_to_do(),
        },
        Completion(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    }
}
