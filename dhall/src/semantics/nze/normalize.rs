use std::collections::HashMap;

use crate::operations::{normalize_operation, OpKind};
use crate::semantics::NzEnv;
use crate::semantics::{Binder, Closure, Hir, HirKind, Nir, NirKind, TextLit};
use crate::syntax::{ExprKind, InterpolatedTextContents};

pub fn apply_any(f: &Nir, a: Nir) -> NirKind {
    match f.kind() {
        NirKind::LamClosure { closure, .. } => closure.apply(a).kind().clone(),
        NirKind::AppliedBuiltin(closure) => closure.apply(a),
        NirKind::UnionConstructor(l, kts) => {
            NirKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => NirKind::Op(OpKind::App(f.clone(), a)),
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

pub type Ret = NirKind;

pub fn ret_nir(x: Nir) -> Ret {
    ret_ref(&x)
}
pub fn ret_kind(x: NirKind) -> Ret {
    x
}
pub fn ret_ref(x: &Nir) -> Ret {
    x.kind().clone()
}
pub fn ret_op(x: OpKind<Nir>) -> Ret {
    NirKind::Op(x)
}

pub fn normalize_one_layer(expr: ExprKind<Nir>, env: &NzEnv) -> NirKind {
    use NirKind::{
        Assert, Const, NEListLit, NEOptionalLit, Num, RecordLit, RecordType,
        UnionType,
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
        ExprKind::Op(ref op) => normalize_operation(op),
        ExprKind::Annot(x, _) => ret_nir(x),
        ExprKind::Assert(x) => ret_kind(Assert(x)),
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
