use std::collections::HashMap;

use crate::operations::{normalize_operation, OpKind};
use crate::semantics::NzEnv;
use crate::semantics::{Binder, Closure, Hir, HirKind, Nir, NirKind, TextLit};
use crate::syntax::{ExprKind, InterpolatedTextContents};

pub fn apply_any<'cx>(f: &Nir<'cx>, a: Nir<'cx>) -> NirKind<'cx> {
    match f.kind() {
        NirKind::LamClosure { closure, .. } => closure.apply(a).kind().clone(),
        NirKind::AppliedBuiltin(closure) => closure.apply(a),
        NirKind::UnionConstructor(l, kts) => {
            NirKind::UnionLit(l.clone(), a, kts.clone())
        }
        _ => NirKind::Op(OpKind::App(f.clone(), a)),
    }
}

pub fn squash_textlit<'cx>(
    elts: impl Iterator<Item = InterpolatedTextContents<Nir<'cx>>>,
) -> Vec<InterpolatedTextContents<Nir<'cx>>> {
    use std::mem::replace;
    use InterpolatedTextContents::{Expr, Text};

    fn inner<'cx>(
        elts: impl Iterator<Item = InterpolatedTextContents<Nir<'cx>>>,
        crnt_str: &mut String,
        ret: &mut Vec<InterpolatedTextContents<Nir<'cx>>>,
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

pub type Ret<'cx> = NirKind<'cx>;

pub fn ret_nir<'cx>(x: Nir<'cx>) -> Ret<'cx> {
    x.into_kind()
}
pub fn ret_kind<'cx>(x: NirKind<'cx>) -> Ret<'cx> {
    x
}
pub fn ret_ref<'cx>(x: &Nir<'cx>) -> Ret<'cx> {
    x.kind().clone()
}
pub fn ret_op<'cx>(x: OpKind<Nir<'cx>>) -> Ret<'cx> {
    NirKind::Op(x)
}

pub fn normalize_one_layer<'cx>(expr: ExprKind<Nir<'cx>>) -> NirKind<'cx> {
    use NirKind::{
        Assert, Const, NEListLit, NEOptionalLit, Num, RecordLit, RecordType,
        UnionType,
    };

    match expr {
        ExprKind::Var(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Builtin(..) => {
            unreachable!("This case should have been handled in normalize_hir")
        }

        ExprKind::Const(c) => ret_kind(Const(c)),
        ExprKind::Num(l) => ret_kind(Num(l)),
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
        ExprKind::Op(op) => normalize_operation(op),
        ExprKind::Annot(x, _) => ret_nir(x),
        ExprKind::Assert(x) => ret_kind(Assert(x)),
        ExprKind::Import(..) => {
            unreachable!("This case should have been handled in resolution")
        }
    }
}

/// Normalize Hir into WHNF
pub fn normalize_hir<'cx>(env: &NzEnv<'cx>, hir: &Hir<'cx>) -> NirKind<'cx> {
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
        HirKind::Expr(ExprKind::Builtin(b)) => {
            NirKind::from_builtin_env(*b, env.clone())
        }
        HirKind::Expr(e) => {
            let e = e.map_ref(|hir| hir.eval(env));
            normalize_one_layer(e)
        }
    }
}
