extern crate proc_macro;
use dhall_core::context::Context;
use dhall_core::*;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;

pub fn dhall_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr: SubExpr<X, Import> = parse_expr(&input_str).unwrap();
    let no_import =
        |_: &Import| -> X { panic!("Don't use import in dhall!()") };
    let expr = rc(expr.as_ref().map_embed(&no_import));
    let output = quote_subexpr(&expr, &Context::new());
    output.into()
}

// Returns an expression of type ExprF<T, _, _>, where T is the
// type of the subexpressions after interpolation.
pub fn quote_expr<TS>(expr: ExprF<TS, X, X>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    let quote_map = |m: BTreeMap<Label, TS>| -> TokenStream {
        let (keys, values): (Vec<TokenStream>, Vec<TS>) =
            m.into_iter().map(|(k, v)| (quote_label(&k), v)).unzip();
        quote! { {
            use std::collections::BTreeMap;
            let mut m = BTreeMap::new();
            #( m.insert(#keys, #values); )*
            m
        } }
    };

    let quote_vec = |e: Vec<TS>| -> TokenStream {
        quote! { vec![ #(#e),* ] }
    };

    use dhall_core::ExprF::*;
    match expr {
        Var(_) => unreachable!(),
        Pi(x, t, b) => {
            let x = quote_label(&x);
            quote! { dhall_core::ExprF::Pi(#x, #t, #b) }
        }
        Lam(x, t, b) => {
            let x = quote_label(&x);
            quote! { dhall_core::ExprF::Lam(#x, #t, #b) }
        }
        App(f, a) => {
            let a = quote_vec(a);
            quote! { dhall_core::ExprF::App(#f, #a) }
        }
        Const(c) => {
            let c = quote_const(c);
            quote! { dhall_core::ExprF::Const(#c) }
        }
        Builtin(b) => {
            let b = quote_builtin(b);
            quote! { dhall_core::ExprF::Builtin(#b) }
        }
        BinOp(o, a, b) => {
            let o = quote_binop(o);
            quote! { dhall_core::ExprF::BinOp(#o, #a, #b) }
        }
        NaturalLit(n) => {
            quote! { dhall_core::ExprF::NaturalLit(#n) }
        }
        BoolLit(b) => {
            quote! { dhall_core::ExprF::BoolLit(#b) }
        }
        EmptyOptionalLit(x) => {
            quote! { dhall_core::ExprF::EmptyOptionalLit(#x) }
        }
        NEOptionalLit(x) => {
            quote! { dhall_core::ExprF::NEOptionalLit(#x) }
        }
        EmptyListLit(t) => {
            quote! { dhall_core::ExprF::EmptyListLit(#t) }
        }
        NEListLit(es) => {
            let es = quote_vec(es);
            quote! { dhall_core::ExprF::NEListLit(#es) }
        }
        RecordType(m) => {
            let m = quote_map(m);
            quote! { dhall_core::ExprF::RecordType(#m) }
        }
        RecordLit(m) => {
            let m = quote_map(m);
            quote! { dhall_core::ExprF::RecordLit(#m) }
        }
        UnionType(m) => {
            let m = quote_map(m);
            quote! { dhall_core::ExprF::UnionType(#m) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type SubExpr<_, _>. Expects interpolated variables
// to be of type SubExpr<_, _>.
fn quote_subexpr(
    expr: &SubExpr<X, X>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    use dhall_core::ExprF::*;
    match map_subexpr(
        expr.as_ref(),
        |e| quote_subexpr(e, ctx),
        |_| unreachable!(),
        |_| unreachable!(),
        |l| l.clone(),
        |l, e| quote_subexpr(e, &ctx.insert(l.clone(), ())),
    ) {
        Var(V(ref s, n)) => {
            match ctx.lookup(s, n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    let s: String = s.into();
                    let var = quote! { dhall_core::V(#s.into(), #n) };
                    bx(quote! { dhall_core::ExprF::Var(#var) })
                }
                // Free variable; interpolates as a rust variable
                None => {
                    let s: String = s.into();
                    // TODO: insert appropriate shifts ?
                    let v: TokenStream = s.parse().unwrap();
                    quote! { {
                        let x: dhall_core::SubExpr<_, _> = #v.clone();
                        x
                    } }
                }
            }
        }
        e => bx(quote_expr(e)),
    }
}

fn quote_builtin(b: Builtin) -> TokenStream {
    format!("dhall_core::Builtin::{:?}", b).parse().unwrap()
}

fn quote_const(c: Const) -> TokenStream {
    format!("dhall_core::Const::{:?}", c).parse().unwrap()
}

fn quote_binop(b: BinOp) -> TokenStream {
    format!("dhall_core::BinOp::{:?}", b).parse().unwrap()
}

fn quote_label(l: &Label) -> TokenStream {
    let l = String::from(l);
    quote! { #l.into() }
}

fn bx(x: TokenStream) -> TokenStream {
    quote! { dhall_core::bx(#x) }
}
