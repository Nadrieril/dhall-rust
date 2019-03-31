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
    let expr = rc(expr.map_embed(&no_import));
    let output = dhall_to_tokenstream_bx(&expr, &Context::new());
    output.into()
}

// Returns an expression of type Expr<_, _>. Expects interpolated variables
// to be of type SubExpr<_, _>.
fn dhall_to_tokenstream(
    expr: &DhallExpr,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    use dhall_core::Expr::*;
    match expr.as_ref() {
        Var(_) => {
            let v = dhall_to_tokenstream_bx(expr, ctx);
            quote! { *#v }
        }
        Pi(x, t, b) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            let b = dhall_to_tokenstream_bx(b, &ctx.insert(x.clone(), ()));
            let x = label_to_tokenstream(x);
            quote! { dhall_core::Expr::Pi(#x, #t, #b) }
        }
        Lam(x, t, b) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            let b = dhall_to_tokenstream_bx(b, &ctx.insert(x.clone(), ()));
            let x = label_to_tokenstream(x);
            quote! { dhall_core::Expr::Lam(#x, #t, #b) }
        }
        App(f, a) => {
            let f = dhall_to_tokenstream_bx(f, ctx);
            let a = vec_to_tokenstream(a, ctx);
            quote! { dhall_core::Expr::App(#f, #a) }
        }
        Const(c) => {
            let c = const_to_tokenstream(*c);
            quote! { dhall_core::Expr::Const(#c) }
        }
        Builtin(b) => {
            let b = builtin_to_tokenstream(*b);
            quote! { dhall_core::Expr::Builtin(#b) }
        }
        BinOp(o, a, b) => {
            let o = binop_to_tokenstream(*o);
            let a = dhall_to_tokenstream_bx(a, ctx);
            let b = dhall_to_tokenstream_bx(b, ctx);
            quote! { dhall_core::Expr::BinOp(#o, #a, #b) }
        }
        NaturalLit(n) => {
            quote! { dhall_core::Expr::NaturalLit(#n) }
        }
        BoolLit(b) => {
            quote! { dhall_core::Expr::BoolLit(#b) }
        }
        EmptyOptionalLit(x) => {
            let x = dhall_to_tokenstream_bx(x, ctx);
            quote! { dhall_core::Expr::EmptyOptionalLit(#x) }
        }
        NEOptionalLit(x) => {
            let x = dhall_to_tokenstream_bx(x, ctx);
            quote! { dhall_core::Expr::NEOptionalLit(#x) }
        }
        EmptyListLit(t) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            quote! { dhall_core::Expr::EmptyListLit(#t) }
        }
        NEListLit(es) => {
            let es = vec_to_tokenstream(es, ctx);
            quote! { dhall_core::Expr::NEListLit(#es) }
        }
        RecordType(m) => {
            let m = map_to_tokenstream(m, ctx);
            quote! { dhall_core::Expr::RecordType(#m) }
        }
        RecordLit(m) => {
            let m = map_to_tokenstream(m, ctx);
            quote! { dhall_core::Expr::RecordLit(#m) }
        }
        UnionType(m) => {
            let m = map_to_tokenstream(m, ctx);
            quote! { dhall_core::Expr::UnionType(#m) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type SubExpr<_, _>
fn dhall_to_tokenstream_bx(
    expr: &DhallExpr,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    use dhall_core::Expr::*;
    match expr.as_ref() {
        Var(V(s, n)) => {
            match ctx.lookup(&s, *n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    let s: String = s.into();
                    let var = quote! { dhall_core::V(#s.into(), #n) };
                    bx(quote! { dhall_core::Expr::Var(#var) })
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
        _ => bx(dhall_to_tokenstream(expr, ctx)),
    }
}

fn builtin_to_tokenstream(b: Builtin) -> TokenStream {
    format!("dhall_core::Builtin::{:?}", b).parse().unwrap()
}

fn const_to_tokenstream(c: Const) -> TokenStream {
    format!("dhall_core::Const::{:?}", c).parse().unwrap()
}

fn binop_to_tokenstream(b: BinOp) -> TokenStream {
    format!("dhall_core::BinOp::{:?}", b).parse().unwrap()
}

fn label_to_tokenstream(l: &Label) -> TokenStream {
    let l = String::from(l);
    quote! { #l.into() }
}

fn map_to_tokenstream(
    m: &BTreeMap<Label, SubExpr<X, X>>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    let (keys, values): (Vec<TokenStream>, Vec<TokenStream>) = m
        .iter()
        .map(|(k, v)| {
            (label_to_tokenstream(k), dhall_to_tokenstream_bx(&*v, ctx))
        })
        .unzip();
    quote! { {
        use std::collections::BTreeMap;
        let mut m = BTreeMap::new();
        #( m.insert(#keys, #values); )*
        m
    } }
}

fn vec_to_tokenstream(
    e: &Vec<DhallExpr>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    let e = e.iter().map(|x| dhall_to_tokenstream_bx(x, ctx));
    quote! { vec![ #(#e),* ] }
}

fn bx(x: TokenStream) -> TokenStream {
    quote! { dhall_core::bx(#x) }
}
