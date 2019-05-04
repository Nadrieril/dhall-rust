extern crate proc_macro;
use dhall_syntax::context::Context;
use dhall_syntax::*;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;

pub fn expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr: SubExpr<_, _, Import> = parse_expr(&input_str).unwrap().unnote();
    let no_import =
        |_: &Import| -> X { panic!("Don't use import in dhall::expr!()") };
    let expr = expr.map_embed(no_import);
    let output = quote_expr(expr.as_ref(), &Context::new());
    output.into()
}

pub fn subexpr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr: SubExpr<_, _, Import> = parse_expr(&input_str).unwrap().unnote();
    let no_import =
        |_: &Import| -> X { panic!("Don't use import in dhall::subexpr!()") };
    let expr = expr.map_embed(no_import);
    let output = quote_subexpr(&expr, &Context::new());
    output.into()
}

// Returns an expression of type ExprF<T, _, _>, where T is the
// type of the subexpressions after interpolation.
pub fn quote_exprf<TS>(expr: ExprF<TS, Label, X>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    match expr {
        ExprF::Var(_) => unreachable!(),
        ExprF::Pi(x, t, b) => {
            let x = quote_label(&x);
            quote! { dhall_syntax::ExprF::Pi(#x, #t, #b) }
        }
        ExprF::Lam(x, t, b) => {
            let x = quote_label(&x);
            quote! { dhall_syntax::ExprF::Lam(#x, #t, #b) }
        }
        ExprF::App(f, a) => {
            quote! { dhall_syntax::ExprF::App(#f, #a) }
        }
        ExprF::Annot(x, t) => {
            quote! { dhall_syntax::ExprF::Annot(#x, #t) }
        }
        ExprF::Const(c) => {
            let c = quote_const(c);
            quote! { dhall_syntax::ExprF::Const(#c) }
        }
        ExprF::Builtin(b) => {
            let b = quote_builtin(b);
            quote! { dhall_syntax::ExprF::Builtin(#b) }
        }
        ExprF::BinOp(o, a, b) => {
            let o = quote_binop(o);
            quote! { dhall_syntax::ExprF::BinOp(#o, #a, #b) }
        }
        ExprF::NaturalLit(n) => {
            quote! { dhall_syntax::ExprF::NaturalLit(#n) }
        }
        ExprF::BoolLit(b) => {
            quote! { dhall_syntax::ExprF::BoolLit(#b) }
        }
        ExprF::SomeLit(x) => {
            quote! { dhall_syntax::ExprF::SomeLit(#x) }
        }
        ExprF::EmptyListLit(t) => {
            quote! { dhall_syntax::ExprF::EmptyListLit(#t) }
        }
        ExprF::NEListLit(es) => {
            let es = quote_vec(es);
            quote! { dhall_syntax::ExprF::NEListLit(#es) }
        }
        ExprF::RecordType(m) => {
            let m = quote_map(m);
            quote! { dhall_syntax::ExprF::RecordType(#m) }
        }
        ExprF::RecordLit(m) => {
            let m = quote_map(m);
            quote! { dhall_syntax::ExprF::RecordLit(#m) }
        }
        ExprF::UnionType(m) => {
            let m = quote_opt_map(m);
            quote! { dhall_syntax::ExprF::UnionType(#m) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type SubExpr<_, _>. Expects interpolated variables
// to be of type SubExpr<_, _>.
fn quote_subexpr(
    expr: &SubExpr<Label, X, X>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    match expr.as_ref().map_ref_with_special_handling_of_binders(
        |e| quote_subexpr(e, ctx),
        |l, e| quote_subexpr(e, &ctx.insert(l.clone(), ())),
        |_| unreachable!(),
        Label::clone,
    ) {
        ExprF::Var(Var(ref s, n)) => {
            match ctx.lookup(s, n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    let s: String = s.into();
                    let var = quote! { dhall_syntax::Var(#s.into(), #n) };
                    rc(quote! { dhall_syntax::ExprF::Var(#var) })
                }
                // Free variable; interpolates as a rust variable
                None => {
                    let s: String = s.into();
                    // TODO: insert appropriate shifts ?
                    let v: TokenStream = s.parse().unwrap();
                    quote! { {
                        let x: dhall_syntax::SubExpr<_, _, _> = #v.clone();
                        x
                    } }
                }
            }
        }
        e => rc(quote_exprf(e)),
    }
}

// Returns an expression of type Expr<_, _, _>. Expects interpolated variables
// to be of type SubExpr<_, _, _>.
fn quote_expr(
    expr: &Expr<Label, X, X>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    match expr.map_ref_with_special_handling_of_binders(
        |e| quote_subexpr(e, ctx),
        |l, e| quote_subexpr(e, &ctx.insert(l.clone(), ())),
        |_| unreachable!(),
        Label::clone,
    ) {
        ExprF::Var(Var(ref s, n)) => {
            match ctx.lookup(s, n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    let s: String = s.into();
                    let var = quote! { dhall_syntax::Var(#s.into(), #n) };
                    quote! { dhall_syntax::ExprF::Var(#var) }
                }
                // Free variable; interpolates as a rust variable
                None => {
                    let s: String = s.into();
                    // TODO: insert appropriate shifts ?
                    let v: TokenStream = s.parse().unwrap();
                    quote! { {
                        let x: dhall_syntax::SubExpr<_, _, _> = #v.clone();
                        x.unroll()
                    } }
                }
            }
        }
        e => quote_exprf(e),
    }
}

fn quote_builtin(b: Builtin) -> TokenStream {
    format!("dhall_syntax::Builtin::{:?}", b).parse().unwrap()
}

fn quote_const(c: Const) -> TokenStream {
    format!("dhall_syntax::Const::{:?}", c).parse().unwrap()
}

fn quote_binop(b: BinOp) -> TokenStream {
    format!("dhall_syntax::BinOp::{:?}", b).parse().unwrap()
}

fn quote_label(l: &Label) -> TokenStream {
    let l = String::from(l);
    quote! { dhall_syntax::Label::from(#l) }
}

fn rc(x: TokenStream) -> TokenStream {
    quote! { dhall_syntax::rc(#x) }
}

fn quote_opt<TS>(x: Option<TS>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    match x {
        Some(x) => quote!(Some(#x)),
        None => quote!(None),
    }
}

fn quote_vec<TS>(e: Vec<TS>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    quote! { vec![ #(#e),* ] }
}

fn quote_map<TS>(m: BTreeMap<Label, TS>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    let entries = m.into_iter().map(|(k, v)| {
        let k = quote_label(&k);
        quote!(m.insert(#k, #v);)
    });
    quote! { {
        use std::collections::BTreeMap;
        let mut m = BTreeMap::new();
        #( #entries )*
        m
    } }
}

fn quote_opt_map<TS>(m: BTreeMap<Label, Option<TS>>) -> TokenStream
where
    TS: quote::ToTokens + std::fmt::Debug,
{
    quote_map(m.into_iter().map(|(k, v)| (k, quote_opt(v))).collect())
}
