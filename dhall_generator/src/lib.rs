extern crate proc_macro;
use dhall_core::context::Context;
use dhall_core::*;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;
use std::rc::Rc;

#[proc_macro]
pub fn dhall_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr: Rc<Expr<X, Import>> = parser::parse_expr(&input_str).unwrap();
    let no_import =
        |_: &Import| -> X { panic!("Don't use import in dhall!()") };
    let expr = expr.map_embed(&no_import);
    let output = dhall_to_tokenstream_bx(&expr, &Context::new());
    output.into()
}

// Returns an expression of type Expr<_, _>. Expects interpolated variables
// to be of type Rc<Expr<_, _>>.
fn dhall_to_tokenstream(
    expr: &Expr<X, X>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    use dhall_core::Expr::*;
    match expr {
        e @ Var(_) => {
            let v = dhall_to_tokenstream_bx(e, ctx);
            quote! { *#v }
        }
        Pi(x, t, b) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            let b = dhall_to_tokenstream_bx(b, &ctx.insert(x.clone(), ()));
            let x = label_to_tokenstream(x);
            quote! { Pi(#x, #t, #b) }
        }
        Lam(x, t, b) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            let b = dhall_to_tokenstream_bx(b, &ctx.insert(x.clone(), ()));
            let x = label_to_tokenstream(x);
            quote! { Lam(#x, #t, #b) }
        }
        App(f, a) => {
            let f = dhall_to_tokenstream_bx(f, ctx);
            let a = vec_to_tokenstream(a, ctx);
            quote! { App(#f, #a) }
        }
        Const(c) => {
            let c = const_to_tokenstream(*c);
            quote! { Const(#c) }
        }
        Builtin(b) => {
            let b = builtin_to_tokenstream(*b);
            quote! { Builtin(#b) }
        }
        BinOp(o, a, b) => {
            let o = binop_to_tokenstream(*o);
            let a = dhall_to_tokenstream_bx(a, ctx);
            let b = dhall_to_tokenstream_bx(b, ctx);
            quote! { BinOp(#o, #a, #b) }
        }
        OptionalLit(t, e) => {
            let t = option_to_tokenstream(t, ctx);
            let e = option_to_tokenstream(e, ctx);
            quote! { OptionalLit(#t, #e) }
        }
        ListLit(t, es) => {
            let t = option_to_tokenstream(t, ctx);
            let es = vec_to_tokenstream(es, ctx);
            quote! { ListLit(#t, #es) }
        }
        Record(m) => {
            let m = map_to_tokenstream(m, ctx);
            quote! { Record(#m) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type Rc<Expr<_, _>>
fn dhall_to_tokenstream_bx(
    expr: &Expr<X, X>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    use dhall_core::Expr::*;
    match expr {
        Var(V(s, n)) => {
            match ctx.lookup(&s, *n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    let s: String = s.clone().into();
                    quote! { bx(Var(V(#s.into(), #n))) }
                }
                // Free variable; interpolates as a rust variable
                None => {
                    let s: String = s.clone().into();
                    // TODO: insert appropriate shifts ?
                    let v: TokenStream = s.parse().unwrap();
                    quote! { {
                        let x: Rc<Expr<_, _>> = #v.clone();
                        x
                    } }
                }
            }
        }
        e => bx(dhall_to_tokenstream(e, ctx)),
    }
}

fn builtin_to_tokenstream(b: Builtin) -> TokenStream {
    format!("{:?}", b).parse().unwrap()
}

fn const_to_tokenstream(c: Const) -> TokenStream {
    format!("{:?}", c).parse().unwrap()
}

fn binop_to_tokenstream(b: BinOp) -> TokenStream {
    format!("{:?}", b).parse().unwrap()
}

fn label_to_tokenstream(l: &Label) -> TokenStream {
    let l = String::from(l.clone());
    quote! { #l.into() }
}

fn map_to_tokenstream(
    m: &BTreeMap<Label, Rc<Expr<X, X>>>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    let (keys, values): (Vec<TokenStream>, Vec<TokenStream>) = m
        .iter()
        .map(|(k, v)| {
            (label_to_tokenstream(k), dhall_to_tokenstream_bx(&*v, ctx))
        })
        .unzip();
    quote! { {
        let mut m = BTreeMap::new();
        #( m.insert(#keys, #values); )*
        m
    } }
}

fn option_to_tokenstream(
    e: &Option<Rc<Expr<X, X>>>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    let e = e.as_ref().map(|x| dhall_to_tokenstream_bx(x, ctx));
    match e {
        Some(x) => quote! { Some(#x) },
        None => quote! { None },
    }
}

fn vec_to_tokenstream(
    e: &Vec<Rc<Expr<X, X>>>,
    ctx: &Context<Label, ()>,
) -> TokenStream {
    let e = e.iter().map(|x| dhall_to_tokenstream_bx(&**x, ctx));
    quote! { vec![ #(#e),* ] }
}

fn bx(x: TokenStream) -> TokenStream {
    quote! { bx(#x) }
}
