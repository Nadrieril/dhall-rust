extern crate proc_macro;
use dhall_core::context::Context;
use dhall_core::*;
use proc_macro2::Literal;
use proc_macro2::TokenStream;
use quote::quote;

#[proc_macro]
pub fn dhall(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr: Box<Expr<X, Import>> = parser::parse_expr(&input_str).unwrap();
    let no_import =
        |_: &Import| -> X { panic!("Don't use import in dhall!()") };
    let expr = expr.map_embed(&no_import);
    let output = dhall_to_tokenstream(&expr, &Context::new());
    output.into()
}

// Returns an expression of type Expr<_, _>. Expects input variables
// to be of type Box<Expr<_, _>> (future-proof for structural sharing).
fn dhall_to_tokenstream<'i>(
    expr: &Expr<'i, X, X>,
    ctx: &Context<'i, ()>,
) -> TokenStream {
    use dhall_core::Expr_::*;
    match expr {
        e @ Var(_) => {
            let v = dhall_to_tokenstream_bx(e, ctx);
            quote! { *#v }
        }
        Lam(x, t, b) => {
            let t = dhall_to_tokenstream_bx(t, ctx);
            let b = dhall_to_tokenstream_bx(b, &ctx.insert(x, ()));
            let x = Literal::string(x);
            quote! { Lam(#x, #t, #b) }
        }
        App(f, a) => {
            let f = dhall_to_tokenstream_bx(f, ctx);
            let a = dhall_to_tokenstream_bx(a, ctx);
            quote! { App(#f, #a) }
        }
        Builtin(b) => {
            let b = builtin_to_tokenstream(b);
            quote! { Builtin(#b) }
        }
        BinOp(o, a, b) => {
            let o = binop_to_tokenstream(o);
            let a = dhall_to_tokenstream_bx(a, ctx);
            let b = dhall_to_tokenstream_bx(b, ctx);
            quote! { BinOp(#o, #a, #b) }
        }
        OptionalLit(t, es) => {
            let t = option_tks(
                t.as_ref()
                    .map(deref)
                    .map(|x| dhall_to_tokenstream_bx(x, ctx)),
            );
            let es =
                vec_tks(es.into_iter().map(|x| dhall_to_tokenstream(x, ctx)));
            quote! { OptionalLit(#t, #es) }
        }
        ListLit(t, es) => {
            let t = option_tks(
                t.as_ref()
                    .map(deref)
                    .map(|x| dhall_to_tokenstream_bx(x, ctx)),
            );
            let es =
                vec_tks(es.into_iter().map(|x| dhall_to_tokenstream(x, ctx)));
            quote! { ListLit(#t, #es) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type Box<Expr<_, _>>
fn dhall_to_tokenstream_bx<'i>(
    expr: &Expr<'i, X, X>,
    ctx: &Context<'i, ()>,
) -> TokenStream {
    use dhall_core::Expr_::*;
    match expr {
        Var(V(s, n)) => {
            match ctx.lookup(s, *n) {
                // Non-free variable; interpolates as itself
                Some(()) => {
                    quote! { bx(Var(V(#s, #n))) }
                }
                // Free variable; interpolates as a rust variable
                None => {
                    // TODO: insert appropriate shifts ?
                    let v: TokenStream = s.parse().unwrap();
                    quote! { {
                        let x: Box<Expr<_, _>> = #v.clone();
                        x
                    } }
                }
            }
        }
        e => bx(dhall_to_tokenstream(e, ctx)),
    }
}

fn builtin_to_tokenstream(b: &Builtin) -> TokenStream {
    format!("{:?}", b).parse().unwrap()
}

fn binop_to_tokenstream(b: &BinOp) -> TokenStream {
    format!("{:?}", b).parse().unwrap()
}

fn deref<T>(x: &Box<T>) -> &T {
    &*x
}

fn bx(x: TokenStream) -> TokenStream {
    quote! { bx(#x) }
}

fn option_tks(x: Option<TokenStream>) -> TokenStream {
    match x {
        Some(x) => quote! { Some(#x) },
        None => quote! { None },
    }
}

fn vec_tks<T>(x: T) -> TokenStream
where
    T: Iterator<Item = TokenStream>,
{
    quote! { vec![ #(#x),* ] }
}
