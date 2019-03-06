extern crate proc_macro;
use dhall_core::*;
use proc_macro2::Literal;
use proc_macro2::TokenStream;
use quote::quote;

#[proc_macro]
pub fn dhall(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_str = input.to_string();
    let expr = parser::parse_expr_pest(&input_str).unwrap();
    let output = dhall_to_tokenstream(&expr);
    output.into()
}

// Returns an expression of type Expr<_, _>. Expects input variables
// to be of type Box<Expr<_, _>> (future-proof for structural sharing).
fn dhall_to_tokenstream(expr: &Expr<X, X>) -> TokenStream {
    use dhall_core::Expr::*;
    match expr {
        Var(V(s, _)) => {
            let v: TokenStream = s.parse().unwrap();
            quote! { {
                let x: Expr<_, _> = (*#v).clone();
                x
            } }
        }
        Lam(x, ref t, ref b) => {
            let x = Literal::string(x);
            let t = dhall_to_tokenstream_bx(t);
            let b = dhall_to_tokenstream_bx(b);
            quote! { Lam(#x, #t, #b) }
        }
        App(ref f, ref a) => {
            let f = dhall_to_tokenstream_bx(f);
            let a = dhall_to_tokenstream_bx(a);
            quote! { App(#f, #a) }
        }
        Builtin(ref b) => {
            let b = builtin_to_tokenstream(b);
            quote! { Builtin(#b) }
        }
        BinOp(ref o, ref a, ref b) => {
            let o = binop_to_tokenstream(o);
            let a = dhall_to_tokenstream_bx(a);
            let b = dhall_to_tokenstream_bx(b);
            quote! { BinOp(#o, #a, #b) }
        }
        OptionalLit(ref t, ref es) => {
            let t =
                option_tks(t.as_ref().map(deref).map(dhall_to_tokenstream_bx));
            let es = vec_tks(es.into_iter().map(dhall_to_tokenstream));
            quote! { OptionalLit(#t, #es) }
        }
        ListLit(ref t, ref es) => {
            let t =
                option_tks(t.as_ref().map(deref).map(dhall_to_tokenstream_bx));
            let es = vec_tks(es.into_iter().map(dhall_to_tokenstream));
            quote! { ListLit(#t, #es) }
        }
        e => unimplemented!("{:?}", e),
    }
}

// Returns an expression of type Box<Expr<_, _>>
fn dhall_to_tokenstream_bx(expr: &Expr<X, X>) -> TokenStream {
    use dhall_core::Expr::*;
    match expr {
        Var(V(s, _)) => {
            let v: TokenStream = s.parse().unwrap();
            quote! { {
                let x: Box<Expr<_, _>> = #v.clone();
                x
            } }
        }
        e => bx(dhall_to_tokenstream(e)),
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
