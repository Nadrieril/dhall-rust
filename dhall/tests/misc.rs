use dhall::error::Error;
use dhall::semantics::*;
use dhall::syntax::*;
use dhall::*;

/// Test that showcases someone using the `dhall` crate directly for a simple operation. If
/// possible try not to break this too much. See
/// https://github.com/Nadrieril/dhall-rust/issues/208.
#[test]
fn manual_function_application() {
    /// Apply a `Natural -> Natural` function to an argument.
    fn apply_natnat_fn<'cx>(f: &Nir<'cx>, n: u64) -> u64 {
        let n_nir = Nir::from_kind(NirKind::Num(NumKind::Natural(n)));
        match f.app(n_nir).kind() {
            NirKind::Num(NumKind::Natural(m)) => *m,
            _ => panic!("`f` was not `Natural -> Natural`"),
        }
    }
    /// Auxiliary function to make `?` work.
    fn run<'cx>(cx: Ctxt<'cx>) -> Result<(), Error> {
        let f_ty = "Natural -> Natural";
        let f = "\\(x: Natural) -> x + 3";
        let f_ty = Parsed::parse_str(f_ty)?
            .skip_resolve(cx)?
            .typecheck(cx)?
            .normalize(cx);
        let f = Parsed::parse_str(f)?
            .skip_resolve(cx)?
            .typecheck_with(cx, &f_ty.to_hir())?
            .normalize(cx);
        for i in 0..5 {
            let n = apply_natnat_fn(f.as_nir(), i);
            assert_eq!(n, i + 3);
        }
        Ok(())
    }
    Ctxt::with_new(run).unwrap();
}
