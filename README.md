# `dhall-rust`

[![Build Status](https://travis-ci.org/Nadrieril/dhall-rust.svg?branch=master)](https://travis-ci.org/Nadrieril/dhall-rust)
[![codecov](https://codecov.io/gh/Nadrieril/dhall-rust/branch/master/graph/badge.svg)](https://codecov.io/gh/Nadrieril/dhall-rust)

This is a WIP implementation in Rust of the [dhall](https://dhall-lang.org) configuration format/programming language.

This language is defined by a [standard](https://github.com/dhall-lang/dhall-lang), and this implementation tries its best to respect it.

This is a nightly crate, so you will need a nightly compiler to use it.

This is still quite unstable so use at your own risk. Documentation is severely lacking for now, sorry !

## Standard-compliance

- Parsing: 100%
- Imports: 10%
- Normalization: 83%
- Typechecking: 83%

You can see what's missing from the commented out tests in `dhall/src/normalize.rs` and `dhall/src/typecheck.rs`.

## License

Licensed under the terms of the 2-Clause BSD License ([LICENSE](LICENSE) or
https://opensource.org/licenses/BSD-2-Clause)
