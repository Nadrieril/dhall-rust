<img src="https://github.com/dhall-lang/dhall-lang/blob/master/img/dhall-logo.svg" width="600" alt="Dhall Logo">

[![Crates.io][crates-badge]][crates-url]
[![Build Status](https://github.com/Nadrieril/dhall-rust/workflows/Test%20suite/badge.svg)](https://github.com/Nadrieril/dhall-rust/actions)
[![codecov](https://codecov.io/gh/Nadrieril/dhall-rust/branch/master/graph/badge.svg)](https://codecov.io/gh/Nadrieril/dhall-rust)

[crates-badge]: https://img.shields.io/crates/v/serde_dhall.svg
[crates-url]: https://crates.io/crates/serde_dhall

Dhall is a programmable configuration language optimized for
maintainability.

You can think of Dhall as: JSON + functions + types + imports

Note that while Dhall is programmable, Dhall is not Turing-complete.  Many
of Dhall's features take advantage of this restriction to provide stronger
safety guarantees and more powerful tooling.

You can find more details about the language by visiting the official website:

* [https://dhall-lang.org](http://dhall-lang.org/)

# `dhall-rust`

This is the Rust implementation of the Dhall configuration language.
It is meant to be used to integrate Dhall in your application.

If you only want to convert Dhall to/from JSON or YAML, you should use the
official tooling instead; instructions can be found
[here](https://docs.dhall-lang.org/tutorials/Getting-started_Generate-JSON-or-YAML.html).

## Usage

For now, the only supported way of integrating Dhall in your application is via
the `serde_dhall` crate, and only parsing is supported.

Add this to your `Cargo.toml`:

```toml
[dependencies]
serde_dhall = "0.3.0"
```

Reading Dhall files is easy and leverages the wonderful [`serde`](https://crates.io/crates/serde) library.

```rust
use std::collections::BTreeMap;

// Some Dhall data
let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";

// Deserialize it to a Rust type.
let deserialized_map: BTreeMap<String, usize> = serde_dhall::from_str(data)?;

let mut expected_map = BTreeMap::new();
expected_map.insert("x".to_string(), 1);
expected_map.insert("y".to_string(), 2);

assert_eq!(deserialized_map, expected_map);
```

## Standard-compliance

This implementation currently supports most of the [Dhall
standard](https://github.com/dhall-lang/dhall-lang) version `14.0.0`.

The main missing features are import caching and import headers. See
[here](https://github.com/Nadrieril/dhall-rust/issues?q=is%3Aopen+is%3Aissue+label%3Astandard-compliance)
for a list of the other missing features.

# Contributing

This section will cover how we can get started on contributing this project.

## Setting up the repository

To get a copy of this repository we can run:

```bash
$ git clone https://github.com/Nadrieril/dhall-rust.git
```

But we also might note that it's better practice to fork the repository to your own workspace.
There you can make changes and submit pull requests against this repository.

After the repositry has been cloned we need to update the [git submodule](https://git-scm.com/book/en/v2/Git-Tools-Submodules)
in the project, i.e. `dhall-lang`. We can do this by running:

```bash
$ git submodule update --init --recursive
```

## Building and Testing

A preferred method among the Rust community for developing is to use [`rustup`](https://rustup.rs/).

It can be installed by running:

```bash
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

or if [nix](https://nixos.org/) is your tool of choice:

```bash
$ nix-shell -p rustup
```

Once `rustup` is installed we can get it to manage our toolchain by running:

```bash
$ rustup toolchain install stable
```

Then we can manage our building and testing with the [`cargo`](https://crates.io/) dependency manager:

```bash
$ cargo build
```

```bash
$ cargo test
```

You can also run tests individually by their name:

```bash
$ cargo test tests::spec::name_of_test
```

Now we can have fun and happy contributing!

## Test suite

The test suite uses tests from the dhall-lang submodule as well as from the
local `dhall/tests` directory.
The various tests are run according to the instructions present in
[`dhall-lang/tests/README.md`](https://github.com/dhall-lang/dhall-lang/blob/master/tests/README.md).

If an output test file (a `fooB.dhall` file) is missing, we will generate it automatically.
This is useful when writing new tests. Don't forget to commit it to git !

If a test fails but you prefer the new output, you can run the test with
`UPDATE_TEST_FILES=1` to overwrite the result file with the new output.
This happens often with ui tests (see below), since we may want to change the
phrasing of errors for example.

```bash
$ UPDATE_TEST_FILES=1 cargo test tests::spec::name_of_test
```

In addition to the usual dhall tests, we additionally run "ui tests", that
ensure that the output of the various errors stays good.
The output of the ui tests is stored in the local `dhall/tests` directory, even
for the tests coming from dhall-lang. They are stored in a `.txt` file with the
same name as the corresponding test.

## Changelog

[???]

- `dhall` now uses the stable Rust toolchain !
- Implement record puns
- Add support for `with` keyword
- Implement remote imports with conservative sanity checking
- Implement `missing` and `env:VAR` imports
- Implement `as Text` and `as Location` imports
- Implement projection by expression
- Implement some normalization simplifications

[0.3.0]

- Update to supporting dhall v14.0.0
- Add support for dotted field syntax
- Disallow Natural literals with leading zeros
- Add support for duplicate record fields
- Update to supporting dhall v13.0.0

[0.2.1]

- Improve documentation and deserialize many more types

[0.2.0]

- Update to supporting dhall v12.0.0

[0.1.0]

- Initial release

## License

Licensed under the terms of the 2-Clause BSD License ([LICENSE](LICENSE) or
https://opensource.org/licenses/BSD-2-Clause)
