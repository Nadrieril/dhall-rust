<img src="https://github.com/dhall-lang/dhall-lang/blob/master/img/dhall-logo.svg" width="600" alt="Dhall Logo">

[![Build Status](https://travis-ci.org/Nadrieril/dhall-rust.svg?branch=master)](https://travis-ci.org/Nadrieril/dhall-rust)
[![codecov](https://codecov.io/gh/Nadrieril/dhall-rust/branch/master/graph/badge.svg)](https://codecov.io/gh/Nadrieril/dhall-rust)

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

`serde_dhall` is a nightly crate, and only works with a nightly compiler.
Add this to your `Cargo.toml`:

```toml
[dependencies]
serde_dhall = "0.2.0"
```

Reading Dhall files is easy and leverages the wonderful [`serde`]() library.

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

This implementation currently supports partially the [Dhall
standard](https://github.com/dhall-lang/dhall-lang) version `12.0.0`.

Only local imports are supported, but otherwise the main features are
implemented. See
[here](https://github.com/Nadrieril/dhall-rust/issues?q=is%3Aopen+is%3Aissue+label%3Astandard-compliance)
for a list of missing features.

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
$ rustup toolchain install nightly
```

Then we can manage our building and testing with the [`cargo`](https://crates.io/) dependency manager:

```bash
$ cargo build
```

```bash
$ cargo test
```

Now we can have fun and happy contributing!

## Changelog

- 0.2.0: Update to supporting dhall v12.0.0

- 0.1.0: Initial release

## License

Licensed under the terms of the 2-Clause BSD License ([LICENSE](LICENSE) or
https://opensource.org/licenses/BSD-2-Clause)
