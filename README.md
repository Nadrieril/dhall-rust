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
- Normalization: 100%
- Typechecking: 83%

You can see what's missing from the commented out tests in `dhall/src/normalize.rs` and `dhall/src/typecheck.rs`.

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

## License

Licensed under the terms of the 2-Clause BSD License ([LICENSE](LICENSE) or
https://opensource.org/licenses/BSD-2-Clause)
