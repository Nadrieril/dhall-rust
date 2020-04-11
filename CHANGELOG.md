# Changelog

#### [Unreleased]

- Allow unions with mixed kinds
- Adjust precedence of `===` and `with`
- Fix running tests on Windows. Developing on this lib should now be possible on Windows.

#### [0.5.3] - 2020-05-30

- Support import caching
- Support building on Windows
- Support building to wasm (but imports don't work)

#### [0.5.2] - 2020-04-12

- Fix #162
- Update to supporting dhall v15.0.0
- Deserialize `Prelude.Map` and `toMap` to a map instead of a list.

#### [0.5.1] - 2020-04-09

- Small fixes

#### [0.5.0] - 2020-04-05

- Add `serde_dhall::from_file` to read a Dhall file directly.
- BREAKING CHANGE: reworked most of the `serde_dhall` API

    You need to replace uses of `from_str(s)` with `from_str(s).parse()`. The
    various type annotation methods have been removed; use instead the methods on
    the `Deserializer` struct.

#### 0.4.0

- `dhall` now uses the stable Rust toolchain !
- Implement record puns
- Add support for `with` keyword
- Implement remote imports with conservative sanity checking
- Implement `missing` and `env:VAR` imports
- Implement `as Text` and `as Location` imports
- Implement projection by expression
- Implement some normalization simplifications

#### 0.3.0

- Update to supporting dhall v14.0.0
- Add support for dotted field syntax
- Disallow Natural literals with leading zeros
- Add support for duplicate record fields
- Update to supporting dhall v13.0.0

#### 0.2.1

- Improve documentation and deserialize many more types

#### 0.2.0

- Update to supporting dhall v12.0.0

#### 0.1.0

- Initial release

<!-- next-url -->
[Unreleased]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.3...HEAD
[0.5.3]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.2...serde_dhall-v0.5.3
[0.5.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.1...serde_dhall-v0.5.2
[0.5.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.0...serde_dhall-v0.5.1
[0.5.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.4.0...serde_dhall-v0.5.0
