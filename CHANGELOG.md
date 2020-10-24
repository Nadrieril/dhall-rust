# Changelog

#### [Unreleased]

- Add a `SimpleValue` type to the public interface (https://github.com/Nadrieril/dhall-rust/pull/183)

#### [0.7.2] - 2020-10-24

- Fix `reqwest` feature (https://github.com/Nadrieril/dhall-rust/pull/182)

#### [0.7.1] - 2020-10-16

- Add a `Display` impl for `SimpleType` (https://github.com/Nadrieril/dhall-rust/issues/179)
- Make reqwest an optional dependency (https://github.com/Nadrieril/dhall-rust/issues/178)

#### [0.7.0] - 2020-09-15

- BREAKING CHANGE: Support Dhall v18.0.0

#### [0.6.0] - 2020-08-05

- Allow trailing delimiters in records, lists, etc.
- BREAKING CHANGE: Support Dhall v17.0.0

    See https://github.com/dhall-lang/dhall-lang/releases/tag/v16.0.0 and
    https://github.com/dhall-lang/dhall-lang/releases/tag/v17.0.0 for details.

- Fix running tests on Windows. Developing on this lib should now be possible on Windows.

#### [0.5.3] - 2020-05-30

- Support import caching
- Support building on Windows
- Support building to wasm (but imports don't work)

#### [0.5.2] - 2020-04-12

- Fix #162
- Update to supporting Dhall v15.0.0
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
[Unreleased]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.2...HEAD
[0.7.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.1...serde_dhall-v0.7.2
[0.7.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.0...serde_dhall-v0.7.1
[0.7.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.6.0...serde_dhall-v0.7.0
[0.6.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.3...serde_dhall-v0.6.0
[0.5.3]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.2...serde_dhall-v0.5.3
[0.5.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.1...serde_dhall-v0.5.2
[0.5.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.0...serde_dhall-v0.5.1
[0.5.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.4.0...serde_dhall-v0.5.0
