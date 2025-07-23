# Changelog

#### [Unreleased]

#### [0.13.0] - unreleased

- BREAKING CHANGE: Change minimum supported version to 1.76.0 because of the `wasm_bindgen` dependency

#### [0.12.1] - 2023-02-01

#### [0.12.0] - 2022-08-15

- BREAKING CHANGE: Change minimum supported version to 1.60.0 because of `minicbor` dependency
- Use `minicbor` instead of the deprecated `serde_cbor` (https://github.com/Nadrieril/dhall-rust/pull/236)
- BREAKING CHANGE: Change minimum supported version to 1.58.0 because of `libtest-mimic` dependency (https://github.com/Nadrieril/dhall-rust/pull/234)
- Implement ToDhall for SimpleType (https://github.com/Nadrieril/dhall-rust/pull/233)

#### [0.11.2] - 2022-06-24

- Implement StaticType for u16 (https://github.com/Nadrieril/dhall-rust/pull/230)

#### [0.11.1] - 2022-05-19

- Improve error message on duplicate non-mergeable fields (https://github.com/Nadrieril/dhall-rust/pull/229)

#### [0.11.0] - 2022-01-01

- Fix reading file with a path relative to HOME (https://github.com/Nadrieril/dhall-rust/pull/224)
- Change `?` to only fall back on absent imports
- Add support for custom builtin types (https://github.com/Nadrieril/dhall-rust/pull/220)
- Add support for Unix shebangs
- `StaticType` derive supports records in Union Types (https://github.com/Nadrieril/dhall-rust/pull/219)
- BREAKING CHANGE: Change minimum supported version to 1.46.0 because of reqwest dependency.

#### [0.10.1] - 2021-04-03

#### [0.10.0] - 2021-02-04

- BREAKING CHANGE: Change minimum supported version to 1.44.0.
- BREAKING CHANGE: Support dhall v20.0.0
- `if` can return a type (https://github.com/Nadrieril/dhall-rust/pull/202)

#### [0.9.0] - 2020-11-20

- BREAKING CHANGE: Support Dhall v19.0.0
- Support reading a CBOR-encoded binary file (https://github.com/Nadrieril/dhall-rust/issues/199)

#### [0.8.0] - 2020-10-28

- Implement serialization (https://github.com/Nadrieril/dhall-rust/issues/164)
- BREAKING CHANGE: use u64/i64 instead of usize/isize in `NumKind`

#### [0.7.5] - 2020-10-28

- Make `SimpleValue` deserializable within other types (https://github.com/Nadrieril/dhall-rust/issues/184)

#### [0.7.4] - 2020-10-25

- Add new `Text/replace` builtin (https://github.com/Nadrieril/dhall-rust/pull/181)

#### [0.7.3] - 2020-10-24

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
[Unreleased]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.12.1...HEAD
[0.12.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.12.0...serde_dhall-v0.12.1
[0.12.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.11.2...serde_dhall-v0.12.0
[0.11.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.11.1...serde_dhall-v0.11.2
[0.11.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.11.0...serde_dhall-v0.11.1
[0.11.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.10.1...serde_dhall-v0.11.0
[0.10.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.10.0...serde_dhall-v0.10.1
[0.10.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.9.0...serde_dhall-v0.10.0
[0.9.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.8.0...serde_dhall-v0.9.0
[0.8.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.5...serde_dhall-v0.8.0
[0.7.5]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.4...serde_dhall-v0.7.5
[0.7.4]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.3...serde_dhall-v0.7.4
[0.7.3]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.2...serde_dhall-v0.7.3
[0.7.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.1...serde_dhall-v0.7.2
[0.7.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.7.0...serde_dhall-v0.7.1
[0.7.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.6.0...serde_dhall-v0.7.0
[0.6.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.3...serde_dhall-v0.6.0
[0.5.3]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.2...serde_dhall-v0.5.3
[0.5.2]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.1...serde_dhall-v0.5.2
[0.5.1]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.5.0...serde_dhall-v0.5.1
[0.5.0]: https://github.com/Nadrieril/dhall-rust/compare/serde_dhall-v0.4.0...serde_dhall-v0.5.0
