# `improved_slice_patterns`

A tiny crate that provides two macros to help matching
on `Vec`s and iterators using the syntax of [`slice_patterns`][slice_patterns]

[slice_patterns]: https://doc.rust-lang.org/nightly/unstable-book/language-features/slice-patterns.html

## Changelog

### V2.0

- `match_vec` now returns a `Result` instead of an `Option`. The `Err` variant
is used to return ownership of the passed vec if there was no match.

## License

Licensed under either of

 * Apache License, Version 2.0
   (http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   (http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions
