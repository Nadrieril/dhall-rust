#![cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

use serde_dhall::{from_str, FromDhall, StaticType};

#[wasm_bindgen_test]
fn test() {
    fn parse<T: FromDhall + StaticType>(s: &str) -> T {
        from_str(s).static_type_annotation().parse().unwrap()
    }
    assert_eq!(parse::<Vec<u64>>("[1, 2]"), vec![1, 2]);
}
