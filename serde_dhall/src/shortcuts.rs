use doc_comment::doc_comment;
use std::path::Path;

use crate::{options, FromDhall, Result, SimpleType, StaticType};

// Avoid copy-pasting documentation

#[rustfmt::skip]
macro_rules! gen_doc {
    (@source_desc, str) => {"a string of Dhall text"};
    (@source_desc, file) => {"a Dhall file"};
    (@source_desc, url) => {"a remote url"};

    (@tck_info1, none) => {""};
    (@tck_info1, manual) => {", additionally checking that it matches the supplied type"};
    (@tck_info1, static) => {", additionally checking that it matches the type of `T`"};

    (@tck_info2, none) => {""};
    (@tck_info2, manual) => {" against the supplied type"};
    (@tck_info2, static) => {" against the type of `T`"};

    (@tck_req, $src:tt, none) => {""};
    (@tck_req, $src:tt, manual) => {""};
    (@tck_req, $src:tt, static) => {
        concat!("`T` must implement the [`StaticType`] trait. Use [`from_", stringify!($src),
                "_manual_type`] to provide a type manually.\n")
    };

    (@tck_comment, $src:tt, none) => {
        concat!("For additional type safety, prefer [`from_", stringify!($src), "_static_type`]
                 or [`from_", stringify!($src), "_manual_type`].\n")
    };
    (@tck_comment, $src:tt, manual) => {concat!("See also [`from_", stringify!($src), "_static_type`].\n")};
    (@tck_comment, $src:tt, static) => {""};

    (@run_example, str) => {""};
    (@run_example, file) => {"no_run"};
    (@run_example, url) => {"no_run"};

    ($src:tt, $ty:tt) => {concat!("
Deserialize an instance of type `T` from ", gen_doc!(@source_desc, $src), gen_doc!(@tck_info1, $ty),".

", gen_doc!(@tck_req, $src, $ty), "
This will recursively resolve all imports in the expression, and typecheck it", gen_doc!(@tck_info2, $ty),"
before deserialization. Relative imports will be resolved relative to the current directory.
See [`options`] for more control over this process.

", gen_doc!(@tck_comment, $src, $ty), "

# Example

```", gen_doc!(@run_example, $src), "
# fn main() -> serde_dhall::Result<()> {",
gen_example!($src, $ty), "
# Ok(())
# }
```

[`options`]: options/index.html
[`from_", stringify!($src), "_manual_type`]: fn.from_", stringify!($src), "_manual_type.html
[`from_", stringify!($src), "_static_type`]: fn.from_", stringify!($src), "_static_type.html
[`StaticType`]: trait.StaticType.html
")};
}

#[rustfmt::skip]
macro_rules! gen_example {
    (str, none) => {concat!(r#"
use serde::Deserialize;

// We use serde's derive feature
#[derive(Deserialize)]
struct Point {
    x: u64,
    y: u64,
}

// Some Dhall data
let data = "{ x = 1, y = 1 + 1 } : { x: Natural, y: Natural }";

// Parse the Dhall string as a Point.
let point: Point = serde_dhall::from_str(data)?;

assert_eq!(point.x, 1);
assert_eq!(point.y, 2);
"#)};

    (str, manual) => {concat!(r#"
use std::collections::HashMap;
use serde_dhall::SimpleType;

// Parse a Dhall type
let point_type_str = "{ x: Natural, y: Natural }";
let point_type: SimpleType = serde_dhall::from_str(point_type_str)?;

// Some Dhall data
let point_data = "{ x = 1, y = 1 + 1 }";

// Deserialize the data to a Rust type. This checks that
// the data matches the provided type.
let deserialized_map: HashMap<String, usize> =
        serde_dhall::from_str_manual_type(point_data, &point_type)?;

let mut expected_map = HashMap::new();
expected_map.insert("x".to_string(), 1);
expected_map.insert("y".to_string(), 2);

assert_eq!(deserialized_map, expected_map);
"#)};

    (str, static) => {concat!(r#"
use serde::Deserialize;
use serde_dhall::StaticType;

#[derive(Deserialize, StaticType)]
struct Point {
    x: u64,
    y: u64,
}

// Some Dhall data
let data = "{ x = 1, y = 1 + 1 }";

// Convert the Dhall string to a Point.
let point: Point = serde_dhall::from_str_static_type(data)?;
assert_eq!(point.x, 1);
assert_eq!(point.y, 2);

// Invalid data fails the type validation
let invalid_data = "{ x = 1, z = 0.3 }";
assert!(serde_dhall::from_str_static_type::<Point>(invalid_data).is_err());
"#)};

    (file, none) => {concat!(r#"
use serde::Deserialize;

// We use serde's derive feature
#[derive(Deserialize)]
struct Point {
    x: u64,
    y: u64,
}

// Parse the Dhall file as a Point.
let point: Point = serde_dhall::from_file("foo.dhall")?;
"#)};

    (file, manual) => {concat!(r#"
use std::collections::HashMap;
use serde_dhall::SimpleType;

// Parse a Dhall type
let point_type_str = "{ x: Natural, y: Natural }";
let point_type: SimpleType = serde_dhall::from_str(point_type_str)?;

// Deserialize the data to a Rust type. This checks that
// the data matches the provided type.
let deserialized_map: HashMap<String, usize> =
        serde_dhall::from_file_manual_type("foo.dhall", &point_type)?;
"#)};

    (file, static) => {concat!(r#"
use serde::Deserialize;
use serde_dhall::StaticType;

#[derive(Deserialize, StaticType)]
struct Point {
    x: u64,
    y: u64,
}

// Convert the Dhall string to a Point.
let point: Point = serde_dhall::from_file_static_type("foo.dhall")?;
"#)};

    ($src:tt, $ty:tt) => {""};
}

macro_rules! generate_fn {
    (@generate_src,
        str, $ty:tt, $name:ident,
    ) => {
        generate_fn!(@generate_ty,
            str, $ty, $name,
            (),
            (s: &str),
            (options::from_str(s)),
        );
    };
    (@generate_src,
        file, $ty:tt, $name:ident,
    ) => {
        generate_fn!(@generate_ty,
            file, $ty, $name,
            (P: AsRef<Path>),
            (path: P),
            (options::from_file(path)),
        );
    };

    (@generate_ty,
        $src:tt, none, $name:ident,
        ($($ty_params:tt)*),
        ($($input_args:tt)*),
        ($($create_options:tt)*),
    ) => {
        generate_fn!(@generate,
            $src, none, $name,
            ($($ty_params)*),
            ($($input_args)*),
            (),
            ($($create_options)*),
        );
    };
    (@generate_ty,
        $src:tt, manual, $name:ident,
        ($($ty_params:tt)*),
        ($($input_args:tt)*),
        ($($create_options:tt)*),
    ) => {
        generate_fn!(@generate,
            $src, manual, $name,
            ($($ty_params)*),
            ($($input_args)*, ty: &SimpleType),
            (),
            ($($create_options)* .type_annotation(ty)),
        );
    };
    (@generate_ty,
        $src:tt, static, $name:ident,
        ($($ty_params:tt)*),
        ($($input_args:tt)*),
        ($($create_options:tt)*),
    ) => {
        generate_fn!(@generate,
            $src, static, $name,
            ($($ty_params)*),
            ($($input_args)*),
            (+ StaticType),
            ($($create_options)* .static_type_annotation()),
        );
    };

    (@generate,
        $src:tt, $ty:tt, $name:ident,
        ($($ty_params:tt)*),
        ($($input_args:tt)*),
        ($($extra_bounds:tt)*),
        ($($create_options:tt)*),
    ) => {
        doc_comment! {
            gen_doc!($src, $ty),
            pub fn $name<T, $($ty_params)*> ($($input_args)*) -> Result<T>
            where
                T: FromDhall $($extra_bounds)*,
            {
                $($create_options)* .parse()
            }
        }
    };

    ($src:tt, $ty:tt, $name:ident) => {
        generate_fn!(@generate_src, $src, $ty, $name,);
    };
}

generate_fn!(str, none, from_str);
generate_fn!(str, manual, from_str_manual_type);
generate_fn!(str, static, from_str_static_type);
generate_fn!(file, none, from_file);
generate_fn!(file, manual, from_file_manual_type);
generate_fn!(file, static, from_file_static_type);
