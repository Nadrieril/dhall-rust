// This crate only contains the grammar-generated parser. The rest of the
// parser is in dhall_core. This separation is because compiling the
// grammar-generated parser is extremely slow.
// See the https://pest.rs documentation for details on what this crate contains.
// The pest file is auto-generated and is located at ./dhall.pest.
// It is generated from grammar.abnf in a rather straightforward manner. Some
// additional overrides are done in ../build.rs.
// The lines that are commented out in ./dhall.pest.visibility are marked as
// silent (see pest docs for what that means) in the generated pest file.
include!(concat!(env!("OUT_DIR"), "/grammar.rs"));
