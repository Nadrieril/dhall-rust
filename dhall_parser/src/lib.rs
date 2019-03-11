// This crate only contains the grammar-generated parser. The rest of the
// parser is in dhall_core. This separation is because compiling the
// grammar-generated parser is extremely slow. Eventually, the whole parser
// should probably be moved to here.
// See the https://pest.rs documentation for details on what this crate contains.
// The pest file is auto-generated and is located at ./dhall.pest.
// It is generated from grammar.abnf in a rather straightforward manner. Some
// additional overrides are done in ../build.rs.
// The lines that are commented out in ./dhall.pest.visibility are marked as
// silent (see pest docs for what that means) in the generated pest file.
// The abnf file has quite a lot of modifications compared to the one from
// the standard. Hopefully those changes should be merged upstream, but for now
// feel free to edit it to make parsing easier.
include!(concat!(env!("OUT_DIR"), "/grammar.rs"));
