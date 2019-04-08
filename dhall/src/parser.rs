#[cfg(test)]
mod spec_tests {
    #![rustfmt::skip]
    // See ../build.rs
    include!(concat!(env!("OUT_DIR"), "/parser_tests.rs"));
}
