#[cfg(test)]
mod tests {
    #![rustfmt::skip]
    // See ../build.rs
    include!(concat!(env!("OUT_DIR"), "/parser_tests.rs"));
}
