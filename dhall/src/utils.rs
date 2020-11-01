use std::fs::File;
use std::io::Read;
use std::path::Path;

use crate::error::Error;

// Compute the sha256 hash of a bitstring.
pub fn sha256_hash(data: &[u8]) -> Box<[u8]> {
    use sha2::Digest;
    sha2::Sha256::digest(data).as_slice().into()
}

pub fn read_binary_file(path: impl AsRef<Path>) -> Result<Box<[u8]>, Error> {
    let mut buffer = Vec::new();
    File::open(path)?.read_to_end(&mut buffer)?;
    Ok(buffer.into())
}
