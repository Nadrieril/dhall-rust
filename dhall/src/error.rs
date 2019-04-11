pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    IO(std::io::Error),
    Parse(dhall_core::ParseError),
    Decode(crate::binary::DecodeError),
    Resolve(crate::imports::ImportError),
    Typecheck(crate::typecheck::TypeError<dhall_core::X>),
    Deserialize(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "{}", err),
            Error::Parse(err) => write!(f, "{}", err),
            Error::Decode(err) => write!(f, "{:?}", err),
            Error::Resolve(err) => write!(f, "{:?}", err),
            Error::Typecheck(err) => write!(f, "{:?}", err),
            Error::Deserialize(err) => write!(f, "{}", err),
        }
    }
}

impl std::error::Error for Error {}
impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Error {
        Error::IO(err)
    }
}
impl From<dhall_core::ParseError> for Error {
    fn from(err: dhall_core::ParseError) -> Error {
        Error::Parse(err)
    }
}
impl From<crate::binary::DecodeError> for Error {
    fn from(err: crate::binary::DecodeError) -> Error {
        Error::Decode(err)
    }
}
impl From<crate::imports::ImportError> for Error {
    fn from(err: crate::imports::ImportError) -> Error {
        Error::Resolve(err)
    }
}
impl From<crate::typecheck::TypeError<dhall_core::X>> for Error {
    fn from(err: crate::typecheck::TypeError<dhall_core::X>) -> Error {
        Error::Typecheck(err)
    }
}
