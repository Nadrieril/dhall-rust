use std::io::Error as IOError;

use crate::semantics::resolve::{CyclesStack, ImportLocation};
use crate::syntax::{Import, ParseError};

mod builder;
pub use builder::*;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

#[derive(Debug)]
#[non_exhaustive]
pub enum ErrorKind {
    IO(IOError),
    Parse(ParseError),
    Decode(DecodeError),
    Encode(EncodeError),
    Resolve(ImportError),
    Typecheck(TypeError),
    Cache(CacheError),
}

#[derive(Debug)]
pub enum ImportError {
    Missing,
    MissingEnvVar,
    MissingHome,
    SanityCheck,
    UnexpectedImport(Import<()>),
    ImportCycle(CyclesStack, ImportLocation),
    Url(url::ParseError),
}

#[derive(Debug)]
pub enum DecodeError {
    CBORError(minicbor::decode::Error),
    WrongFormatError(String),
}

#[derive(Debug)]
pub enum EncodeError {
    CBORError(minicbor::encode::Error<core::convert::Infallible>),
}

/// A structured type error
#[derive(Debug)]
pub struct TypeError {
    message: TypeMessage,
}

/// The specific type error
#[derive(Debug)]
pub enum TypeMessage {
    Custom(String),
}

#[derive(Debug)]
pub enum CacheError {
    MissingConfiguration,
    InitialisationError { cause: IOError },
    CacheHashInvalid,
}

impl Error {
    pub fn new(kind: ErrorKind) -> Self {
        Error { kind }
    }
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
}

impl TypeError {
    pub fn new(message: TypeMessage) -> Self {
        TypeError { message }
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use TypeMessage::*;
        let msg = match &self.message {
            Custom(s) => format!("Type error: {}", s),
        };
        write!(f, "{}", msg)
    }
}

impl std::error::Error for TypeError {}

impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let msg = match self {
            EncodeError::CBORError(e) => format!("Encode error: {}", e),
        };
        write!(f, "{}", msg)
    }
}

impl std::error::Error for EncodeError {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.kind {
            ErrorKind::IO(err) => write!(f, "{}", err),
            ErrorKind::Parse(err) => write!(f, "{}", err),
            ErrorKind::Decode(err) => write!(f, "{:?}", err),
            ErrorKind::Encode(err) => write!(f, "{:?}", err),
            ErrorKind::Resolve(err) => write!(f, "{:?}", err),
            ErrorKind::Typecheck(err) => write!(f, "{}", err),
            ErrorKind::Cache(err) => write!(f, "{:?}", err),
        }
    }
}

impl std::error::Error for Error {}
impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error::new(kind)
    }
}
impl From<IOError> for Error {
    fn from(err: IOError) -> Error {
        ErrorKind::IO(err).into()
    }
}
impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        ErrorKind::Parse(err).into()
    }
}
impl From<url::ParseError> for Error {
    fn from(err: url::ParseError) -> Error {
        ErrorKind::Resolve(ImportError::Url(err)).into()
    }
}
impl From<DecodeError> for Error {
    fn from(err: DecodeError) -> Error {
        ErrorKind::Decode(err).into()
    }
}
impl From<EncodeError> for Error {
    fn from(err: EncodeError) -> Error {
        ErrorKind::Encode(err).into()
    }
}
impl From<ImportError> for Error {
    fn from(err: ImportError) -> Error {
        ErrorKind::Resolve(err).into()
    }
}
impl From<TypeError> for Error {
    fn from(err: TypeError) -> Error {
        ErrorKind::Typecheck(err).into()
    }
}
impl From<CacheError> for Error {
    fn from(err: CacheError) -> Error {
        ErrorKind::Cache(err).into()
    }
}
