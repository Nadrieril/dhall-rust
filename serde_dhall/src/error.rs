use dhall::error::Error as DhallError;

/// Alias for a `Result` with the error type `serde_dhall::Error`.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur when deserializing Dhall data.
#[derive(Debug)]
pub struct Error(pub(crate) ErrorKind);

#[derive(Debug)]
pub(crate) enum ErrorKind {
    Dhall(DhallError),
    Deserialize(String),
    Serialize(String),
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error(kind)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            ErrorKind::Dhall(err) => write!(f, "{}", err),
            ErrorKind::Deserialize(err) => write!(f, "{}", err),
            ErrorKind::Serialize(err) => write!(f, "{}", err),
        }
    }
}

impl std::error::Error for Error {}

impl serde::de::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        ErrorKind::Deserialize(msg.to_string()).into()
    }
}

impl serde::ser::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        ErrorKind::Serialize(msg.to_string()).into()
    }
}
