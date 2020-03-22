use dhall::error::Error as DhallError;

/// TODO
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
#[non_exhaustive]
/// TODO
pub enum Error {
    Dhall(DhallError),
    Deserialize(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Dhall(err) => write!(f, "{}", err),
            Error::Deserialize(err) => write!(f, "{}", err),
        }
    }
}

impl std::error::Error for Error {}

impl serde::de::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Error::Deserialize(msg.to_string())
    }
}
