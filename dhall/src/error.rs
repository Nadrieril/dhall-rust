use quick_error::quick_error;

pub type Result<T> = std::result::Result<T, Error>;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        IO(err: std::io::Error) {
            from()
        }
        Parse(err: dhall_core::ParseError) {
            from()
        }
        Decode(err: crate::binary::DecodeError) {
            from()
        }
        Resolve(err: crate::imports::ImportError) {
            from()
        }
        Typecheck(err: crate::typecheck::TypeError<dhall_core::X>) {
            from()
        }
    }
}
