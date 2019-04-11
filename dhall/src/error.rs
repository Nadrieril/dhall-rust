use quick_error::quick_error;

pub type Result<T> = std::result::Result<T, Error>;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        IO(err: std::io::Error) {
            from()
            display("{}", err)
        }
        Parse(err: dhall_core::ParseError) {
            from()
            display("{}", err)
        }
        Decode(err: crate::binary::DecodeError) {
            from()
            display("{:?}", err)
        }
        Resolve(err: crate::imports::ImportError) {
            from()
            display("{}", err)
        }
        Typecheck(err: crate::typecheck::TypeError<dhall_core::X>) {
            from()
            display("{:?}", err)
        }
        Deserialize(err: String) {
            display("{}", err)
        }
    }
}
