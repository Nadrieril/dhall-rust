use crate::expr::Type;
use crate::traits::Deserialize;
use crate::traits::Result;

impl<'a, T: serde::Deserialize<'a>> Deserialize<'a> for T {
    fn from_str(_s: &'a str, _ty: Option<&Type>) -> Result<Self> {
        unimplemented!()
    }
}
