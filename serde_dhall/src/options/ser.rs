use crate::options::{HasAnnot, ManualAnnot, NoAnnot, StaticAnnot, TypeAnnot};
use crate::{Result, SimpleType, ToDhall};

#[derive(Debug, Clone)]
pub struct Serializer<'a, T, A> {
    data: &'a T,
    annot: A,
}

impl<'a, T> Serializer<'a, T, NoAnnot> {
    pub fn type_annotation<'ty>(
        self,
        ty: &'ty SimpleType,
    ) -> Serializer<'a, T, ManualAnnot<'ty>> {
        Serializer {
            annot: ManualAnnot(ty),
            data: self.data,
        }
    }

    pub fn static_type_annotation(self) -> Serializer<'a, T, StaticAnnot> {
        Serializer {
            annot: StaticAnnot,
            data: self.data,
        }
    }
}

impl<'a, T, A> Serializer<'a, T, A>
where
    A: TypeAnnot,
{
    pub fn to_string(&self) -> Result<String>
    where
        T: ToDhall + HasAnnot<A>,
    {
        let val = self.data.to_dhall(T::get_annot(self.annot).as_ref())?;
        Ok(val.to_string())
    }
}

pub fn serialize<'a, T>(data: &'a T) -> Serializer<'a, T, NoAnnot>
where
    T: ToDhall,
{
    Serializer {
        data,
        annot: NoAnnot,
    }
}
