use crate::{Result, SimpleType, StaticType, ToDhall};

#[derive(Debug, Clone, Copy)]
pub struct NoAnnot;
#[derive(Debug, Clone, Copy)]
pub struct ManualAnnot<'ty>(&'ty SimpleType);
#[derive(Debug, Clone, Copy)]
pub struct StaticAnnot;

pub trait RequiredAnnot<A> {
    fn get_annot(a: &A) -> SimpleType;
}
impl<'ty, T> RequiredAnnot<ManualAnnot<'ty>> for T {
    fn get_annot(a: &ManualAnnot<'ty>) -> SimpleType {
        a.0.clone()
    }
}
impl<T: StaticType> RequiredAnnot<StaticAnnot> for T {
    fn get_annot(_: &StaticAnnot) -> SimpleType {
        T::static_type()
    }
}

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

impl<'a, T, A> Serializer<'a, T, A> {
    pub fn to_string(&self) -> Result<String>
    where
        T: ToDhall + RequiredAnnot<A>,
    {
        let val = self.data.to_dhall(&T::get_annot(&self.annot))?;
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
