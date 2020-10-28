use crate::{SimpleType, StaticType};

pub(crate) mod de;
pub(crate) mod ser;

#[derive(Debug, Clone, Copy)]
pub struct NoAnnot;
#[derive(Debug, Clone, Copy)]
pub struct ManualAnnot<'ty>(&'ty SimpleType);
#[derive(Debug, Clone, Copy)]
pub struct StaticAnnot;

pub trait TypeAnnot: Copy {}
pub trait HasAnnot<A: TypeAnnot> {
    fn get_annot(a: A) -> Option<SimpleType>;
}

impl TypeAnnot for NoAnnot {}
impl TypeAnnot for ManualAnnot<'_> {}
impl TypeAnnot for StaticAnnot {}

impl<T> HasAnnot<NoAnnot> for T {
    fn get_annot(_: NoAnnot) -> Option<SimpleType> {
        None
    }
}
impl<T> HasAnnot<ManualAnnot<'_>> for T {
    fn get_annot(a: ManualAnnot<'_>) -> Option<SimpleType> {
        Some(a.0.clone())
    }
}
impl<T: StaticType> HasAnnot<StaticAnnot> for T {
    fn get_annot(_: StaticAnnot) -> Option<SimpleType> {
        Some(T::static_type())
    }
}
