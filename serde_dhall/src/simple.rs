use std::collections::{BTreeMap, HashMap};

use dhall::semantics::{Hir, HirKind, Nir, NirKind};
use dhall::syntax::{Builtin, ExprKind, NumKind, Span};

use crate::{Deserialize, Error, Result, Sealed, Value};

/// A simple value of the kind that can be decoded with serde
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SimpleValue {
    Num(NumKind),
    Text(String),
    Optional(Option<Box<SimpleValue>>),
    List(Vec<SimpleValue>),
    Record(BTreeMap<String, SimpleValue>),
    Union(String, Option<Box<SimpleValue>>),
}

/// The type of a value that can be decoded by Serde, like `{ x: Bool, y: List Natural }`.
///
/// A `SimpleType` is used when deserializing values to ensure they are of the expected type.
/// Rather than letting `serde` handle potential type mismatches, this uses the type-checking
/// capabilities of Dhall to catch errors early and cleanly indicate in the user's code where the
/// mismatch happened.
///
/// You would typically not manipulate `SimpleType`s by hand but rather let Rust infer it for your
/// datatype using the [`StaticType`][TODO] trait, and methods that require it like
/// [`from_file_static_type`][TODO] and [`Options::static_type_annotation`][TODO]. If you need to supply a
/// `SimpleType` manually however, you can deserialize it like any other Dhall value using the
/// functions provided by this crate.
///
/// # Examples
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::HashMap;
/// use serde_dhall::SimpleType;
///
/// let ty: SimpleType =
///     serde_dhall::from_str("{ x: Natural, y: Natural }")?;
///
/// let mut map = HashMap::new();
/// map.insert("x".to_string(), SimpleType::Natural);
/// map.insert("y".to_string(), SimpleType::Natural);
/// assert_eq!(ty, SimpleType::Record(map));
/// # Ok(())
/// # }
/// ```
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use serde_dhall::{SimpleType, StaticType};
///
/// #[derive(StaticType)]
/// struct Foo {
///     x: bool,
///     y: Vec<u64>,
/// }
///
/// let ty: SimpleType =
///     serde_dhall::from_str("{ x: Bool, y: List Natural }")?;
///
/// assert_eq!(ty, Foo::static_type());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpleType {
    /// Corresponds to the Dhall type `Bool`
    Bool,
    /// Corresponds to the Dhall type `Natural`
    Natural,
    /// Corresponds to the Dhall type `Integer`
    Integer,
    /// Corresponds to the Dhall type `Double`
    Double,
    /// Corresponds to the Dhall type `Text`
    Text,
    /// Corresponds to the Dhall type `Optional T`
    Optional(Box<SimpleType>),
    /// Corresponds to the Dhall type `List T`
    List(Box<SimpleType>),
    /// Corresponds to the Dhall type `{ x : T, y : U }`
    Record(HashMap<String, SimpleType>),
    /// Corresponds to the Dhall type `< x : T | y : U >`
    Union(HashMap<String, Option<SimpleType>>),
}

impl SimpleValue {
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
        Some(match nir.kind() {
            NirKind::Num(lit) => SimpleValue::Num(lit.clone()),
            NirKind::TextLit(x) => SimpleValue::Text(
                x.as_text()
                    .expect("Normal form should ensure the text is a string"),
            ),
            NirKind::EmptyOptionalLit(_) => SimpleValue::Optional(None),
            NirKind::NEOptionalLit(x) => {
                SimpleValue::Optional(Some(Box::new(Self::from_nir(x)?)))
            }
            NirKind::EmptyListLit(_) => SimpleValue::List(vec![]),
            NirKind::NEListLit(xs) => SimpleValue::List(
                xs.iter().map(Self::from_nir).collect::<Option<_>>()?,
            ),
            NirKind::RecordLit(kvs) => SimpleValue::Record(
                kvs.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionLit(field, x, _) => SimpleValue::Union(
                field.into(),
                Some(Box::new(Self::from_nir(x)?)),
            ),
            NirKind::UnionConstructor(field, ty)
                if ty.get(field).map(|f| f.is_some()) == Some(false) =>
            {
                SimpleValue::Union(field.into(), None)
            }
            _ => return None,
        })
    }
}

impl SimpleType {
    pub(crate) fn from_nir(nir: &Nir) -> Option<Self> {
        Some(match nir.kind() {
            NirKind::BuiltinType(b) => match b {
                Builtin::Bool => SimpleType::Bool,
                Builtin::Natural => SimpleType::Natural,
                Builtin::Integer => SimpleType::Integer,
                Builtin::Double => SimpleType::Double,
                Builtin::Text => SimpleType::Text,
                _ => unreachable!(),
            },
            NirKind::OptionalType(t) => {
                SimpleType::Optional(Box::new(Self::from_nir(t)?))
            }
            NirKind::ListType(t) => {
                SimpleType::List(Box::new(Self::from_nir(t)?))
            }
            NirKind::RecordType(kts) => SimpleType::Record(
                kts.iter()
                    .map(|(k, v)| Some((k.into(), Self::from_nir(v)?)))
                    .collect::<Option<_>>()?,
            ),
            NirKind::UnionType(kts) => SimpleType::Union(
                kts.iter()
                    .map(|(k, v)| {
                        Some((
                            k.into(),
                            v.as_ref()
                                .map(|v| Ok(Self::from_nir(v)?))
                                .transpose()?,
                        ))
                    })
                    .collect::<Option<_>>()?,
            ),
            _ => return None,
        })
    }

    pub(crate) fn to_value(&self) -> Value {
        Value {
            hir: self.to_hir(),
            as_simple_val: None,
            as_simple_ty: Some(self.clone()),
        }
    }
    pub(crate) fn to_hir(&self) -> Hir {
        let hir = |k| Hir::new(HirKind::Expr(k), Span::Artificial);
        hir(match self {
            SimpleType::Bool => ExprKind::Builtin(Builtin::Bool),
            SimpleType::Natural => ExprKind::Builtin(Builtin::Natural),
            SimpleType::Integer => ExprKind::Builtin(Builtin::Integer),
            SimpleType::Double => ExprKind::Builtin(Builtin::Double),
            SimpleType::Text => ExprKind::Builtin(Builtin::Text),
            SimpleType::Optional(t) => ExprKind::App(
                hir(ExprKind::Builtin(Builtin::Optional)),
                t.to_hir(),
            ),
            SimpleType::List(t) => {
                ExprKind::App(hir(ExprKind::Builtin(Builtin::List)), t.to_hir())
            }
            SimpleType::Record(kts) => ExprKind::RecordType(
                kts.into_iter()
                    .map(|(k, t)| (k.as_str().into(), t.to_hir()))
                    .collect(),
            ),
            SimpleType::Union(kts) => ExprKind::UnionType(
                kts.into_iter()
                    .map(|(k, t)| {
                        (k.as_str().into(), t.as_ref().map(|t| t.to_hir()))
                    })
                    .collect(),
            ),
        })
    }
}

impl Sealed for SimpleValue {}

impl Deserialize for SimpleValue {
    fn from_dhall(v: &Value) -> Result<Self> {
        v.to_simple_value().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })
    }
}

impl Sealed for SimpleType {}

impl Deserialize for SimpleType {
    fn from_dhall(v: &Value) -> Result<Self> {
        v.to_simple_type().ok_or_else(|| {
            Error::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            ))
        })
    }
}
