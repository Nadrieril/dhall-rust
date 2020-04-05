use std::collections::{BTreeMap, HashMap};

use dhall::semantics::{Hir, HirKind, Nir, NirKind};
use dhall::syntax::{Builtin, Expr, ExprKind, NumKind, Span};

use crate::{Error, ErrorKind, FromDhall, Result, Sealed};

#[doc(hidden)]
/// An arbitrary Dhall value.
#[derive(Debug, Clone)]
pub struct Value {
    /// Invariant: in normal form
    hir: Hir,
    /// Cached conversions because they are annoying to construct from Hir.
    /// At most one of them will be `Some`.
    as_simple_val: Option<SimpleValue>,
    as_simple_ty: Option<SimpleType>,
}

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
/// datatype using the [`StaticType`] trait, and methods that require it like
/// [`from_file_static_type`] and [`Options::static_type_annotation`]. If you need to supply a
/// `SimpleType` manually however, you can deserialize it like any other Dhall value using the
/// functions provided by this crate.
///
/// [`StaticType`]: trait.StaticType.html
/// [`from_file_static_type`]: fn.from_file_static_type.html
/// [`Options::static_type_annotation`]: options/struct.Options.html#method.static_type_annotation
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
/// assert_eq!(Foo::static_type(), ty);
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

impl Value {
    pub(crate) fn from_nir(x: &Nir) -> Self {
        Value {
            hir: x.to_hir_noenv(),
            as_simple_val: SimpleValue::from_nir(x),
            as_simple_ty: SimpleType::from_nir(x),
        }
    }

    pub(crate) fn as_hir(&self) -> &Hir {
        &self.hir
    }

    /// Converts a Value into a SimpleValue.
    pub(crate) fn to_simple_value(&self) -> Option<SimpleValue> {
        self.as_simple_val.clone()
    }

    /// Converts a Value into a SimpleType.
    pub(crate) fn to_simple_type(&self) -> Option<SimpleType> {
        self.as_simple_ty.clone()
    }

    /// Converts a value back to the corresponding AST expression.
    pub(crate) fn to_expr(&self) -> Expr {
        self.hir.to_expr(Default::default())
    }
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

impl Sealed for Value {}
impl Sealed for SimpleValue {}
impl Sealed for SimpleType {}

impl FromDhall for Value {
    fn from_dhall(v: &Value) -> Result<Self> {
        Ok(v.clone())
    }
}
impl FromDhall for SimpleValue {
    fn from_dhall(v: &Value) -> Result<Self> {
        v.to_simple_value().ok_or_else(|| {
            Error(ErrorKind::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            )))
        })
    }
}
impl FromDhall for SimpleType {
    fn from_dhall(v: &Value) -> Result<Self> {
        v.to_simple_type().ok_or_else(|| {
            Error(ErrorKind::Deserialize(format!(
                "this cannot be deserialized into a simple type: {}",
                v
            )))
        })
    }
}

impl Eq for Value {}
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.hir == other.hir
    }
}
impl std::fmt::Display for Value {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter,
    ) -> std::result::Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}
