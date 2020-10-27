use std::collections::{BTreeMap, HashMap};

use dhall::builtins::Builtin;
use dhall::operations::OpKind;
use dhall::semantics::{Hir, HirKind, Nir, NirKind};
pub use dhall::syntax::NumKind;
use dhall::syntax::{Expr, ExprKind, Span};

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

/// A value of the kind that can be decoded by `serde_dhall`, e.g. `{ x = True, y = [1, 2, 3] }`.
/// This can be obtained with [`from_str()`] or [`from_file()`].
/// It can also be deserialized into Rust types with [`from_simple_value()`].
///
/// # Examples
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::BTreeMap;
/// use serde::Deserialize;
/// use serde_dhall::{from_simple_value, NumKind, SimpleValue};
///
/// #[derive(Debug, PartialEq, Eq, Deserialize)]
/// struct Foo {
///     x: bool,
///     y: Vec<u64>,
/// }
///
/// let value: SimpleValue =
///     serde_dhall::from_str("{ x = True, y = [1, 2, 3] }").parse()?;
///
/// assert_eq!(
///     value,
///     SimpleValue::Record({
///         let mut r = BTreeMap::new();
///         r.insert(
///             "x".to_string(),
///             SimpleValue::Num(NumKind::Bool(true))
///         );
///         r.insert(
///             "y".to_string(),
///             SimpleValue::List(vec![
///                 SimpleValue::Num(NumKind::Natural(1)),
///                 SimpleValue::Num(NumKind::Natural(2)),
///                 SimpleValue::Num(NumKind::Natural(3)),
///             ])
///         );
///         r
///     })
/// );
///
/// let foo: Foo = from_simple_value(value)?;
///
/// assert_eq!(
///     foo,
///     Foo {
///         x: true,
///         y: vec![1, 2, 3]
///     }
/// );
/// # Ok(())
/// # }
/// ```
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::BTreeMap;
/// use serde_dhall::{NumKind, SimpleValue};
///
/// let value: SimpleValue =
///     serde_dhall::from_str("{ x = 1, y = 2 }").parse()?;
///
/// let mut map = BTreeMap::new();
/// map.insert("x".to_string(), SimpleValue::Num(NumKind::Natural(1)));
/// map.insert("y".to_string(), SimpleValue::Num(NumKind::Natural(2)));
/// assert_eq!(value, SimpleValue::Record(map));
/// # Ok(())
/// # }
/// ```
///
/// [`from_str()`]: fn.from_str.html
/// [`from_file()`]: fn.from_file.html
/// [`from_simple_value()`]: fn.from_simple_value.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpleValue {
    /// Numbers and booleans - `True`, `1`, `+2`, `3.24`
    Num(NumKind),
    /// A string of text - `"Hello world!"`
    Text(String),
    /// An optional value - `Some e`, `None`
    Optional(Option<Box<SimpleValue>>),
    /// A list of values - `[a, b, c, d, e]`
    List(Vec<SimpleValue>),
    /// A record value - `{ k1 = v1, k2 = v2 }`
    Record(BTreeMap<String, SimpleValue>),
    /// A union value (both the name of the variant and the variant's value) - `Left e`
    Union(String, Option<Box<SimpleValue>>),
}

/// The type of a value that can be decoded by `serde_dhall`, e.g. `{ x: Bool, y: List Natural }`.
///
/// A `SimpleType` is used when deserializing values to ensure they are of the expected type.
/// Rather than letting `serde` handle potential type mismatches, this uses the type-checking
/// capabilities of Dhall to catch errors early and cleanly indicate in the user's code where the
/// mismatch happened.
///
/// You would typically not manipulate `SimpleType`s by hand but rather let Rust infer it for your
/// datatype by deriving the [`StaticType`] trait, and using
/// [`Deserializer::static_type_annotation`]. If you need to supply a `SimpleType` manually, you
/// can either deserialize it like any other Dhall value, or construct it manually.
///
/// [`StaticType`]: trait.StaticType.html
/// [`Deserializer::static_type_annotation`]: options/struct.Deserializer.html#method.static_type_annotation
///
/// # Examples
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
///     serde_dhall::from_str("{ x: Bool, y: List Natural }").parse()?;
///
/// assert_eq!(Foo::static_type(), ty);
/// # Ok(())
/// # }
/// ```
///
/// ```rust
/// # fn main() -> serde_dhall::Result<()> {
/// use std::collections::HashMap;
/// use serde_dhall::SimpleType;
///
/// let ty: SimpleType =
///     serde_dhall::from_str("{ x: Natural, y: Natural }").parse()?;
///
/// let mut map = HashMap::new();
/// map.insert("x".to_string(), SimpleType::Natural);
/// map.insert("y".to_string(), SimpleType::Natural);
/// assert_eq!(ty, SimpleType::Record(map));
/// # Ok(())
/// # }
/// ```
///
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
            NirKind::EmptyListLit(t) => {
                // Detect and handle the special records that make assoc maps
                if let NirKind::RecordType(kts) = t.kind() {
                    if kts.len() == 2
                        && kts.contains_key("mapKey")
                        && kts.contains_key("mapValue")
                    {
                        return Some(SimpleValue::Record(Default::default()));
                    }
                }
                SimpleValue::List(vec![])
            }
            NirKind::NEListLit(xs) => {
                // Detect and handle the special records that make assoc maps
                if let NirKind::RecordLit(kvs) = xs[0].kind() {
                    if kvs.len() == 2
                        && kvs.contains_key("mapKey")
                        && kvs.contains_key("mapValue")
                    {
                        let convert_entry = |x: &Nir| match x.kind() {
                            NirKind::RecordLit(kvs) => {
                                let k = match kvs.get("mapKey").unwrap().kind()
                                {
                                    NirKind::TextLit(t)
                                        if t.as_text().is_some() =>
                                    {
                                        t.as_text().unwrap()
                                    }
                                    // TODO
                                    _ => panic!(
                                        "Expected `mapKey` to be a text \
                                         literal"
                                    ),
                                };
                                let v = Self::from_nir(
                                    kvs.get("mapValue").unwrap(),
                                )?;
                                Some((k, v))
                            }
                            _ => unreachable!("Internal type error"),
                        };
                        return Some(SimpleValue::Record(
                            xs.iter()
                                .map(convert_entry)
                                .collect::<Option<_>>()?,
                        ));
                    }
                }
                SimpleValue::List(
                    xs.iter().map(Self::from_nir).collect::<Option<_>>()?,
                )
            }
            NirKind::RecordLit(kvs) => SimpleValue::Record(
                kvs.iter()
                    .map(|(k, v)| Some((k.to_string(), Self::from_nir(v)?)))
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
            SimpleType::Optional(t) => ExprKind::Op(OpKind::App(
                hir(ExprKind::Builtin(Builtin::Optional)),
                t.to_hir(),
            )),
            SimpleType::List(t) => ExprKind::Op(OpKind::App(
                hir(ExprKind::Builtin(Builtin::List)),
                t.to_hir(),
            )),
            SimpleType::Record(kts) => ExprKind::RecordType(
                kts.iter()
                    .map(|(k, t)| (k.as_str().into(), t.to_hir()))
                    .collect(),
            ),
            SimpleType::Union(kts) => ExprKind::UnionType(
                kts.iter()
                    .map(|(k, t)| {
                        (k.as_str().into(), t.as_ref().map(|t| t.to_hir()))
                    })
                    .collect(),
            ),
        })
    }

    /// Converts back to the corresponding AST expression.
    pub(crate) fn to_expr(&self) -> Expr {
        self.to_hir().to_expr(Default::default())
    }
}

impl Sealed for Value {}
impl Sealed for SimpleType {}

impl FromDhall for Value {
    fn from_dhall(v: &Value) -> Result<Self> {
        Ok(v.clone())
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

impl std::fmt::Display for SimpleType {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter,
    ) -> std::result::Result<(), std::fmt::Error> {
        self.to_expr().fmt(f)
    }
}

#[test]
fn test_display_simpletype() {
    use SimpleType::*;
    let ty = List(Box::new(Optional(Box::new(Natural))));
    assert_eq!(ty.to_string(), "List (Optional Natural)".to_string())
}
