use std::io::Error as IOError;

use dhall_syntax::{BinOp, Import, Label, ParseError, V};

use crate::core::context::TypecheckContext;
use crate::phase::resolve::ImportStack;
use crate::phase::{Normalized, Type, Typed};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    IO(IOError),
    Parse(ParseError),
    Decode(DecodeError),
    Encode(EncodeError),
    Resolve(ImportError),
    Typecheck(TypeError),
    Deserialize(String),
}

#[derive(Debug)]
pub enum ImportError {
    Recursive(Import, Box<Error>),
    UnexpectedImport(Import),
    ImportCycle(ImportStack, Import),
}

#[derive(Debug)]
pub enum DecodeError {
    CBORError(serde_cbor::error::Error),
    WrongFormatError(String),
}

#[derive(Debug)]
pub enum EncodeError {
    CBORError(serde_cbor::error::Error),
}

/// A structured type error that includes context
#[derive(Debug)]
pub struct TypeError {
    type_message: TypeMessage,
    context: TypecheckContext,
}

/// The specific type error
#[derive(Debug)]
pub(crate) enum TypeMessage {
    UnboundVariable(V<Label>),
    InvalidInputType(Normalized),
    InvalidOutputType(Normalized),
    NotAFunction(Typed),
    TypeMismatch(Typed, Normalized, Typed),
    AnnotMismatch(Typed, Normalized),
    Untyped,
    FieldCollision(Label),
    InvalidListElement(usize, Normalized, Typed),
    InvalidListType(Normalized),
    InvalidOptionalType(Normalized),
    InvalidPredicate(Typed),
    IfBranchMismatch(Typed, Typed),
    IfBranchMustBeTerm(bool, Typed),
    InvalidFieldType(Label, Type),
    NotARecord(Label, Normalized),
    MustCombineRecord(Typed),
    MissingRecordField(Label, Typed),
    MissingUnionField(Label, Normalized),
    BinOpTypeMismatch(BinOp, Typed),
    NoDependentTypes(Normalized, Normalized),
    InvalidTextInterpolation(Typed),
    Merge1ArgMustBeRecord(Typed),
    Merge2ArgMustBeUnion(Typed),
    MergeEmptyNeedsAnnotation,
    MergeHandlerMissingVariant(Label),
    MergeVariantMissingHandler(Label),
    MergeAnnotMismatch,
    MergeHandlerTypeMismatch,
    MergeHandlerReturnTypeMustNotBeDependent,
    ProjectionMustBeRecord,
    ProjectionMissingEntry,
    Sort,
    RecordMismatch(Typed, Typed),
    RecordTypeDuplicateField,
    RecordTypeMergeRequiresRecordType(Type),
    RecordTypeMismatch(Type, Type, Type, Type),
    UnionTypeDuplicateField,
    // Unimplemented,
}

impl TypeError {
    pub(crate) fn new(
        context: &TypecheckContext,
        type_message: TypeMessage,
    ) -> Self {
        TypeError {
            context: context.clone(),
            type_message,
        }
    }
}

impl std::error::Error for TypeMessage {
    fn description(&self) -> &str {
        use TypeMessage::*;
        match *self {
            // UnboundVariable => "Unbound variable",
            InvalidInputType(_) => "Invalid function input",
            InvalidOutputType(_) => "Invalid function output",
            NotAFunction(_) => "Not a function",
            TypeMismatch(_, _, _) => "Wrong type of function argument",
            _ => "Unhandled error",
        }
    }
}

impl std::fmt::Display for TypeMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            // UnboundVariable(_) => {
            //     f.write_str(include_str!("errors/UnboundVariable.txt"))
            // }
            // TypeMismatch(e0, e1, e2) => {
            //     let template = include_str!("errors/TypeMismatch.txt");
            //     let s = template
            //         .replace("$txt0", &format!("{}", e0.as_expr()))
            //         .replace("$txt1", &format!("{}", e1.as_expr()))
            //         .replace("$txt2", &format!("{}", e2.as_expr()))
            //         .replace(
            //             "$txt3",
            //             &format!(
            //                 "{}",
            //                 e2.get_type()
            //                     .unwrap()
            //                     .as_normalized()
            //                     .unwrap()
            //                     .as_expr()
            //             ),
            //         );
            //     f.write_str(&s)
            // }
            _ => f.write_str("Unhandled error message"),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "{}", err),
            Error::Parse(err) => write!(f, "{}", err),
            Error::Decode(err) => write!(f, "{:?}", err),
            Error::Encode(err) => write!(f, "{:?}", err),
            Error::Resolve(err) => write!(f, "{:?}", err),
            Error::Typecheck(err) => write!(f, "{:?}", err),
            Error::Deserialize(err) => write!(f, "{}", err),
        }
    }
}

impl std::error::Error for Error {}
impl From<IOError> for Error {
    fn from(err: IOError) -> Error {
        Error::IO(err)
    }
}
impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::Parse(err)
    }
}
impl From<DecodeError> for Error {
    fn from(err: DecodeError) -> Error {
        Error::Decode(err)
    }
}
impl From<EncodeError> for Error {
    fn from(err: EncodeError) -> Error {
        Error::Encode(err)
    }
}
impl From<ImportError> for Error {
    fn from(err: ImportError) -> Error {
        Error::Resolve(err)
    }
}
impl From<TypeError> for Error {
    fn from(err: TypeError) -> Error {
        Error::Typecheck(err)
    }
}
