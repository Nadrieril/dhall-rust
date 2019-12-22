use std::io::Error as IOError;

use crate::semantics::core::context::TypecheckContext;
use crate::semantics::core::value::Value;
use crate::semantics::phase::resolve::ImportStack;
use crate::semantics::phase::NormalizedExpr;
use crate::syntax::{BinOp, Import, Label, ParseError, Span};

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
}

#[derive(Debug)]
pub enum ImportError {
    Recursive(Import<NormalizedExpr>, Box<Error>),
    UnexpectedImport(Import<NormalizedExpr>),
    ImportCycle(ImportStack, Import<NormalizedExpr>),
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
    message: TypeMessage,
    context: TypecheckContext,
}

/// The specific type error
#[derive(Debug)]
pub(crate) enum TypeMessage {
    UnboundVariable(Span),
    InvalidInputType(Value),
    InvalidOutputType(Value),
    NotAFunction(Value),
    TypeMismatch(Value, Value, Value),
    AnnotMismatch(Value, Value),
    InvalidListElement(usize, Value, Value),
    InvalidListType(Value),
    InvalidOptionalType(Value),
    InvalidPredicate(Value),
    IfBranchMismatch(Value, Value),
    IfBranchMustBeTerm(bool, Value),
    InvalidFieldType(Label, Value),
    NotARecord(Label, Value),
    MustCombineRecord(Value),
    MissingRecordField(Label, Value),
    MissingUnionField(Label, Value),
    BinOpTypeMismatch(BinOp, Value),
    InvalidTextInterpolation(Value),
    Merge1ArgMustBeRecord(Value),
    Merge2ArgMustBeUnion(Value),
    MergeEmptyNeedsAnnotation,
    MergeHandlerMissingVariant(Label),
    MergeVariantMissingHandler(Label),
    MergeAnnotMismatch,
    MergeHandlerTypeMismatch,
    MergeHandlerReturnTypeMustNotBeDependent,
    ProjectionMustBeRecord,
    ProjectionMissingEntry,
    ProjectionDuplicateField,
    Sort,
    RecordTypeDuplicateField,
    RecordTypeMergeRequiresRecordType(Value),
    UnionTypeDuplicateField,
    EquivalenceArgumentMustBeTerm(bool, Value),
    EquivalenceTypeMismatch(Value, Value),
    AssertMismatch(Value, Value),
    AssertMustTakeEquivalence,
}

impl TypeError {
    pub(crate) fn new(
        context: &TypecheckContext,
        message: TypeMessage,
    ) -> Self {
        TypeError {
            context: context.clone(),
            message,
        }
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use TypeMessage::*;
        let msg = match &self.message {
            UnboundVariable(span) => span.error("Type error: Unbound variable"),
            InvalidInputType(v) => {
                v.span().error("Type error: Invalid function input")
            }
            InvalidOutputType(v) => {
                v.span().error("Type error: Invalid function output")
            }
            NotAFunction(v) => v.span().error("Type error: Not a function"),
            TypeMismatch(x, y, z) => {
                x.span()
                    .error("Type error: Wrong type of function argument")
                    + "\n"
                    + &z.span().error(format!(
                        "This argument has type {:?}",
                        z.get_type().unwrap()
                    ))
                    + "\n"
                    + &y.span().error(format!(
                        "But the function expected an argument of type {:?}",
                        y
                    ))
            }
            _ => "Type error: Unhandled error".to_string(),
        };
        write!(f, "{}", msg)
    }
}

impl std::error::Error for TypeError {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "{}", err),
            Error::Parse(err) => write!(f, "{}", err),
            Error::Decode(err) => write!(f, "{:?}", err),
            Error::Encode(err) => write!(f, "{:?}", err),
            Error::Resolve(err) => write!(f, "{:?}", err),
            Error::Typecheck(err) => write!(f, "{}", err),
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
