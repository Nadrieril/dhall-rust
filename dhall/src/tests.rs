#[cfg(not(test))]
use assert_eq as assert_eq_pretty;
#[cfg(test)]
use pretty_assertions::assert_eq as assert_eq_pretty;

macro_rules! assert_eq_display {
    ($left:expr, $right:expr) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    panic!(
                        r#"assertion failed: `(left == right)`
 left: `{}`,
right: `{}`"#,
                        left_val, right_val
                    )
                }
            }
        }
    }};
}

/// Wrapper around string slice that makes debug output `{:?}` to print string same way as `{}`.
/// Used in different `assert*!` macros in combination with `pretty_assertions` crate to make
/// test failures to show nice diffs.
#[derive(PartialEq, Eq)]
#[doc(hidden)]
pub struct PrettyString(String);

/// Make diff to display string as multi-line string
impl std::fmt::Debug for PrettyString {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

macro_rules! assert_eq_pretty_str {
    ($left:expr, $right:expr) => {
        assert_eq_pretty!(
            PrettyString($left.to_string()),
            PrettyString($right.to_string())
        );
    };
}

use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

use crate::error::{Error, Result};
use crate::syntax::binary;
use crate::{Normalized, NormalizedExpr, Parsed, Resolved};

#[allow(dead_code)]
enum Test {
    ParserSuccess(TestFile, TestFile),
    ParserFailure(TestFile),
    Printer(TestFile, TestFile),
    BinaryEncoding(TestFile, TestFile),
    BinaryDecodingSuccess(TestFile, TestFile),
    BinaryDecodingFailure(TestFile),
    ImportSuccess(TestFile, TestFile),
    ImportFailure(TestFile),
    ImportError(TestFile, TestFile),
    TypeInferenceSuccess(TestFile, TestFile),
    TypeInferenceFailure(TestFile),
    TypeError(TestFile, TestFile),
    Normalization(TestFile, TestFile),
    AlphaNormalization(TestFile, TestFile),
}

#[allow(dead_code)]
enum TestFile {
    Source(&'static str),
    Binary(&'static str),
    UI(&'static str),
}

impl TestFile {
    pub fn path(&self) -> PathBuf {
        match self {
            TestFile::Source(path)
            | TestFile::Binary(path)
            | TestFile::UI(path) => PathBuf::from(path),
        }
    }

    /// Parse the target file
    pub fn parse(&self) -> Result<Parsed> {
        match self {
            TestFile::Source(_) => Parsed::parse_file(&self.path()),
            TestFile::Binary(_) => Parsed::parse_binary_file(&self.path()),
            TestFile::UI(_) => panic!("Can't parse a UI test file"),
        }
    }
    /// Parse and resolve the target file
    pub fn resolve(&self) -> Result<Resolved> {
        Ok(self.parse()?.resolve()?)
    }
    /// Parse, resolve, tck and normalize the target file
    pub fn normalize(&self) -> Result<Normalized> {
        Ok(self.resolve()?.typecheck()?.normalize())
    }

    /// Check that the provided expression matches the file contents.
    pub fn compare(&self, expr: impl Into<NormalizedExpr>) -> Result<()> {
        let expr = expr.into();
        let expected = self.parse()?.to_expr();
        assert_eq_display!(expr, expected);
        Ok(())
    }
    /// Check that the provided expression matches the file contents.
    pub fn compare_debug(&self, expr: impl Into<NormalizedExpr>) -> Result<()> {
        let expr = expr.into();
        let expected = self.parse()?.to_expr();
        assert_eq_pretty!(expr, expected);
        Ok(())
    }
    /// Check that the provided expression matches the file contents.
    pub fn compare_binary(
        &self,
        expr: impl Into<NormalizedExpr>,
    ) -> Result<()> {
        match self {
            TestFile::Binary(_) => {}
            _ => panic!("This is not a binary file"),
        }
        let expr_data = binary::encode(&expr.into())?;
        let expected_data = {
            let mut data = Vec::new();
            File::open(&self.path())?.read_to_end(&mut data)?;
            data
        };

        // Compare bit-by-bit
        if expr_data != expected_data {
            use serde_cbor::de::from_slice;
            use serde_cbor::value::Value;
            // use std::io::Write;
            // File::create(&expected)?.write_all(&expr_data)?;
            // Pretty-print difference
            assert_eq_pretty!(
                from_slice::<Value>(&expr_data).unwrap(),
                from_slice::<Value>(&expected_data).unwrap()
            );
            // If difference was not visible in the cbor::Value, compare normally.
            assert_eq!(expr_data, expected_data);
        }
        Ok(())
    }
}

#[allow(dead_code)]
fn run_test_stringy_error(test: Test) -> std::result::Result<(), String> {
    run_test(test).map_err(|e| e.to_string())?;
    Ok(())
}

fn run_test(test: Test) -> Result<()> {
    use self::Test::*;
    match test {
        ParserSuccess(expr, expected) => {
            let expr = expr.parse()?;
            // This exercices both parsing and binary decoding
            expected.compare_debug(expr)?;
        }
        ParserFailure(expr) => {
            let err = expr.parse().unwrap_err();
            match &err {
                Error::Parse(_) => {}
                Error::IO(e) if e.kind() == std::io::ErrorKind::InvalidData => {
                }
                e => panic!("Expected parse error, got: {:?}", e),
            }
        }
        BinaryEncoding(expr, expected) => {
            let expr = expr.parse()?;
            expected.compare_binary(expr)?;
        }
        BinaryDecodingSuccess(expr, expected) => {
            let expr = expr.parse()?;
            expected.compare_debug(expr)?;
        }
        BinaryDecodingFailure(expr) => {
            expr.parse().unwrap_err();
        }
        Printer(expr, _) => {
            let expected = expr.parse()?;
            // Round-trip pretty-printer
            let expr: Parsed = Parsed::parse_str(&expected.to_string())?;
            assert_eq!(expr, expected);
        }
        ImportSuccess(expr, expected) => {
            let expr = expr.normalize()?;
            expected.compare(expr)?;
        }
        ImportFailure(expr) => {
            expr.parse()?.resolve().unwrap_err();
        }
        // Checks the output of the type error against a text file. If the text file doesn't exist,
        // we instead write to it the output we got. This makes it easy to update those files: just
        // `rm -r dhall/tests/type-errors` and run the tests again.
        ImportError(expr, expected) => {
            let err: Error = expr.parse()?.resolve().unwrap_err().into();

            let error_file_path = expected.path();
            if error_file_path.is_file() {
                let expected_msg = std::fs::read_to_string(error_file_path)?;
                let msg = format!("{}\n", err);
                assert_eq_pretty_str!(msg, expected_msg);
            } else {
                std::fs::create_dir_all(error_file_path.parent().unwrap())?;
                let mut file = File::create(error_file_path)?;
                writeln!(file, "{}", err)?;
            }
        }
        TypeInferenceSuccess(expr, expected) => {
            let ty = expr.resolve()?.typecheck()?.get_type()?;
            expected.compare(ty)?;
        }
        TypeInferenceFailure(expr) => {
            expr.resolve()?.typecheck().unwrap_err();
        }
        // Checks the output of the type error against a text file. If the text file doesn't exist,
        // we instead write to it the output we got. This makes it easy to update those files: just
        // `rm -r dhall/tests/type-errors` and run the tests again.
        TypeError(expr, expected) => {
            let err: Error = expr.resolve()?.typecheck().unwrap_err().into();

            let error_file_path = expected.path();
            if error_file_path.is_file() {
                let expected_msg = std::fs::read_to_string(error_file_path)?;
                let msg = format!("{}\n", err);
                assert_eq_pretty_str!(msg, expected_msg);
            } else {
                std::fs::create_dir_all(error_file_path.parent().unwrap())?;
                let mut file = File::create(error_file_path)?;
                writeln!(file, "{}", err)?;
            }
        }
        Normalization(expr, expected) => {
            let expr = expr.normalize()?;
            expected.compare(expr)?;
        }
        AlphaNormalization(expr, expected) => {
            let expr = expr.normalize()?.to_expr_alpha();
            expected.compare(expr)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod spec {
    macro_rules! make_spec_test {
        ($type:expr, $name:ident) => {
            #[test]
            #[allow(non_snake_case)]
            fn $name() {
                use crate::tests::Test::*;
                use crate::tests::*;
                match run_test_stringy_error($type) {
                    Ok(_) => {}
                    Err(s) => panic!(s),
                }
            }
        };
    }

    // See build.rs
    include!(concat!(env!("OUT_DIR"), "/spec_tests.rs"));
}
