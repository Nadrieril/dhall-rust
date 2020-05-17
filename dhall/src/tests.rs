#[cfg(not(test))]
use assert_eq as assert_eq_pretty;
#[cfg(test)]
use pretty_assertions::assert_eq as assert_eq_pretty;

use std::env;
use std::fmt::Display;
use std::fs::{create_dir_all, read_to_string, File};
use std::io::{Read, Write};
use std::path::PathBuf;

use crate::error::{ErrorKind, Result};
use crate::syntax::{binary, Expr};
use crate::{Normalized, Parsed, Resolved, Typed};

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

#[allow(dead_code)]
enum Test {
    ParserSuccess(TestFile, TestFile),
    ParserFailure(TestFile, TestFile),
    Printer(TestFile, TestFile),
    BinaryEncoding(TestFile, TestFile),
    BinaryDecodingSuccess(TestFile, TestFile),
    BinaryDecodingFailure(TestFile, TestFile),
    ImportSuccess(TestFile, TestFile),
    ImportFailure(TestFile, TestFile),
    SemanticHash(TestFile, TestFile),
    TypeInferenceSuccess(TestFile, TestFile),
    TypeInferenceFailure(TestFile, TestFile),
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
            | TestFile::UI(path) => PathBuf::from("dhall").join(path),
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
    /// Parse, resolve and tck the target file
    pub fn typecheck(&self) -> Result<Typed> {
        Ok(self.resolve()?.typecheck()?)
    }
    /// Parse, resolve, tck and normalize the target file
    pub fn normalize(&self) -> Result<Normalized> {
        Ok(self.typecheck()?.normalize())
    }

    /// If UPDATE_TEST_FILES=1, we overwrite the output files with our own output.
    fn force_update() -> bool {
        env::var("UPDATE_TEST_FILES") == Ok("1".to_string())
    }
    /// Write the provided expression to the pointed file.
    fn write_expr(&self, expr: impl Into<Expr>) -> Result<()> {
        let expr = expr.into();
        let path = self.path();
        create_dir_all(path.parent().unwrap())?;
        let mut file = File::create(path)?;
        match self {
            TestFile::Source(_) => {
                writeln!(file, "{}", expr)?;
            }
            TestFile::Binary(_) => {
                let expr_data = binary::encode(&expr)?;
                file.write_all(&expr_data)?;
            }
            TestFile::UI(_) => panic!("Can't write an expression to a UI file"),
        }
        Ok(())
    }
    /// Write the provided string to the pointed file.
    fn write_ui(&self, x: impl Display) -> Result<()> {
        match self {
            TestFile::UI(_) => {}
            _ => panic!("Can't write a ui string to a dhall file"),
        }
        let path = self.path();
        create_dir_all(path.parent().unwrap())?;
        let mut file = File::create(path)?;
        writeln!(file, "{}", x)?;
        Ok(())
    }

    /// Check that the provided expression matches the file contents.
    pub fn compare(&self, expr: impl Into<Expr>) -> Result<()> {
        let expr = expr.into();
        if !self.path().is_file() {
            return self.write_expr(expr);
        }

        let expected = self.parse()?.to_expr();
        if expr != expected {
            if Self::force_update() {
                self.write_expr(expr)?;
            } else {
                assert_eq_display!(expr, expected);
            }
        }
        Ok(())
    }
    /// Check that the provided expression matches the file contents.
    pub fn compare_debug(&self, expr: impl Into<Expr>) -> Result<()> {
        let expr = expr.into();
        if !self.path().is_file() {
            return self.write_expr(expr);
        }

        let expected = self.parse()?.to_expr();
        if expr != expected {
            if Self::force_update() {
                self.write_expr(expr)?;
            } else {
                assert_eq_pretty!(expr, expected);
            }
        }
        Ok(())
    }
    /// Check that the provided expression matches the file contents.
    pub fn compare_binary(&self, expr: impl Into<Expr>) -> Result<()> {
        let expr = expr.into();
        match self {
            TestFile::Binary(_) => {}
            _ => panic!("This is not a binary file"),
        }
        if !self.path().is_file() {
            return self.write_expr(expr);
        }

        let expr_data = binary::encode(&expr)?;
        let expected_data = {
            let mut data = Vec::new();
            File::open(&self.path())?.read_to_end(&mut data)?;
            data
        };

        // Compare bit-by-bit
        if expr_data != expected_data {
            if Self::force_update() {
                self.write_expr(expr)?;
            } else {
                use serde_cbor::de::from_slice;
                use serde_cbor::value::Value;
                // Pretty-print difference
                assert_eq_pretty!(
                    from_slice::<Value>(&expr_data).unwrap(),
                    from_slice::<Value>(&expected_data).unwrap()
                );
                // If difference was not visible in the cbor::Nir, compare normally.
                assert_eq!(expr_data, expected_data);
            }
        }
        Ok(())
    }
    /// Check that the provided string matches the file contents. Writes to the corresponding file
    /// if it is missing.
    pub fn compare_ui(&self, x: impl Display) -> Result<()> {
        if !self.path().is_file() {
            return self.write_ui(x);
        }

        let expected = read_to_string(self.path())?;
        let msg = format!("{}\n", x);
        if msg != expected {
            if Self::force_update() {
                self.write_ui(x)?;
            } else {
                assert_eq_pretty_str!(expected, msg);
            }
        }
        Ok(())
    }
}

#[allow(dead_code)]
fn run_test_or_panic(test: Test) {
    let res = if env::var("CI_GRCOV").is_ok() {
        // Augment stack size when running with 0 inlining to avoid overflows
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(|| run_test(test))
            .unwrap()
            .join()
            .unwrap()
    } else {
        run_test(test)
    };
    match res {
        Ok(_) => {}
        Err(e) => panic!(e.to_string()),
    }
}

fn run_test(test: Test) -> Result<()> {
    use self::Test::*;
    // Setup current directory to the root of the repository. Important for `as Location` tests.
    let root_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf();
    env::set_current_dir(root_dir.as_path())?;
    // Set environment variable for import tests.
    env::set_var("DHALL_TEST_VAR", "6 * 7");

    match test {
        ParserSuccess(expr, expected) => {
            let expr = expr.parse()?;
            // This exercices both parsing and binary decoding
            expected.compare_debug(expr)?;
        }
        ParserFailure(expr, expected) => {
            use std::io;
            let err = expr.parse().unwrap_err();
            match err.kind() {
                ErrorKind::Parse(_) => {}
                ErrorKind::IO(e) if e.kind() == io::ErrorKind::InvalidData => {}
                e => panic!("Expected parse error, got: {:?}", e),
            }
            expected.compare_ui(err)?;
        }
        BinaryEncoding(expr, expected) => {
            let expr = expr.parse()?;
            expected.compare_binary(expr)?;
        }
        BinaryDecodingSuccess(expr, expected) => {
            let expr = expr.parse()?;
            expected.compare_debug(expr)?;
        }
        BinaryDecodingFailure(expr, expected) => {
            let err = expr.parse().unwrap_err();
            expected.compare_ui(err)?;
        }
        Printer(expr, expected) => {
            let parsed = expr.parse()?;
            // Round-trip pretty-printer
            let reparsed = Parsed::parse_str(&parsed.to_string())?;
            assert_eq!(reparsed, parsed);
            expected.compare_ui(parsed)?;
        }
        ImportSuccess(expr, expected) => {
            // Configure cache for import tests
            env::set_var(
                "XDG_CACHE_HOME",
                root_dir
                    .join("dhall-lang")
                    .join("tests")
                    .join("import")
                    .join("cache")
                    .as_path(),
            );
            let expr = expr.normalize()?;
            expected.compare(expr)?;
        }
        ImportFailure(expr, expected) => {
            let err = expr.resolve().unwrap_err();
            expected.compare_ui(err)?;
        }
        SemanticHash(expr, expected) => {
            let expr = expr.normalize()?.to_expr_alpha();
            let hash = hex::encode(expr.hash()?);
            expected.compare_ui(format!("sha256:{}", hash))?;
        }
        TypeInferenceSuccess(expr, expected) => {
            let ty = expr.typecheck()?.get_type()?;
            expected.compare(ty)?;
        }
        TypeInferenceFailure(expr, expected) => {
            let err = expr.typecheck().unwrap_err();
            expected.compare_ui(err)?;
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
                run_test_or_panic($type);
            }
        };
    }

    // See build.rs
    include!(concat!(env!("OUT_DIR"), "/spec_tests.rs"));
}
