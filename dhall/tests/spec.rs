use std::env;
use std::ffi::OsString;
use std::fs::{create_dir_all, read_to_string, File};
use std::io::{Read, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::fmt::Display;

use walkdir::WalkDir;
use libtest_mimic::{Arguments, Outcome, Test, run_tests};
#[cfg(not(test))]
use assert_eq as assert_eq_pretty;
#[cfg(test)]
use pretty_assertions::assert_eq as assert_eq_pretty;

use dhall::error::{ErrorKind, Result};
use dhall::syntax::{binary, Expr};
use dhall::{Normalized, Parsed, Resolved, Typed};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FileType {
    /// Dhall source file
    Text,
    /// Dhall binary file
    Binary,
    /// Text file with hash
    Hash,
    /// Text file with expected text output
    UI,
}

#[derive(Clone)]
enum TestFile {
    Source(String),
    Binary(String),
    UI(String),
}

impl FileType {
    fn to_ext(self) -> &'static str {
        match self {
            FileType::Text => "dhall",
            FileType::Binary => "dhallb",
            FileType::Hash => "hash",
            FileType::UI => "txt",
        }
    }
    fn constructor(self) -> &'static str {
        match self {
            FileType::Text => "TestFile::Source",
            FileType::Binary => "TestFile::Binary",
            FileType::Hash => "TestFile::Binary",
            FileType::UI => "TestFile::UI",
        }
    }
    fn construct(self, path: &str) -> TestFile {
        match self {
            FileType::Text => TestFile::Source(format!("{}.{}", path, self.to_ext())),
            FileType::Binary => TestFile::Binary(format!("{}.{}", path, self.to_ext())),
            FileType::Hash => TestFile::Binary(format!("{}.{}", path, self.to_ext())),
            FileType::UI => TestFile::UI(format!("{}.{}", path, self.to_ext())),
        }
    }
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

#[derive(Clone)]
struct TestFeature {
    /// Name of the module, used in the output of `cargo test`
    module_name: &'static str,
    /// Directory containing the tests files, relative to the base tests directory
    directory: &'static str,
    /// Relevant variant of `dhall::tests::Test`
    variant: Rc<dyn Fn(TestFile, TestFile) -> SpecTest>,
    /// Given a file name, whether to only include it in release tests
    too_slow_path: Rc<dyn Fn(&str) -> bool>,
    /// Given a file name, whether to exclude it
    exclude_path: Rc<dyn Fn(&str) -> bool>,
    /// Type of the input file
    input_type: FileType,
    /// Type of the output file, if any
    output_type: Option<FileType>,
}

#[derive(Clone)]
enum SpecTest {
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

fn define_features() -> Vec<TestFeature> {
    let default_feature = TestFeature {
        module_name: "",
        directory: "",
        variant: Rc::new(|_, _| panic!()),
        too_slow_path: Rc::new(|_path: &str| false),
        exclude_path: Rc::new(|_path: &str| false),
        input_type: FileType::Text,
        output_type: None,
    };

    #[allow(clippy::nonminimal_bool)]
    vec![
        TestFeature {
            module_name: "parser_success",
            directory: "parser/success/",
            variant: Rc::new(SpecTest::ParserSuccess),
            too_slow_path: Rc::new(|path: &str| path == "largeExpression"),
            exclude_path: Rc::new(|path: &str| {
                false
                    // Pretty sure the test is incorrect
                    || path == "unit/import/urls/quotedPathFakeUrlEncode"
            }),
            output_type: Some(FileType::Binary),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "parser_failure",
            directory: "parser/failure/",
            variant: Rc::new(SpecTest::ParserFailure),
            output_type: Some(FileType::UI),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "printer",
            directory: "parser/success/",
            variant: Rc::new(SpecTest::Printer),
            too_slow_path: Rc::new(|path: &str| path == "largeExpression"),
            output_type: Some(FileType::UI),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "binary_encoding",
            directory: "parser/success/",
            variant: Rc::new(SpecTest::BinaryEncoding),
            too_slow_path: Rc::new(|path: &str| path == "largeExpression"),
            exclude_path: Rc::new(|path: &str| {
                false
                    // Pretty sure the test is incorrect
                    || path == "unit/import/urls/quotedPathFakeUrlEncode"
                    // See https://github.com/pyfisch/cbor/issues/109
                    || path == "double"
                    || path == "unit/DoubleLitExponentNoDot"
                    || path == "unit/DoubleLitSecretelyInt"
            }),
            output_type: Some(FileType::Binary),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "binary_decoding_success",
            directory: "binary-decode/success/",
            variant: Rc::new(SpecTest::BinaryDecodingSuccess),
            exclude_path: Rc::new(|path: &str| {
                false
                    // We don't support bignums
                    || path == "unit/IntegerBigNegative"
                    || path == "unit/IntegerBigPositive"
                    || path == "unit/NaturalBig"
            }),
            input_type: FileType::Binary,
            output_type: Some(FileType::Text),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "binary_decoding_failure",
            directory: "binary-decode/failure/",
            variant: Rc::new(SpecTest::BinaryDecodingFailure),
            input_type: FileType::Binary,
            output_type: Some(FileType::UI),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "import_success",
            directory: "import/success/",
            variant: Rc::new(SpecTest::ImportSuccess),
            exclude_path: Rc::new(|path: &str| {
                false
                    // TODO: import hash
                    || path == "hashFromCache"
                    // TODO: the standard does not respect https://tools.ietf.org/html/rfc3986#section-5.2
                    || path == "unit/asLocation/RemoteCanonicalize4"
                    // TODO: import headers
                    || path == "customHeaders"
                    || path == "headerForwarding"
                    || path == "noHeaderForwarding"
            }),
            output_type: Some(FileType::Text),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "import_failure",
            directory: "import/failure/",
            variant: Rc::new(SpecTest::ImportFailure),
            exclude_path: Rc::new(|path: &str| {
                false
                    // TODO: import headers
                    || path == "customHeadersUsingBoundVariable"
            }),
            output_type: Some(FileType::UI),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "semantic_hash",
            directory: "semantic-hash/success/",
            variant: Rc::new(SpecTest::SemanticHash),
            exclude_path: Rc::new(|path: &str| {
                false
                    // We don't support bignums
                    || path == "simple/integerToDouble"
                    // See https://github.com/pyfisch/cbor/issues/109
                    || path == "prelude/Integer/toDouble/0"
                    || path == "prelude/Integer/toDouble/1"
                    || path == "prelude/Natural/toDouble/0"
            }),
            output_type: Some(FileType::Hash),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "beta_normalize",
            directory: "normalization/success/",
            variant: Rc::new(SpecTest::Normalization),
            too_slow_path: Rc::new(|path: &str| path == "remoteSystems"),
            exclude_path: Rc::new(|path: &str| {
                false
                    // Cannot typecheck
                    || path == "unit/Sort"
                    // We don't support bignums
                    || path == "simple/integerToDouble"
                    // TODO: fix Double/show
                    || path == "prelude/JSON/number/1"
            }),
            output_type: Some(FileType::Text),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "alpha_normalize",
            directory: "alpha-normalization/success/",
            variant: Rc::new(SpecTest::AlphaNormalization),
            exclude_path: Rc::new(|path: &str| {
                // This test is designed to not typecheck
                path == "unit/FunctionNestedBindingXXFree"
            }),
            output_type: Some(FileType::Text),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "type_inference_success",
            directory: "type-inference/success/",
            variant: Rc::new(SpecTest::TypeInferenceSuccess),
            too_slow_path: Rc::new(|path: &str| path == "prelude"),
            output_type: Some(FileType::Text),
            ..default_feature.clone()
        },
        TestFeature {
            module_name: "type_inference_failure",
            directory: "type-inference/failure/",
            variant: Rc::new(SpecTest::TypeInferenceFailure),
            exclude_path: Rc::new(|path: &str| {
                false
                    // TODO: enable free variable checking
                    || path == "unit/MergeHandlerFreeVar"
            }),
            output_type: Some(FileType::UI),
            ..default_feature
        },
    ]
}

fn run_test_or_panic(test: &SpecTest) {
    let res = if env::var("CI_GRCOV").is_ok() {
        let test: SpecTest = test.clone();
        // Augment stack size when running with 0 inlining to avoid overflows
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(move || run_test(&test))
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

fn run_test(test: &SpecTest) -> Result<()> {
    use self::SpecTest::*;
    // Setup current directory to the root of the repository. Important for `as Location` tests.
    env::set_current_dir(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap(),
    )?;
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

fn dhall_files_in_dir<'a>(
    dir: &'a Path,
    take_ab_suffix: bool,
    filetype: FileType,
) -> impl Iterator<Item = (String, String)> + 'a {
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(move |path| {
            let path = path.path().strip_prefix(dir).unwrap();
            let ext = path.extension()?;
            if *ext != OsString::from(filetype.to_ext()) {
                return None;
            }
            let path = path.to_string_lossy();
            let path = &path[..path.len() - 1 - ext.len()];
            let path = if take_ab_suffix && &path[path.len() - 1..] != "A" {
                return None;
            } else if take_ab_suffix {
                path[..path.len() - 1].to_owned()
            } else {
                path.to_owned()
            };
            // Transform path into a valid Rust identifier
            let name = path.replace("/", "_").replace("-", "_");
            Some((name, path))
        })
}

fn make_test_module(
    tests: &mut Vec<Test<SpecTest>>,
    base_paths: &[&Path],
    feature: TestFeature,
) -> std::io::Result<()> {
    let take_ab_suffix = feature.output_type.is_some()
        && (feature.output_type != Some(FileType::UI)
            || feature.module_name == "printer");
    let input_suffix = if take_ab_suffix { "A" } else { "" };
    let output_suffix = if take_ab_suffix { "B" } else { "" };

    for base_path in base_paths {
        let tests_dir = base_path.join(feature.directory);
        for (name, path) in
            dhall_files_in_dir(&tests_dir, take_ab_suffix, feature.input_type)
        {
            if (feature.exclude_path)(&path) {
                continue;
            }
            if (feature.too_slow_path)(&path) {
                #[cfg(debug_assertions)]
                continue;
            }
            let path = tests_dir.join(path);
            let path = path.to_string_lossy();

            let input = feature
                .input_type
                .construct(&format!("{}{}", path, input_suffix));
            let output = match feature.output_type {
                None => None,
                Some(output_type @ FileType::UI) => {
                    // All ui outputs are in the local `tests/` directory.
                    let path = PathBuf::from("tests/").join(
                        PathBuf::from(path.as_ref())
                            .strip_prefix(base_path)
                            .unwrap(),
                    );
                    let path = path.to_str().unwrap();
                    let output = output_type
                        .construct(&format!("{}{}", path, output_suffix));
                    Some(output)
                }
                Some(output_type) => {
                    let output = output_type
                        .construct(&format!("{}{}", path, output_suffix));
                    Some(output)
                }
            };

            let test = match output {
                None => panic!(),
                Some(output) => {
                    (feature.variant)(input, output)
                }
            };
            tests.push(Test {
                name: format!("{}::{}", feature.module_name, name),
                kind: "".into(),
                is_ignored: false,
                is_bench: false,
                data: test,
            });
        }
    }
    Ok(())
}

fn generate_tests() -> Vec<Test<SpecTest>> {
    let spec_tests_dirs =
        vec![Path::new("../dhall-lang/tests/"), Path::new("tests/")];

    let features = define_features();

    let mut tests = Vec::new();
    for feature in features {
        make_test_module(&mut tests, &spec_tests_dirs, feature).unwrap();
    }
    tests
}

fn main() {
    let tests = generate_tests();

    let args = Arguments::from_args();
    run_tests(&args, tests, |test| { run_test_or_panic(&test.data); Outcome::Passed }).exit();
}
