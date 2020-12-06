use anyhow::Result;
use rand::distributions::Alphanumeric;
use rand::Rng;
use std::env;
use std::ffi::OsString;
use std::fmt::{Debug, Display};
use std::fs::{create_dir_all, read_to_string, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use libtest_mimic::{Arguments, Outcome, Test};
use walkdir::WalkDir;

use dhall::error::Error as DhallError;
use dhall::error::ErrorKind;
use dhall::syntax::{binary, Expr};
use dhall::{Normalized, Parsed, Resolved, Typed};

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
    fn construct(self, path: &str) -> TestFile {
        let file = format!("{}.{}", path, self.to_ext());
        match self {
            FileType::Text => TestFile::Source(file),
            FileType::Binary => TestFile::Binary(file),
            FileType::Hash => TestFile::UI(file),
            FileType::UI => TestFile::UI(file),
        }
    }
}

// Custom assert_eq macro that returns an Error and prints pretty diffs.
macro_rules! assert_eq {
    (@@make_str, debug, $x:expr) => {
        format!("{:#?}", $x)
    };
    (@@make_str, display, $x:expr) => {
        $x.to_string()
    };

    (@$style:ident, $left:expr, $right:expr) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                if *left_val != *right_val {
                    let left_val = assert_eq!(@@make_str, $style, left_val);
                    let right_val = assert_eq!(@@make_str, $style, right_val);
                    let msg = format!(
                        "assertion failed: `(left == right)`\n\n{}\n",
                        colored_diff::PrettyDifference {
                            expected: &left_val,
                            actual: &right_val
                        }
                    );
                    return Err(TestError(msg).into());
                }
            }
        }
    };
    ($left:expr, $right:expr) => {
        assert_eq!(@debug, $left, $right)
    };
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
        Ok(match self {
            TestFile::Source(_) => Parsed::parse_file(&self.path())?,
            TestFile::Binary(_) => Parsed::parse_binary_file(&self.path())?,
            TestFile::UI(_) => {
                Err(TestError(format!("Can't parse a UI test file")))?
            }
        })
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

    /// If UPDATE_TEST_FILES is `true`, we overwrite the output files with our own output.
    fn force_update() -> bool {
        UPDATE_TEST_FILES.load(Ordering::Acquire)
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
            TestFile::UI(_) => Err(TestError(format!(
                "Can't write an expression to a UI file"
            )))?,
        }
        Ok(())
    }
    /// Write the provided string to the pointed file.
    fn write_ui(&self, x: impl Display) -> Result<()> {
        match self {
            TestFile::UI(_) => {}
            _ => Err(TestError(format!(
                "Can't write a ui string to a dhall file"
            )))?,
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
                assert_eq!(@display, expr, expected);
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
                assert_eq!(expr, expected);
            }
        }
        Ok(())
    }
    /// Check that the provided expression matches the file contents.
    pub fn compare_binary(&self, expr: impl Into<Expr>) -> Result<()> {
        let expr = expr.into();
        match self {
            TestFile::Binary(_) => {}
            _ => Err(TestError(format!("This is not a binary file")))?,
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
                assert_eq!(
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
        let expected = expected.replace("\r\n", "\n"); // Normalize line endings
        let msg = format!("{}\n", x);
        // TODO: git changes newlines on windows
        let msg = msg.replace("\r\n", "\n");
        if msg != expected {
            if Self::force_update() {
                self.write_ui(x)?;
            } else {
                assert_eq!(@display, expected, msg);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
struct TestFeature {
    /// Name of the module, used in the output of `cargo test`
    module_name: &'static str,
    /// Directory containing the tests files, relative to the base tests directory
    directory: &'static str,
    /// Relevant variant of `dhall::tests::SpecTestKind`
    variant: SpecTestKind,
    /// Type of the input file
    input_type: FileType,
    /// Type of the output file
    output_type: FileType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpecTestKind {
    ParserSuccess,
    ParserFailure,
    Printer,
    BinaryEncoding,
    BinaryDecodingSuccess,
    BinaryDecodingFailure,
    ImportSuccess,
    ImportFailure,
    SemanticHash,
    TypeInferenceSuccess,
    TypeInferenceFailure,
    Normalization,
    AlphaNormalization,
}

#[derive(Clone)]
struct SpecTest {
    kind: SpecTestKind,
    input: TestFile,
    output: TestFile,
}

#[derive(Debug, Clone)]
struct TestError(String);

impl std::fmt::Display for TestError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.0)
    }
}
impl std::error::Error for TestError {}

fn dhall_files_in_dir<'a>(
    dir: &'a Path,
    take_ab_suffix: bool,
    filetype: FileType,
) -> impl Iterator<Item = String> + 'a {
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
            Some(path)
        })
}

// Whether to overwrite the output files when our own output differs. This is set once in `main()`.
static UPDATE_TEST_FILES: AtomicBool = AtomicBool::new(false);

static LOCAL_TEST_PATH: &str = "tests/";
static TEST_PATHS: &[&str] = &["../dhall-lang/tests/", LOCAL_TEST_PATH];

static FEATURES: &'static [TestFeature] = &[
    TestFeature {
        module_name: "parser_success",
        directory: "parser/success/",
        variant: SpecTestKind::ParserSuccess,
        input_type: FileType::Text,
        output_type: FileType::Binary,
    },
    TestFeature {
        module_name: "parser_failure",
        directory: "parser/failure/",
        variant: SpecTestKind::ParserFailure,
        input_type: FileType::Text,
        output_type: FileType::UI,
    },
    TestFeature {
        module_name: "printer",
        directory: "parser/success/",
        variant: SpecTestKind::Printer,
        input_type: FileType::Text,
        output_type: FileType::UI,
    },
    TestFeature {
        module_name: "binary_encoding",
        directory: "parser/success/",
        variant: SpecTestKind::BinaryEncoding,
        input_type: FileType::Text,
        output_type: FileType::Binary,
    },
    TestFeature {
        module_name: "binary_decoding_success",
        directory: "binary-decode/success/",
        variant: SpecTestKind::BinaryDecodingSuccess,
        input_type: FileType::Binary,
        output_type: FileType::Text,
    },
    TestFeature {
        module_name: "binary_decoding_failure",
        directory: "binary-decode/failure/",
        variant: SpecTestKind::BinaryDecodingFailure,
        input_type: FileType::Binary,
        output_type: FileType::UI,
    },
    TestFeature {
        module_name: "import_success",
        directory: "import/success/",
        variant: SpecTestKind::ImportSuccess,
        input_type: FileType::Text,
        output_type: FileType::Text,
    },
    TestFeature {
        module_name: "import_failure",
        directory: "import/failure/",
        variant: SpecTestKind::ImportFailure,
        input_type: FileType::Text,
        output_type: FileType::UI,
    },
    TestFeature {
        module_name: "semantic_hash",
        directory: "semantic-hash/success/",
        variant: SpecTestKind::SemanticHash,
        input_type: FileType::Text,
        output_type: FileType::Hash,
    },
    TestFeature {
        module_name: "beta_normalize",
        directory: "normalization/success/",
        variant: SpecTestKind::Normalization,
        input_type: FileType::Text,
        output_type: FileType::Text,
    },
    TestFeature {
        module_name: "alpha_normalize",
        directory: "alpha-normalization/success/",
        variant: SpecTestKind::AlphaNormalization,
        input_type: FileType::Text,
        output_type: FileType::Text,
    },
    TestFeature {
        module_name: "type_inference_success",
        directory: "type-inference/success/",
        variant: SpecTestKind::TypeInferenceSuccess,
        input_type: FileType::Text,
        output_type: FileType::Text,
    },
    TestFeature {
        module_name: "type_inference_failure",
        directory: "type-inference/failure/",
        variant: SpecTestKind::TypeInferenceFailure,
        input_type: FileType::Text,
        output_type: FileType::UI,
    },
];

fn discover_tests_for_feature(feature: TestFeature) -> Vec<Test<SpecTest>> {
    let take_ab_suffix =
        feature.output_type != FileType::UI || feature.module_name == "printer";
    let input_suffix = if take_ab_suffix { "A" } else { "" };
    let output_suffix = if take_ab_suffix { "B" } else { "" };

    let mut tests = Vec::new();
    for base_path in TEST_PATHS {
        let base_path = Path::new(base_path);
        let tests_dir = base_path.join(feature.directory);
        for path in
            dhall_files_in_dir(&tests_dir, take_ab_suffix, feature.input_type)
        {
            // Ignore some tests if they are known to be failing or not meant to pass.
            let rel_path = Path::new(feature.directory)
                .join(&path)
                .to_string_lossy()
                .replace("\\", "/");
            let is_ignored = ignore_test(feature.variant, &rel_path);

            // Transform path into a valid Rust identifier
            let name =
                path.replace("\\", "_").replace("/", "_").replace("-", "_");

            let path = tests_dir.join(path);
            let path = path.to_string_lossy();

            let output_path = match feature.output_type {
                FileType::UI => {
                    // All ui outputs are in the local tests directory.
                    let path = PathBuf::from(LOCAL_TEST_PATH).join(
                        PathBuf::from(path.as_ref())
                            .strip_prefix(base_path)
                            .unwrap(),
                    );
                    path.to_str().unwrap().to_owned()
                }
                _ => path.as_ref().to_owned(),
            };

            let input = feature
                .input_type
                .construct(&format!("{}{}", path, input_suffix));
            let output = feature
                .output_type
                .construct(&format!("{}{}", output_path, output_suffix));

            tests.push(Test {
                name: format!("{}::{}", feature.module_name, name),
                kind: "".into(),
                is_ignored,
                is_bench: false,
                data: SpecTest {
                    input,
                    output,
                    kind: feature.variant,
                },
            });
        }
    }
    tests
}

/// Ignore some tests if they are known to be failing or not meant to pass.
/// `path` must be relative to the test directorie(s).
#[allow(clippy::nonminimal_bool)]
fn ignore_test(variant: SpecTestKind, path: &str) -> bool {
    use SpecTestKind::*;

    // This will never succeed because of a specificity of dhall-rust.
    let is_meant_to_fail = false
        // We don't support bignums
        || path == "binary-decode/success/unit/IntegerBigNegative"
        || path == "binary-decode/success/unit/IntegerBigPositive"
        || path == "binary-decode/success/unit/NaturalBig"
        || path == "semantic-hash/success/simple/integerToDouble"
        || path == "normalization/success/simple/integerToDouble"
        // These don't typecheck but we always tck before normalizing.
        || path == "alpha-normalization/success/unit/FunctionNestedBindingXXFree"
        || path == "normalization/success/unit/Sort";

    // Fails because of Windows-specific shenanigans.
    let fails_on_windows = false
        // TODO: git changes newlines on windows
        || (variant == ImportSuccess
            && (path == "import/success/unit/AsText"
                || path == "import/success/unit/QuotedPath"))
        || variant == ParserFailure
        || variant == TypeInferenceFailure
        // Paths on windows have backslashes; this breaks many things. This is undefined in the
        // spec; see https://github.com/dhall-lang/dhall-lang/issues/1032
        || (variant == ImportSuccess && path.contains("asLocation"))
        || variant == ImportFailure;

    // Only include in release tests.
    let is_too_slow = false
        || path == "parser/success/largeExpression"
        || path == "normalization/success/remoteSystems";

    // This is a mistake in the spec, we should make a PR for it.
    let is_spec_error = false
        // The standard does not respect https://tools.ietf.org/html/rfc3986#section-5.2
        || path == "import/success/unit/asLocation/RemoteCanonicalize4"
        // The spec should specify how to print a Double
        || path == "normalization/success/prelude/JSON/number/1";

    // Failing for now, we should fix that.
    let is_failing_for_now = false
        // TODO: fix that one
        // || path == "import/success/unit/MixImportModes"
        // TODO: fails because of caching issues.
        || path == "type-inference/success/prelude"
        // TODO: do not recover from cyclic imports
        || path == "import/failure/unit/DontRecoverCycle"
        // TODO: import headers
        || path == "import/success/customHeaders"
        || path == "import/success/headerForwarding"
        || path == "import/success/noHeaderForwarding"
        || path == "import/failure/customHeadersUsingBoundVariable"
        // TODO: enable free variable checking
        || path == "type-inference/failure/unit/MergeHandlerFreeVar";

    (cfg!(debug_assertions) && is_too_slow)
        || (cfg!(windows) && fails_on_windows)
        || is_meant_to_fail
        || is_spec_error
        || is_failing_for_now
}

fn run_test_stringy_error(test: &SpecTest) -> std::result::Result<(), String> {
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
    res.map_err(|e| e.to_string())
}

fn run_test(test: &SpecTest) -> Result<()> {
    /// Like `Result::unwrap_err`, but returns an error instead of panicking.
    fn unwrap_err<T: Debug, E>(x: Result<T, E>) -> Result<E, TestError> {
        match x {
            Ok(x) => Err(TestError(format!("{:?}", x))),
            Err(e) => Ok(e),
        }
    }

    use self::SpecTestKind::*;
    let SpecTest {
        input: expr,
        output: expected,
        ..
    } = test;
    match test.kind {
        ParserSuccess => {
            let expr = expr.parse()?;
            // This exercices both parsing and binary decoding
            expected.compare_debug(expr)?;
        }
        ParserFailure => {
            use std::io;
            let err = unwrap_err(expr.parse())?;
            match err.downcast_ref::<DhallError>() {
                Some(err) => match err.kind() {
                    ErrorKind::Parse(_) => {}
                    ErrorKind::IO(e)
                        if e.kind() == io::ErrorKind::InvalidData => {}
                    e => Err(TestError(format!(
                        "Expected parse error, got: {:?}",
                        e
                    )))?,
                },
                None => {}
            }
            expected.compare_ui(err)?;
        }
        BinaryEncoding => {
            let expr = expr.parse()?;
            expected.compare_binary(expr)?;
        }
        BinaryDecodingSuccess => {
            let expr = expr.parse()?;
            expected.compare_debug(expr)?;
        }
        BinaryDecodingFailure => {
            let err = unwrap_err(expr.parse())?;
            expected.compare_ui(err)?;
        }
        Printer => {
            let parsed = expr.parse()?;
            // Round-trip pretty-printer
            let reparsed = Parsed::parse_str(&parsed.to_string())?;
            assert_eq!(reparsed, parsed);
            expected.compare_ui(parsed)?;
        }
        ImportSuccess => {
            let expr = expr.normalize()?;
            expected.compare(expr)?;
        }
        ImportFailure => {
            let err = unwrap_err(expr.resolve())?;
            expected.compare_ui(err)?;
        }
        SemanticHash => {
            let expr = expr.normalize()?.to_expr_alpha();
            let hash = hex::encode(expr.sha256_hash()?);
            expected.compare_ui(format!("sha256:{}", hash))?;
        }
        TypeInferenceSuccess => {
            let ty = expr.typecheck()?.get_type()?;
            expected.compare(ty)?;
        }
        TypeInferenceFailure => {
            let err = unwrap_err(expr.typecheck())?;
            expected.compare_ui(err)?;
        }
        Normalization => {
            let expr = expr.normalize()?;
            expected.compare(expr)?;
        }
        AlphaNormalization => {
            let expr = expr.normalize()?.to_expr_alpha();
            expected.compare(expr)?;
        }
    }
    Ok(())
}

fn main() {
    let tests = FEATURES
        .iter()
        .copied()
        .flat_map(discover_tests_for_feature)
        .collect();

    // Setup current directory to the root of the repository. Important for `as Location` tests.
    let root_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf();
    env::set_current_dir(root_dir.as_path()).unwrap();

    // Set environment variable for import tests.
    env::set_var("DHALL_TEST_VAR", "6 * 7");

    // Configure cache for import tests
    let dhall_cache_dir = root_dir
        .join("dhall-lang")
        .join("tests")
        .join("import")
        .join("cache")
        .join("dhall");
    let random_id = rand::thread_rng()
        .sample_iter(Alphanumeric)
        .take(36)
        .collect::<String>();
    let cache_dir = format!("dhall-tests-{}", random_id);
    let cache_dir = env::temp_dir().join(cache_dir);
    std::fs::create_dir_all(&cache_dir).unwrap();
    fs_extra::dir::copy(&dhall_cache_dir, &cache_dir, &Default::default())
        .unwrap();
    env::set_var("XDG_CACHE_HOME", &cache_dir);

    // Whether to overwrite the output files when our own output differs.
    // Either set `UPDATE_TEST_FILES=1` (deprecated) or pass `--bless` as an argument to this test
    // runner. Eg: `cargo test --test spec -- -q --bless`.
    let bless = env::args().any(|arg| arg == "--bless")
        || env::var("UPDATE_TEST_FILES") == Ok("1".to_string());
    UPDATE_TEST_FILES.store(bless, Ordering::Release);

    let args = Arguments::from_iter(env::args().filter(|arg| arg != "--bless"));
    let res = libtest_mimic::run_tests(&args, tests, |test| {
        let result = std::panic::catch_unwind(move || {
            run_test_stringy_error(&test.data)
        });
        match result {
            Ok(Ok(_)) => Outcome::Passed,
            Ok(Err(e)) => Outcome::Failed { msg: Some(e) },
            Err(_) => Outcome::Failed {
                msg: Some("thread panicked".to_string()),
            },
        }
    });

    std::fs::remove_dir_all(&cache_dir).unwrap();

    res.exit();
}
