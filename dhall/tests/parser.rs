#![feature(custom_inner_attributes)]
#![rustfmt::skip]
mod common;

macro_rules! parser_success {
    ($name:ident, $path:expr) => {
        make_spec_test!(ParserSuccess, $name, $path);
    };
}
macro_rules! parser_failure {
    ($name:ident, $path:expr) => {
        make_spec_test!(ParserFailure, $name, $path);
    };
}

parser_success!(spec_parser_success_annotations, "annotations");
parser_success!(spec_parser_success_asText, "asText");
parser_success!(spec_parser_success_blockComment, "blockComment");
parser_success!(spec_parser_success_builtins, "builtins");
parser_success!(spec_parser_success_collectionImportType, "collectionImportType");
parser_success!(spec_parser_success_double, "double");
parser_success!(spec_parser_success_doubleQuotedString, "doubleQuotedString");
parser_success!(spec_parser_success_environmentVariables, "environmentVariables");
parser_success!(spec_parser_success_escapedDoubleQuotedString, "escapedDoubleQuotedString");
parser_success!(spec_parser_success_escapedSingleQuotedString, "escapedSingleQuotedString");
parser_success!(spec_parser_success_fields, "fields");
parser_success!(spec_parser_success_forall, "forall");
parser_success!(spec_parser_success_functionType, "functionType");
parser_success!(spec_parser_success_identifier, "identifier");
parser_success!(spec_parser_success_ifThenElse, "ifThenElse");
parser_success!(spec_parser_success_importAlt, "importAlt");
parser_success!(spec_parser_success_interpolatedDoubleQuotedString, "interpolatedDoubleQuotedString");
parser_success!(spec_parser_success_interpolatedSingleQuotedString, "interpolatedSingleQuotedString");
parser_success!(spec_parser_success_label, "label");
parser_success!(spec_parser_success_lambda, "lambda");
// parser_success!(spec_parser_success_largeExpression, "largeExpression");
parser_success!(spec_parser_success_let, "let");
parser_success!(spec_parser_success_lineComment, "lineComment");
parser_success!(spec_parser_success_list, "list");
parser_success!(spec_parser_success_merge, "merge");
parser_success!(spec_parser_success_multilet, "multilet");
parser_success!(spec_parser_success_natural, "natural");
parser_success!(spec_parser_success_nestedBlockComment, "nestedBlockComment");
parser_success!(spec_parser_success_operators, "operators");
// parser_success!(spec_parser_success_parenthesizeUsing, "parenthesizeUsing");
parser_success!(spec_parser_success_pathTermination, "pathTermination");
parser_success!(spec_parser_success_paths, "paths");
parser_success!(spec_parser_success_quotedLabel, "quotedLabel");
parser_success!(spec_parser_success_quotedPaths, "quotedPaths");
parser_success!(spec_parser_success_record, "record");
parser_success!(spec_parser_success_reservedPrefix, "reservedPrefix");
parser_success!(spec_parser_success_singleQuotedString, "singleQuotedString");
parser_success!(spec_parser_success_sort, "sort");
parser_success!(spec_parser_success_spaceAfterListAppend, "spaceAfterListAppend");
parser_success!(spec_parser_success_template, "template");
parser_success!(spec_parser_success_unicodeComment, "unicodeComment");
parser_success!(spec_parser_success_unicodeDoubleQuotedString, "unicodeDoubleQuotedString");
parser_success!(spec_parser_success_unicodePaths, "unicodePaths");
parser_success!(spec_parser_success_union, "union");
parser_success!(spec_parser_success_urls, "urls");
parser_success!(spec_parser_success_whitespace, "whitespace");
parser_success!(spec_parser_success_whitespaceBuffet, "whitespaceBuffet");

parser_failure!(spec_parser_failure_annotation, "annotation");
parser_failure!(spec_parser_failure_builtins, "builtins");
parser_failure!(spec_parser_failure_doubleBoundsNeg, "doubleBoundsNeg");
parser_failure!(spec_parser_failure_doubleBoundsPos, "doubleBoundsPos");
parser_failure!(spec_parser_failure_importAccess, "importAccess");
parser_failure!(spec_parser_failure_incompleteIf, "incompleteIf");
parser_failure!(spec_parser_failure_mandatoryNewline, "mandatoryNewline");
parser_failure!(spec_parser_failure_missingSpace, "missingSpace");
