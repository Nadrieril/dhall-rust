#!/usr/bin/env bash
# This script generates the missing "...B.dhall" files in tests.
# It needs to have a valid `dhall` executable in the PATH.
# It also uses the `fd` command (https://github.com/sharkdp/fd), until
# someone comes up with the correct equivalent `find` invocation.
#
# Usage:
# $ ./update-tests.sh

usage_text=$(cat <<-END
Usage: update-tests.sh [missing | add]
END
)

cd "$(dirname "$0")" || exit 1

if [ ! -x "$(which dhall)" ] ; then
    echo "Error: 'dhall' executable not found in PATH"
fi
if [ ! -x "$(which fd)" ] ; then
    echo "Error: 'fd' executable not found in PATH"
fi
if [ ! -x "$(which cbor2diag.rb)" ] ; then
    echo "Error: 'cbor2diag.rb' executable not found in PATH"
fi

function parser_input_file() { echo "$1A.dhall"; }
function parser_output_file() { echo "$1B.dhallb"; }
function parser_process() {
    dhall encode --file "$1"
}

function binary-decode_input_file() { echo "$1A.dhallb"; }
function binary-decode_output_file() { echo "$1B.dhall"; }
function binary-decode_process() {
    dhall decode --file "$1"
}

function semantic-hash_input_file() { echo "$1A.dhall"; }
function semantic-hash_output_file() { echo "$1B.hash"; }
function semantic-hash_process() {
    dhall hash --file "$1"
}

function import_input_file() { echo "$1A.dhall"; }
function import_output_file() { echo "$1B.dhall"; }
function import_process() {
    dhall resolve --file "$1"
}

function type-inference_input_file() { echo "$1A.dhall"; }
function type-inference_output_file() { echo "$1B.dhall"; }
function type-inference_process() {
    dhall resolve --file "$1" | dhall type
}

function normalization_input_file() { echo "$1A.dhall"; }
function normalization_output_file() { echo "$1B.dhall"; }
function normalization_process() {
    dhall resolve --file "$1" | dhall normalize
}

function alpha-normalization_input_file() { echo "$1A.dhall"; }
function alpha-normalization_output_file() { echo "$1B.dhall"; }
function alpha-normalization_process() {
    dhall normalize --alpha --file "$1"
}

tmpfile=$(mktemp -t update-tests.XXXXXX)
trap "{ rm -f $tmpfile; }" EXIT

function generate_output_file() {
    folder="$1"
    file="$2"
    INPUT_FILE="$(${folder}_input_file "$file")"
    OUTPUT_FILE="$(${folder}_output_file "$file")"
    if [ ! -f "$OUTPUT_FILE" ]; then
        echo "$OUTPUT_FILE"
        ${folder}_process "$INPUT_FILE" > "$tmpfile"
        if [ $? -eq 0 ]; then
            mv "$tmpfile" "$OUTPUT_FILE"
            if [ "$folder" = "parser" ]; then
                cat "$OUTPUT_FILE" | cbor2diag.rb > "${file}B.diag"
            fi
        fi
    fi
}

if [ "$1" = "missing" ]; then
    echo "Generating missing output files..."
    for folder in parser binary-decode semantic-hash import type-inference normalization alpha-normalization; do
        fd 'A\.dhallb?$' ./dhall-lang/tests/$folder/success  ./dhall/tests/$folder/success \
            | sed 's/A.dhallb\?$//' \
            | while read file; do
                generate_output_file "$folder" "$file"
            done
    done

elif [ "$1" = "add" ]; then
    # Takes in stdin lists of a path and file contents, like:
    #   normalization/unit/TextShowEmpty Text/show ""
    # This will add a test to the local tests folder for each such line, and generate
    # the output using the `dhall` command in the PATH.
    while read file contents; do
        folder="$(echo "$file" | cut -d/ -f1)"
        is_success="$(echo "$file" | cut -d/ -f2)"
        file="./dhall/tests/$file"
        mkdir -p "$(dirname "$file")"

        if [ "$is_success" = "success" ]; then
            INPUT_FILE="${file}A.dhall"
            echo "$contents" > $INPUT_FILE
            generate_output_file "$folder" "$file"
        else
            INPUT_FILE="${file}.dhall"
            echo "$contents" > $INPUT_FILE
        fi
    done

else
    echo "$usage_text"
fi
