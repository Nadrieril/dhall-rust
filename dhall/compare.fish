#!/usr/bin/env fish

set dhall_hs_path ../dhall
set dhall_hs $dhall_hs_path/.stack-work/install/**/bin/dhall
set dhall_rs target/debug/dhall
set input_file $argv[1]
diff -u \
    --label "dhall-hs < $input_file" (eval $dhall_hs < $input_file ^&1 | psub) \
    --label "dhall-rs < $input_file" (eval $dhall_rs < $input_file ^&1 | psub)
