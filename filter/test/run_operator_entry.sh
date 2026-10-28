#!/bin/sh
# Build and run test_operator_entry.ml against the installed camlp5.
# Usage: run_operator_entry.sh [entry-name]   (a wrong name must fail: rc 1)
set -e
here=$(cd "$(dirname "$0")" && pwd)
c5=$(camlp5 -where)
tmp=$(mktemp -d)
cp "$here/test_operator_entry.ml" "$tmp/"
cd "$tmp"
ocamlfind ocamlc -package camlp-streams,pcre2,compiler-libs.common -linkpkg \
   -I "$c5" odyl.cma camlp5.cma o_keywords.cmo pa_o.cmo \
   test_operator_entry.ml -o test_operator_entry
./test_operator_entry "$@"
