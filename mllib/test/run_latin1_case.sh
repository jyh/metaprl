#!/bin/sh
# Check mllib/latin1_case.ml against the OCaml 4 stdlib's case functions.
#   run_latin1_case.sh            build with latin1_case.ml, diff against
#                                 latin1_case.expected (exit 0 = same)
#   run_latin1_case.sh --expected regenerate the expected file; run this
#                                 with an OCaml 4 compiler (4.12 has the
#                                 old functions)
set -e
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if [ "$1" = "--expected" ]; then
   cp "$here/latin1_case_ocaml4.ml" "$tmp/latin1_case.ml"
else
   cp "$here/../latin1_case.ml" "$here/../latin1_case.mli" "$tmp/"
fi
cp "$here/latin1_case_print.ml" "$tmp/"
cd "$tmp"
if [ -f latin1_case.mli ]; then ocamlc -c latin1_case.mli; fi
ocamlc -o print latin1_case.ml latin1_case_print.ml
if [ "$1" = "--expected" ]; then
   ./print > "$here/latin1_case.expected"
   echo "wrote latin1_case.expected ($(wc -l < "$here/latin1_case.expected") lines)"
else
   ./print > out.txt
   diff "$here/latin1_case.expected" out.txt && echo "latin1_case: OK ($(wc -l < out.txt | tr -d " ") lines match)"
fi
