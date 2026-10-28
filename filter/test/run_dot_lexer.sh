#!/bin/sh
# Build test_dot_lexer.ml against the camlp5 on PATH and run it on the corpus.
# Usage: run_dot_lexer.sh 7|8 > out.txt
#   7: the reference (camlp5 7, its own lexer); writes test_dot_lexer.expected
#   8: filter/filter/filter_dot_lexer.ml over camlp5 8's lexer
# Then: diff filter/test/test_dot_lexer.expected out.txt
set -e
here=$(cd "$(dirname "$0")" && pwd)
c5=$(camlp5 -where)
tmp=$(mktemp -d)
cp "$here/test_dot_lexer.ml" "$tmp/"
cd "$tmp"
case "$1" in
   7) cp "$here/dot_lexer_compat_7.ml" dot_lexer_compat.ml
      ocamlfind ocamlc -I "$c5" gramlib.cma dot_lexer_compat.ml test_dot_lexer.ml -o t ;;
   8) cp "$here/dot_lexer_compat_8.ml" dot_lexer_compat.ml
      cp "$here/../filter/filter_dot_lexer.ml" .
      ocamlfind ocamlc -package camlp5,camlp-streams -linkpkg -I "$c5" gramlib.cma \
         filter_dot_lexer.ml dot_lexer_compat.ml test_dot_lexer.ml -o t ;;
   *) echo "usage: $0 7|8" >&2; exit 2 ;;
esac
./t "$here/dot_lexer_corpus.txt"
