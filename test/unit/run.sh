#!/bin/sh
# Unit tests for MetaPRL's OCaml libraries, run after the build (omake).
# Each test/unit/test_*.ml is compiled in a temporary directory against the
# built libmojave (libmojave/lm.cma) and mllib (mllib/util.cma), run, and
# its output compared with test/unit/test_*.expected, which is the output
# as generated from the code when the test was written (never typed).
# Exit 1 if any output differs or any test fails to build or run.
# Usage (from the metaprl root, after omake): sh test/unit/run.sh
set -u
root=$(pwd)
here="$root/test/unit"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0
for src in "$here"/test_*.ml; do
   name=$(basename "$src" .ml)
   cp "$src" "$tmp/"
   if ! (cd "$tmp" && ocamlfind ocamlc -package unix,threads.posix -linkpkg \
           -I "$root/libmojave" -I "$root/mllib" "$root/libmojave/lm.cma" "$root/mllib/util.cma" \
           "$name.ml" -o "$name") > "$tmp/$name.build" 2>&1; then
      echo "FAIL $name: does not build"; cat "$tmp/$name.build"; status=1; continue
   fi
   if ! (cd "$tmp" && "./$name") > "$tmp/$name.out" 2>&1; then
      echo "FAIL $name: exited non-zero"; cat "$tmp/$name.out"; status=1; continue
   fi
   # OCaml's stdout is in text mode on Windows: ignore the CRs it adds.
   if diff -u --strip-trailing-cr "$here/$name.expected" "$tmp/$name.out"; then
      echo "OK   $name"
   else
      echo "FAIL $name: output differs from $name.expected"; status=1
   fi
done
exit $status
