#!/bin/sh
# Unit tests for MetaPRL's OCaml libraries, run after the build (omake).
# Each test/unit/test_*.ml is compiled in a temporary directory against the
# built libmojave (libmojave/lm.cma), mllib (mllib/util.cma), the refiner
# (refiner/refiner.cma) and the proof library (tactics/null/trefiner.cma,
# tactics/proof/prooflib.cma, which need camlp5's runtime), run, and
# its output compared with test/unit/test_*.expected, which is the output
# as generated from the code when the test was written (never typed).
# Exit 1 if any output differs or any test fails to build or run.
# Usage (from the metaprl root, after omake): sh test/unit/run.sh
set -u
root=$(pwd)
# On Windows this shell is Cygwin's and pwd prints /cygdrive/d/...,
# which the native (MinGW/MSVC) compiler cannot open: hand it D:/... instead.
if command -v cygpath > /dev/null 2>&1; then root=$(cygpath -m "$root"); fi
here="$root/test/unit"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0
# The interfaces of libmojave, mllib and the refiner (built with -rectypes).
includes=""
for d in libmojave libmojave/stdlib libmojave/util libmojave/unix libmojave/system mllib \
         refiner/refbase refiner/refsig refiner/term_gen refiner/term_std refiner/term_ds \
         refiner/rewrite refiner/refiner refiner/reflib tactics/null tactics/proof; do
   includes="$includes -I $root/$d"
done
# The proof library reaches libmojave's C primitives (Lm_terminfo), so link
# its C archive into the bytecode (-custom), and ncurses when this build uses it.
clibs=""
for a in "$root/lib/liblmcutil.a" "$root/lib/liblmcutil.lib"; do
   if [ -f "$a" ]; then clibs="-custom -cclib $a"; break; fi
done
if grep -q '^NCURSES_ENABLED *= *true' "$root/mk/config" 2>/dev/null; then
   clibs="$clibs -cclib -lncurses"
fi
for src in "$here"/test_*.ml; do
   name=$(basename "$src" .ml)
   cp "$src" "$tmp/"
   if ! (cd "$tmp" && ocamlfind ocamlc -package unix,threads.posix,camlp5 -thread -linkpkg -rectypes \
           $includes "$root/libmojave/lm.cma" "$root/mllib/util.cma" "$root/refiner/refiner.cma" \
           "$root/tactics/null/trefiner.cma" "$root/tactics/proof/prooflib.cma" $clibs \
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
