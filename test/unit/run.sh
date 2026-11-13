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
# MetaPRL's own C primitives (clib: putenv, execv, execvp for Punix).
for a in "$root/lib/clib.a" "$root/lib/clib.lib"; do
   if [ -f "$a" ]; then clibs="$clibs -cclib $a"; break; fi
done
if grep -q '^NCURSES_ENABLED *= *true' "$root/mk/config" 2>/dev/null; then
   clibs="$clibs -cclib -lncurses"
fi
# A COMPILATION_MODE = native build (the weekly Windows census, the Linux
# proofs job) has no .cma archives, only .cmxa: link those with ocamlopt
# then (no -custom; the C archives link as they are).
if [ ! -f "$root/tactics/proof/prooflib.cma" ] && [ -f "$root/tactics/proof/prooflib.cmxa" ]; then
   comp="ocamlfind ocamlopt"; a=cmxa
   clibs=$(printf '%s\n' "$clibs" | sed 's/-custom //')
   echo "(native build: linking the .cmxa archives with ocamlopt)"
else
   comp="ocamlfind ocamlc"; a=cma
fi
# A test whose first line is exactly "(* unit-link: filter *)" is also
# linked against the term library (library/library) and the filter
# (filter/prlc), which no other test needs; every other test's link is as
# it was.  Such a test also runs with MP_ROOT and MPLIB set to this tree:
# the filter's Setup reads both when it is loaded (Term_grammar links it).
# Such a test may also name, on its second line, objects that are in no
# archive, only native ones (the filter executable's modules, camlp5's
# printer):  "(* unit-native: filter/filter/filter_patt.cmx
# camlp5/pr_o.cmx *)", on one line, each path from this tree's root or, for
# camlp5/..., from camlp5's directory.  That test is linked with ocamlopt and
# the .cmxa archives, and is SKIPPED (not failed) in a build that has no
# .cmxa archives, or in which a named object is missing (the Windows
# runners' camlp5 8.05.02 has no o_keywords.cmx); the SKIP line names it.
# A test whose output is platform-specific (Setup's default editor is
# notepad.exe on Win32) keeps a second file, test_*.expected.win32, used
# when the compiler's os_type is Win32.
os_type=$(ocamlfind ocamlc -config-var os_type 2>/dev/null)
camlp5dir=$(ocamlfind query camlp5 2>/dev/null)
for src in "$here"/test_*.ml; do
   name=$(basename "$src" .ml)
   extra=""
   runenv=""
   tcomp=$comp; ta=$a; tclibs=$clibs; native=""
   if [ "$(head -n 1 "$src" | tr -d '\r')" = "(* unit-link: filter *)" ]; then
      line2=$(sed -n 2p "$src" | tr -d '\r')
      case "$line2" in
         "(* unit-native: "*" *)")
            native=${line2#"(* unit-native: "}; native=${native%" *)"}
            if [ ! -f "$root/filter/prlc.cmxa" ]; then
               echo "SKIP $name: it links native objects and this build has no .cmxa archives"; continue
            fi
            tcomp="ocamlfind ocamlopt"; ta=cmxa
            tclibs=$(printf '%s\n' "$clibs" | sed 's/-custom //') ;;
      esac
      extra="-I $root/library -I $root/filter/base -I $root/filter/filter $root/library/library.$ta $root/filter/prlc.$ta"
      missing=""
      for o in $native; do
         case "$o" in
            camlp5/*) f="$camlp5dir/${o#camlp5/}" ;;
            *) f="$root/$o" ;;
         esac
         if [ -f "$f" ]; then extra="$extra $f"; else missing="$missing $o"; fi
      done
      if [ -n "$missing" ]; then
         echo "SKIP $name: not in this build:$missing"; continue
      fi
      runenv="MP_ROOT=$root MPLIB=$root/lib"
   fi
   cp "$src" "$tmp/"
   if ! (cd "$tmp" && $tcomp -package unix,threads.posix,camlp5 -thread -linkpkg -rectypes \
           $includes "$root/libmojave/lm.$ta" "$root/mllib/util.$ta" "$root/refiner/refiner.$ta" \
           "$root/tactics/null/trefiner.$ta" "$root/tactics/proof/prooflib.$ta" $extra $tclibs \
           "$name.ml" -o "$name") > "$tmp/$name.build" 2>&1; then
      echo "FAIL $name: does not build"; cat "$tmp/$name.build"; status=1; continue
   fi
   if ! (cd "$tmp" && env $runenv "./$name") > "$tmp/$name.out" 2>&1; then
      echo "FAIL $name: exited non-zero"; cat "$tmp/$name.out"; status=1; continue
   fi
   # OCaml's stdout is in text mode on Windows: ignore the CRs it adds.
   expected="$here/$name.expected"
   if [ "$os_type" = Win32 ] && [ -f "$expected.win32" ]; then expected="$expected.win32"; fi
   if diff -u --strip-trailing-cr "$expected" "$tmp/$name.out"; then
      echo "OK   $name"
   else
      echo "FAIL $name: output differs from $(basename "$expected")"; status=1
   fi
done
exit $status
