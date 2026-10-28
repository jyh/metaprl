#!/bin/sh
# Build and run the Filter_ocaml pin against a built metaprl tree.
#   run_pin_filter_ocaml.sh <metaprl-tree> <output-file> <ocaml files...>
# The tree must already be built (libmojave/lm.cma, mllib/util.cma,
# refiner/refiner.cma, filter/prlc.cma and the C archives).  Run it with
# the compilers that built the tree on PATH.
set -e
root=$(cd "$1" && pwd); out=$2; shift 2
case "$out" in /*) ;; *) out="$PWD/$out" ;; esac
# The run happens in a temporary directory, so make the inputs absolute.
files=""
for f in "$@"; do
   case "$f" in /*) files="$files $f" ;; *) files="$files $PWD/$f" ;; esac
done
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
c5=$(camlp5 -where)
inc=""
for d in libmojave/stdlib libmojave/util libmojave/unix mllib \
         refiner/refsig refiner/refbase refiner/refiner refiner/reflib \
         refiner/term_ds refiner/term_std refiner/term_gen refiner/rewrite \
         filter/base filter/filter; do
   [ -d "$root/$d" ] && inc="$inc -I $root/$d"
done
# camlp5 8 is an ocamlfind package with dependencies; camlp5 7 may not
# be registered with ocamlfind at all, so link its archive by path.
if ocamlfind query -predicates syntax,preprocessor,byte -format '%a' camlp5 2>/dev/null | grep -q 'camlp5.cma'; then
   pkgs=camlp5,unix,str,threads.posix; c5lib=""
else
   pkgs=unix,str,threads.posix; c5lib="$c5/camlp5.cma"
fi
cp "$here/pin_filter_ocaml.ml" "$tmp/"
# MLast's let bindings differ between camlp5 7 and 8.
case "$(camlp5 -v 2>&1)" in
   *"version 7."*) cp "$here/pin_compat_camlp5_7.ml" "$tmp/pin_compat.ml" ;;
   *) cp "$here/pin_compat_camlp5_8.ml" "$tmp/pin_compat.ml" ;;
esac
cd "$tmp"
ocamlfind ocamlc -predicates syntax,preprocessor -package $pkgs -thread -rectypes -linkpkg \
   -I "$c5" $inc -custom $c5lib \
   "$root/libmojave/lm.cma" "$root/mllib/util.cma" "$root/refiner/refiner.cma" \
   "$root/filter/prlc.cma" "$c5/pa_o.cmo" \
   -cclib -L"$root/libmojave/cutil" -cclib -L"$root/clib" \
   -cclib -llmcutil -cclib "$root/clib/clib.a" \
   pin_compat.ml pin_filter_ocaml.ml -o pin
# PIN_TIMEOUT (seconds, default 600) bounds the run; ./pin is killed by
# its own pid if it is still running then.
./pin $files > "$out" &
pin=$!
n=0
while kill -0 "$pin" 2>/dev/null && [ "$n" -lt "${PIN_TIMEOUT:-600}" ]; do
   sleep 1; n=$((n + 1))
done
if kill -0 "$pin" 2>/dev/null; then
   kill "$pin"
   echo "pin_filter_ocaml: TIMEOUT after ${n}s; partial output in $out" >&2
   exit 3
fi
wait "$pin"
echo "pin_filter_ocaml: $(grep -c '^== ' "$out") files, $(grep -c 'roundtrip=' "$out") items, $(grep -c 'roundtrip=same' "$out") round-trip same -> $out"
