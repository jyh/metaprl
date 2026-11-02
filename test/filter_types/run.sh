#!/bin/sh
# The filter's term-type checking (refiner/reflib/term_ty_infer.ml) on small
# theories: each *.ml here is preprocessed by the built filter (lib/camlp5n)
# outside the theory tree, after its interface (its extends and declare
# lines), and the outcome is compared with expected.txt:
#   <name> ACCEPTED
#   <name> REFUSED <term> has type <T>, used with type <U>   (a type error)
#   <name> REFUSED Failure: <message>                       (refused earlier)
# The builds of the theories show only that well-typed declarations are
# accepted; these fixtures check that ill-typed ones are refused, and why.
# Statements covered, one ok/bad pair or more each: prim_rw (check_rewrite),
# interactive (check_rule), dform (check_dform), iform (check_iform),
# production (check_production), declare rewrite (check_type_rewrite; that
# line is indented in its fixture so it stays out of the interface).
# Usage (from the metaprl root, after omake): sh test/filter_types/run.sh
# Exit 0 = the same as expected.txt.
set -u
# On Windows this shell is Cygwin's: pwd and mktemp print /cygdrive/... and
# /tmp/..., which the native filter cannot open, so hand it D:/... paths
# (as test/unit/run.sh does), and join MP_INCLUDE with ';', the filter's
# separator on Win32 (filter_main.ml set_path).
if command -v cygpath > /dev/null 2>&1; then win=1; else win=; fi
w() { if [ -n "$win" ]; then cygpath -m "$1"; else printf '%s' "$1"; fi; }
if [ -n "$win" ]; then psep=';'; else psep=':'; fi
root=$(w "$(pwd)")
here="$root/test/filter_types"
tmp=$(w "$(mktemp -d)")
trap 'rm -rf "$tmp"' EXIT
[ -x "$root/lib/camlp5n" ] || { echo "FAIL: $root/lib/camlp5n is not built"; exit 1; }
# Every built theory directory, for the filter's search path.
dirs=$(find "$root/theories" "$root/support" "$root/lib" -name '*.cmiz' -exec dirname {} \; | sort -u)
[ -n "$dirs" ] || { echo "FAIL: no built theory (.cmiz) found under $root"; exit 1; }
incs=""
for d in $dirs; do incs="$incs -I $d"; done
MP_ROOT="$root" MPLIB="$root/lib" MP_GROUP=filter_types MP_DESCR=filter_types \
MP_INCLUDE=$(printf '%s\n' $dirs | paste -sd"$psep" -)
export MP_ROOT MPLIB MP_GROUP MP_DESCR MP_INCLUDE
out="$tmp/out.txt"
: > "$out"
# In C-locale order: a shell glob sorts ok_term and ok_term_as_dform
# differently on macOS and Linux.
for src in $(cd "$here" && ls *.ml | LC_ALL=C sort | sed "s|^|$here/|"); do
   name=$(basename "$src" .ml)
   cp "$src" "$tmp/$name.ml"
   grep -E '^(extends|declare) ' "$src" > "$tmp/$name.mli"
   ( cd "$tmp" && "$root/lib/camlp5n" -loc _loc $incs "$name.mli" > "$name.mli.pp" 2> "$name.mli.err" ) \
      || { echo "$name INTERFACE-REFUSED" >> "$out"; continue; }
   if ( cd "$tmp" && "$root/lib/camlp5n" -loc _loc $incs "$name.ml" > "$name.ml.pp" 2> "$name.ml.err" ); then
      echo "$name ACCEPTED" >> "$out"
   else
      grep -v 'Quotation.upsert' "$tmp/$name.ml.err" | tr -d '\r' | awk -v n="$name" '
         { line = $0; sub(/^[ -]*/, "", line); sub(/[ ]*$/, "", line) }
         line == "type error:" { t = 1; k = 0; next }
         t { a[++k] = line }
         /^Failure: / && fail == "" { fail = line }
         END {
            for (i = 2; i <= k; i++) if (a[i] == "has type") { subj = a[i - 1]; has = a[i + 1] }
            for (i = 1; i <= k; i++) if (a[i] == "but is used with type") used = a[i + 1]
            if (has != "") printf "%s REFUSED %s has type %s, used with type %s\n", n, subj, has, used
            else if (fail != "") print n " REFUSED " fail
            else print n " REFUSED (no type error or failure text)" }' >> "$out"
   fi
done
cat "$out"
if diff -u "$here/expected.txt" "$out" > "$tmp/diff"; then echo "filter_types: same as expected.txt"; exit 0
else cat "$tmp/diff"; echo "filter_types: FAIL (output differs from expected.txt)"; exit 1; fi
