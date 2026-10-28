#!/bin/sh
# Compare a pin run with the expected file.
#   compare_pin.sh pin_filter_ocaml.expected out.txt
# Exit 0 when every item has the same term structure (shape=), round trip
# and free variables.  Items whose full term differs only in its source
# locations are counted and reported, not failed: camlp5 7 and 8 record
# locations differently.
set -e
exp=$1; out=$2
[ -s "$out" ] || { echo "compare_pin: no output in $out" >&2; exit 2; }
strip() { awk '{ if ($3 ~ /^shape=/) $2 = "-"; print }' "$1"; }
strip "$exp" > "${out:?}.exp-shape"
strip "$out" > "${out:?}.out-shape"
total=$(grep -c '^[0-9]' "$exp")
locs=$(diff "$exp" "$out" | grep -c '^>' || true)
if diff "${out:?}.exp-shape" "${out:?}.out-shape" > "${out:?}.shape-diff"; then
   echo "compare_pin: structure OK for all $total items; $locs differ only in locations"
   rm -f -- "${out:?}.exp-shape" "${out:?}.out-shape" "${out:?}.shape-diff"
else
   echo "compare_pin: STRUCTURE DIFFERS on $(grep -c '^>' "${out:?}.shape-diff") of $total items (see ${out:?}.shape-diff)"
   exit 1
fi
