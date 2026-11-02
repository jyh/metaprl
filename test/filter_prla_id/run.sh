#!/bin/sh
# A module's proof archive (.prla) stores the module's id, an OCaml int
# from Filter_cache_fun.hash, as a decimal. Reading it back, the filter
# refused an id >= 2^30 ("Filter_summary.dest_id: not an int"): Lm_num
# reads such a decimal as a big number, and dest_id asked Lm_num whether
# it fits Lm_num's 30-bit Int. An id >= 2^30 is possible on 64-bit (the
# hash is seeded with 0x6ace12d4, bit 30 set), so such a module could not
# build from its text archive. No committed archive has one (211 of 234
# carry an id, all with |id| < 2^30), so nothing showed it until a new
# module drew one.
# The test compiles a copy of itt_pairwise2 (interface and implementation)
# under another name with its .prla, the archive's id replaced by each id
# below, through lib/camlp5n as the build does, and records whether the
# implementation is accepted. The ids: one >= 2^30, one below, and one
# negative (archives written on 32-bit carry negative ids).
# Run after the build, from the metaprl root. Exit 1 if the output
# differs from expected.
set -u
# On Windows this shell is Cygwin's: pwd and mktemp print /cygdrive/... and
# /tmp/..., which the native filter cannot open, so hand it D:/... paths
# (as test/unit/run.sh does), and join MP_INCLUDE with ';', the filter's
# separator on Win32 (filter_main.ml set_path).
if command -v cygpath > /dev/null 2>&1; then win=1; else win=; fi
w() { if [ -n "$win" ]; then cygpath -m "$1"; else printf '%s' "$1"; fi; }
if [ -n "$win" ]; then psep=';'; else psep=':'; fi
root=$(w "$(pwd)")
here="$root/test/filter_prla_id"
tmp=$(w "$(mktemp -d)")
trap 'rm -rf "$tmp"' EXIT
[ -x "$root/lib/camlp5n" ] || { echo "FAIL: $root/lib/camlp5n is not built"; exit 1; }
src="$root/theories/itt/core/itt_pairwise2"
[ -f "$src.prla" ] || { echo "FAIL: $src.prla is missing"; exit 1; }
dirs=$(find "$root/theories" "$root/support" "$root/lib" -name '*.cmiz' -exec dirname {} \; | sort -u)
incs="-I $tmp"
for d in $dirs; do incs="$incs -I $d"; done
MP_ROOT="$root" MPLIB="$root/lib" MP_GROUP=filter_prla_id MP_DESCR=filter_prla_id \
MP_INCLUDE=$(printf '%s\n' "$tmp" $dirs | paste -sd"$psep" -)
export MP_ROOT MPLIB MP_GROUP MP_DESCR MP_INCLUDE
out="$tmp/out.txt"
: > "$out"
for id in 1511842520 609661056 -1000750977; do
   rm -f "$tmp"/idfix.*
   cp "$src.ml" "$tmp/idfix.ml"
   cp "$src.mli" "$tmp/idfix.mli"
   # Replace the number on the line after the archive's id summary.
   awk -v id="$id" '
      done == 0 && prev ~ /^NSummary!id\tid\tid Summary$/ && $0 ~ /^P\tp[0-9]+\tNumber -?[0-9]+$/ {
         sub(/Number -?[0-9]+$/, "Number " id); done = 1 }
      { print; prev = $0 }
      END { if (done != 1) exit 3 }' "$src.prla" > "$tmp/idfix.prla" \
      || { echo "FAIL: no id line in $src.prla"; exit 1; }
   if ! ( cd "$tmp" && "$root/lib/camlp5n" -loc _loc $incs idfix.mli > idfix.mli.pp 2> idfix.mli.err ); then
      echo "id $id: interface refused" >> "$out"
   elif ( cd "$tmp" && "$root/lib/camlp5n" -loc _loc $incs idfix.ml > idfix.ml.pp 2> idfix.ml.err ); then
      echo "id $id: accepted" >> "$out"
   else
      msg=$(grep -v 'Quotation.upsert' "$tmp/idfix.ml.err" | tr -d '\r' | grep -E 'dest_id|Failed|Error' | head -1 | sed 's/^ *//')
      echo "id $id: REFUSED ($msg)" >> "$out"
   fi
done
if diff -u "$here/expected" "$out"; then
   echo "OK   $(wc -l < "$out" | tr -d ' ') archive ids read as expected"
else
   echo "FAIL: output differs from $here/expected"
   exit 1
fi
