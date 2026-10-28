#!/bin/sh
# Replay every stored proof and compare each rule's status with
# proof_census.expected. A change that breaks a stored proof, or drops one,
# shows as a diff. Needs mp built with THEORIES = all.
#
# Each expected line is "module rule status", where status is "primitive",
# "complete N" or "incomplete N" (N = rule boxes; 0 means no stored proof).
# The modules replayed are the ones the expected file names, EACH IN ITS OWN
# mp PROCESS: in one session the output depends on which modules were
# entered before, and a status can print under the wrong module.
# A module the shell cannot enter (cd prints no "Module: /m") is recorded
# as "m - notentered"; its status_all would otherwise replay every module.
# mp runs with -batch, which does not auto-save an archive.
# LIMIT: it checks status and rule-box count, not the proofs' content.
# Usage: proof_census.sh [out]   (exit 0 = same as expected)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
expected="$here/proof_census.expected"
out=${1:-$(mktemp)}
tmp=${PROOF_CENSUS_TMP:-$(mktemp -d)}
# An empty or missing expected file would replay nothing and compare equal.
if [ -z "$PROOF_CENSUS_ONE" ] && [ ! -s "$expected" ]; then
   echo "FAIL: $expected is missing or empty"
   exit 1
fi
[ -n "$PROOF_CENSUS_ONE" ] || cut -d' ' -f1 "$expected" | uniq > "$tmp/modules"
# One module: replay it and print "module rule status" lines.
one() {
   printf 'cd "/%s";;\nstatus_all ();;\n' "$1" | "$mp" -batch 2>&1 | tr -d '\r' \
      | sed 's/\x1b\[[0-9;]*m//g' | awk -v m="$1" '
      $0 == "Module: /" m { entered = 1; next }
      entered && /^Status: `/ {
         r = $0; sub(/^Status: `/, "", r); sub(/'"'"' is .*/, "", r)
         n = $0; sub(/.*proof \(/, "", n); sub(/ rule boxes.*/, "", n)
         if ($0 ~ /is a primitive/) s = "primitive"
         else if ($0 ~ /with a complete proof/) s = "complete " n
         else if ($0 ~ /with an incomplete proof/) s = "incomplete " n
         else s = "other"
         print m " " r " " s
      }
      END { if (!entered) print m " - notentered" }' > "$tmp/m.$1"
}
if [ -n "$PROOF_CENSUS_ONE" ]; then one "$PROOF_CENSUS_ONE"; exit 0; fi
xargs -P 4 -I{} env PROOF_CENSUS_TMP="$tmp" PROOF_CENSUS_ONE={} sh "$0" < "$tmp/modules"
: > "$out"
while read -r m; do cat "$tmp/m.$m" >> "$out" 2>/dev/null; done < "$tmp/modules"
echo "replayed: $(wc -l < "$tmp/modules" | tr -d ' ') modules, $(wc -l < "$out" | tr -d ' ') rule statuses"
if [ ! -s "$out" ]; then
   echo "FAIL: no rule status was replayed"
   exit 1
fi
if diff -u "$expected" "$out" > "$tmp/diff"; then
   echo "OK: every status as expected"
   exit 0
fi
head -60 "$tmp/diff"
echo "FAIL: $(grep -c '^[-+][^-+]' "$tmp/diff") changed lines (first 60 shown)"
exit 1
