#!/bin/sh
# Display forms print goals as expected. Nothing else pins printed output:
# the proof census reads rule statuses only. For each rule in
# dform_golden.list (one per itt/core module: its first rule with a stored
# complete proof in proof_census.expected), mp -batch prints the rule's
# node with `ls ""` (assumptions, goal, and the stored tactic text; the
# proof is not expanded), and the text is compared with
# dform_golden.expected, which is that output as generated from the code.
# One mp process per rule. ANSI escapes, CR, form feed and shift-in/out
# bytes are removed; the width is mp's default when stdout is not a
# terminal (80): this test never runs on a terminal.
# DFORM_MODE selects the display mode: prl (the default, mp's own, compared
# with dform_golden.expected), or src / tex (compared with
# dform_golden.<mode>.expected). Each mode marks the stored tactic its own
# way, and that mark must be present: BY  (prl), \textbf{BY } (tex),
# Summary!rule_box (src).
# LIMITS: the prl, src and tex modes only (html is not compared); one goal per module, so a display form
# no listed goal uses is not covered; a rule renamed or moved shows as
# a FAIL line, not as a display difference. Needs a built editor/ml/mp.opt.
# Usage: dform_golden.sh [out]   (exit 0 = same as expected)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
list="$here/dform_golden.list"
mode=${DFORM_MODE:-prl}
case "$mode" in
   prl) expected="$here/dform_golden.expected"; mark='BY '; set_mode= ;;
   tex) expected="$here/dform_golden.tex.expected"; mark='\textbf{BY }'; set_mode='set_dfmode "tex";;\n' ;;
   src) expected="$here/dform_golden.src.expected"; mark='Summary!rule_box'; set_mode='set_dfmode "src";;\n' ;;
   *) echo "FAIL: unknown DFORM_MODE $mode (prl, tex or src)"; exit 1 ;;
esac
out=${1:-$(mktemp)}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if [ ! -s "$list" ] || [ ! -s "$expected" ]; then
   echo "FAIL: $list or $expected is missing or empty"
   exit 1
fi
: > "$out"
while read -r m r; do
   [ -n "$m" ] || continue
   printf "${set_mode}"'cd "/%s/%s";;\nls "";;\n' "$m" "$r" | "$mp" -batch > "$tmp/raw" 2>&1
   tr -d '\r\014\016\017' < "$tmp/raw" | sed 's/\x1b\[[0-9;]*m//g; s/[ ]*$//' > "$tmp/clean"
   echo "== $m $r" >> "$out"
   # Keep what follows the "Module: /m" line that cd prints.
   if grep -q "^Module: /$m\$" "$tmp/clean" && grep -F -q -- "$mark" "$tmp/clean"; then
      sed -n "/^Module: \/$m\$/,\$p" "$tmp/clean" | sed '1d' >> "$out"
   else
      echo "FAIL: no Module line or no tactic mark ($mark) for $m $r" >> "$out"
   fi
done < "$list"
if diff -u "$expected" "$out"; then
   echo "OK   $(grep -c '^== ' "$out") goals print as expected ($mode mode)"
   exit 0
else
   echo "FAIL: display differs from $expected"
   exit 1
fi
