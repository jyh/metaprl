#!/bin/sh
# The MetaPRL shell must read a minus with one argument as negation, as
# OCaml does: proof steps such as `nameHypT (-1) "a"` depend on it.
# Each expression's value is taken from OCaml itself and compared with
# what the shell prints. Needs a built editor/ml/mp.opt.
# Usage: toploop_minus.sh    (run from anywhere; exit 0 = all agree)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
tmp=$(mktemp -d)
exprs='(0 - 1)
(-1)
(- 1)
(7 - 2 - 1)
(10 - (-3))
(-(2))
(-(1 + 1))
(3 - (-(1 + 1)))'
# After each expression a sentinel (9000 + i) marks where its output ends.
printf '%s\n' "$exprs" | awk '{ print $0 ";;"; print "(9000 + " NR ");;" }' > "$tmp/in"
# A terminal is needed: without one the shell reads no input.
if script --version >/dev/null 2>&1; then
   (cat "$tmp/in"; sleep 20) | script -q -c "$mp -cli" "$tmp/raw" >/dev/null 2>&1   # util-linux
else
   (cat "$tmp/in"; sleep 20) | script -q "$tmp/raw" "$mp" -cli >/dev/null 2>&1        # BSD
fi
tr -d '\r' < "$tmp/raw" | sed 's/\x1b\[[0-9;]*m//g' > "$tmp/out"
# For expression i: the "value : type" line before sentinel 900i, or "".
result() {
   awk -v i="$1" '
      /^# *900[0-9]+ : int$/ { n = $2 + 0 - 9000; if (n == i) { print got; exit } got = ""; next }
      /^# *.* : [a-z>-][a-z> -]*$/ { line = $0; sub(/^# */, "", line); got = line }' "$tmp/out"
}
fail=0; i=0
printf '%s\n' "$exprs" | while IFS= read -r e; do
   i=$((i+1))
   want=$(printf 'print_int %s;;\n' "$e" | ocaml -stdin 2>&1)
   got=$(result $i)
   if [ "$got" = "$want : int" ]; then echo "OK   $e = $want"
   else echo "FAIL $e: OCaml gives $want, the shell printed '$got'"; echo x >> "$tmp/failed"; fi
done
[ -f "$tmp/failed" ] && exit 1
exit 0
