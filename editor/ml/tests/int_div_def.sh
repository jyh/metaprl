#!/bin/sh
# itt_int_ext's definitions of div and rem must compute what the primitive
# literal rewrites (reduce_div_meta, reduce_rem_meta) compute. Until this
# test, unfold_div's recursion dropped the "1 +@", so 7 /@ 2 unfolded to 0
# while reduce_div_meta gave 3, and False was derivable.
# Each case asserts "lhs ~ rhs" inside a proof of div_wf and closes it by
# unfolding the definitions and computing (no reduce_*_meta on the left):
# each value is the one reduce_div_meta / reduce_rem_meta gives; every case
# but the last must close, and the last (the old answer) must not.
# A case reads "close" only when the shell records the refine (its BY line),
# "fail" only on a Refine error; anything else (a quotation that did not
# parse, a module not entered) fails the test: absence of an error is not a
# proof.
# -batch: mp -cli auto-saves the archive after a refine.
# Needs a built editor/ml/mp. Usage: int_div_def.sh   (exit 0 = all agree)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
tmp=$(mktemp -d)
# rw, never byDefT: byDefT ends in autoT, which closes these goals with
# reduce_div_meta itself and would test nothing.
run='(tryT (rw (higherC unfold_rem) 0) thenT rw (higherC unfold_div) 0 thenT rw reduceC 0 thenT repeatT (rw (higherC reduce_fix) 0 thenT rw reduceC 0) thenT tryT autoT)'
cases='(7 /@ 2) ~ 3|close
((0 -@ 7) /@ 2) ~ (0 -@ 3)|close
(7 /@ (0 -@ 2)) ~ (0 -@ 3)|close
(7 %@ 2) ~ 1|close
((0 -@ 7) %@ 2) ~ (0 -@ 1)|close
(7 /@ 2) ~ 0|fail'
fail=0; i=0
echo "$cases" | while IFS='|' read -r goal want; do
   i=$((i+1))
   printf 'cd "/itt_int_ext/div_wf";;\nrefine (assertT << %s >> thenAT completeT %s);;\nls "";;\n' "$goal" "$run" | "$mp" -batch 2>&1 | tr -d '\r\016\017' | sed 's/\x1b\[[0-9;]*m//g' > "$tmp/raw$i"
   if grep -q 'Refine error' "$tmp/raw$i"; then got=fail
   elif grep -q '^BY (assertT' "$tmp/raw$i"; then got=close
   else echo "HARNESS $goal: neither a refine error nor a recorded refine:"; head -20 "$tmp/raw$i"; echo x >> "$tmp/failed"; continue; fi
   if [ "$got" = "$want" ]; then echo "OK   $goal: $got"
   else echo "FAIL $goal: expected $want, got $got"; echo x >> "$tmp/failed"; fi
done
[ -f "$tmp/failed" ] && exit 1
exit 0
