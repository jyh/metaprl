#!/bin/sh
# itt_inv_typing.independentProductTypeElimination must not derive void.
# Until this test it added w: type{B} from type{A * B}, which is false when A
# is empty (type{void * B} holds for every B): with B = decide{x; a. unit;
# b. void} and x : top it derived void from the ITT core alone (42 primitive
# steps). The rule now adds w: (A -> type{B}), the form
# functionTypeElimination uses.
# Each case asserts a goal inside a proof of itt_record0's
# recordTypeElimination (a module that sees both top and this rule) and tries
# to close it. A case reads "close" only when the shell records the refine
# (its BY line names the assertion), "fail" only on a Refine error, and
# anything else (a quotation that did not parse, a module not entered) is a
# HARNESS error, exit 2: absence of an error is not a proof. The derivation
# of void must fail; the control (the derivation's true type{void * unit}
# step) must close.
# -batch: mp -cli auto-saves the archive after a refine.
# Needs a built editor/ml/mp. Usage: inv_typing_sound.sh   (exit 0 = sound)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
tmp=$(mktemp -d)
prod='rwh unfold_prod 0 thenT productType thenLT [autoT; voidElimination (-1)]'
void="assertT << decide{inr{it}; a. unit; b. void} >> thenLT [substT << inr{it} = inl{it} in top >> 0 thenLT [autoT; rw reduceC 0 thenT autoT; assertT << \"type\"{void * decide{'vv; a. unit; b. void}} >> thenLT [$prod; independentProductTypeElimination (-1) thenT nthHypT (-1)]]; rw reduceC (-1) thenT nthHypT (-1)]"
fail=0
check() { # goal tactic want
   printf 'cd "/itt_record0/recordTypeElimination";;\nrefine (assertT << %s >> thenAT completeT (%s));;\nls "";;\n' "$1" "$2" | "$mp" -batch 2>&1 | tr -d '\r\016\017' | sed 's/\x1b\[[0-9;]*m//g' > "$tmp/raw"
   if grep -q 'Refine error' "$tmp/raw"; then got=fail
   elif grep -q '^BY (assertT' "$tmp/raw"; then got=close
   else echo "HARNESS $1: neither a refine error nor a recorded refine:"; head -20 "$tmp/raw"; exit 2; fi
   if [ "$got" = "$3" ]; then echo "OK   $1: $got"
   else echo "FAIL $1: expected $3, got $got"; fail=1; fi
}
check '"type"{void * unit}' "$prod" close
check 'void' "$void" fail
exit $fail
