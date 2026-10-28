#!/bin/sh
# util/pa_macro must not make NOT, AND or OR keywords: the x86 compiler
# theory (theories/experimental/compile) names opcodes with them.
# The expected output is camlp5's own printer, without pa_macro, on the
# same input; and IFDEF must still choose the right branch.
# Usage: run_pa_macro.sh [macroprint]   (default: util/macroprint)
here=$(cd "$(dirname "$0")" && pwd)
mp=${1:-$here/../macroprint}
tmp=$(mktemp -d)
fail=0
camlp5o o_keywords.cmo pr_o.cmo "$here/kw.ml" > "$tmp/kw.expected" || { echo "FAIL: camlp5o on kw.ml"; exit 2; }
"$mp" "$here/kw.ml" > "$tmp/kw.out" 2>&1
if cmp -s "$tmp/kw.expected" "$tmp/kw.out"; then echo "OK   NOT/AND/OR as constructors"
else echo "FAIL NOT/AND/OR as constructors:"; cat "$tmp/kw.out"; fail=1; fi
camlp5o o_keywords.cmo pr_o.cmo "$here/ifdef_foo.ml" > "$tmp/if.expected" || { echo "FAIL: camlp5o on ifdef_foo.ml"; exit 2; }
"$mp" -D FOO "$here/ifdef.ml" > "$tmp/if.out" 2>&1
if cmp -s "$tmp/if.expected" "$tmp/if.out"; then echo "OK   IFDEF/IFNDEF with -D FOO"
else echo "FAIL IFDEF/IFNDEF with -D FOO:"; cat "$tmp/if.out"; fail=1; fi
exit $fail
