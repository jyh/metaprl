#!/bin/sh
# Pin what the shell's `ls` options select (Shell_util.option_of_char).
#
# On one module (itt_int_base, in the default build), `ls "<opts>"` is run
# for each option, and each listing is checked by the KIND of its entries,
# not by counts (how many rules are proved depends on the build):
#   r   only rewrites and definitions, at least one of each
#   R   only rules, at least one
#   rR  exactly the entries of r and of R together
#   u   only rewrites and rules that are not proved ("!" status), and every
#       unproved rewrite or rule of r and R is listed
#   p   only the Extends lines, the same as the plain listing's
#   d   only display forms, precedences and the declarations they display
#   D   only documentation
#   f   formal items only (no let, dform, doc, Extends)
#   a   every entry of f and of i
#   Z   the error "ls: unrecognized option 'Z'", and the shell goes on
# An entry is a line that does not start with a space; its kind is the word
# after the status bracket ("?[1,2] rewrite ...", "![<H> ⊢ .] rule ..."),
# or else its first word. A bracket that holds a goal spans several lines
# and is joined to the line that closes it.
#
# Usage: sh editor/ml/tests/ls_options.sh [MP]
#   from the metaprl root, after a build. Every check must see its listing,
#   so an mp that loads nothing fails rather than passes.
MP=${1:-editor/ml/mp}
out=${TMPDIR:-/tmp}/ls_options.$$
opts='none r R rR u p d D f i a Z'
{
   for o in $opts; do
      a=$o; [ "$o" = none ] && a=
      printf 'cd "/lsopt_%s";;\ncd "/itt_int_base";;\nls "%s";;\n' "$o" "$a"
   done
   printf 'cd "/lsopt_end";;\n'
} | "$MP" -batch 2>&1 | tr -d '\r\016\017\f' | sed 's/\x1b\[[0-9;]*m//g' > "${out:?}"

awk -v opts="$opts" '
function kind(l,   m) {
   if (match(l, /^[!?#*]\[[^]]*\] +[A-Za-z_]+/)) {
      m = substr(l, RSTART, RLENGTH); sub(/^[!?#*]\[[^]]*\] +/, "", m); return m
   }
   split(l, w, " "); return w[1]
}
/module lsopt_[A-Za-z]+ does not exist/ {
   s = $0; sub(/.*module lsopt_/, "", s); sub(/ does not exist.*/, "", s); sec = s; seen[sec] = 1; next
}
sec == "" { next }
{ text[sec] = text[sec] $0 "\n" }
# A status bracket that holds a whole goal wraps: "![" alone, then the goal,
# then "...] rule name :". The entry is the bracket joined to that line.
pend != "" && /\] +[A-Za-z_]+ / {
   l = $0; sub(/^.*\] +/, "", l); add(pend "] " l); pend = ""; next
}
/^[!?#*]\[$/ { pend = $0; next }
/^[^ ]/ {
   l = $0; sub(/Failure:$/, "", l)
   if (l == "" || l == "Failure:" || l ~ /^Module:/ || l ~ /^Uncaught exception:/) next
   add(l)
}
function add(l,   k) {
   k = kind(l)
   n[sec]++; e[sec, n[sec]] = l; ek[sec, n[sec]] = k; has[sec, l] = 1; cnt[sec, k]++
}
function only(s, allowed,   i, k, bad) {
   bad = ""
   for (i = 1; i <= n[s]; i++) { k = ek[s, i]; if (index(" " allowed " ", " " k " ") == 0) { bad = e[s, i]; break } }
   return bad
}
function check(name, ok, why) {
   if (ok) { print "PASS " name } else { print "FAIL " name ": " why; fails++ }
}
END {
   split(opts, os, " ")
   for (i in os) if (!seen[os[i]]) { print "FAIL ls \"" os[i] "\": its marker never appeared (did the shell stop?)"; fails++ }
   if (!seen["end"]) { print "FAIL the end marker never appeared"; fails++ }
   b = only("r", "rewrite define");    check("r: rewrites and definitions only", b == "" && cnt["r", "rewrite"] > 0 && cnt["r", "define"] > 0, b == "" ? "none listed" : b)
   b = only("R", "rule");              check("R: rules only", b == "" && cnt["R", "rule"] > 0, b == "" ? "none listed" : b)
   ok = n["rR"] == n["r"] + n["R"] && n["rR"] > 0; why = "rR " n["rR"] " entries, r " n["r"] " + R " n["R"]
   for (i = 1; i <= n["r"]; i++) if (!has["rR", e["r", i]]) { ok = 0; why = "missing " e["r", i] }
   for (i = 1; i <= n["R"]; i++) if (!has["rR", e["R", i]]) { ok = 0; why = "missing " e["R", i] }
   check("rR: the entries of r and R together", ok, why)
   ok = 1; why = ""
   for (i = 1; i <= n["u"]; i++) {
      if (e["u", i] ~ /^!/) { ok = 0; why = "proved entry listed: " e["u", i] }
      if (ek["u", i] != "rewrite" && ek["u", i] != "rule") { ok = 0; why = "not a rewrite or rule: " e["u", i] }
   }
   for (i = 1; i <= n["rR"]; i++) {
      l = e["rR", i]; k = ek["rR", i]
      if ((k == "rewrite" || k == "rule") && l !~ /^!/ && !has["u", l]) { ok = 0; why = "unproved entry not listed: " l }
   }
   check("u: exactly the unproved rewrites and rules", ok, why)
   b = only("p", "Extends"); ok = b == "" && n["p"] > 0 && n["p"] == cnt["none", "Extends"]
   for (i = 1; i <= n["p"]; i++) if (!has["none", e["p", i]]) ok = 0
   check("p: the Extends lines of the plain listing", ok, b == "" ? "p " n["p"] ", plain " cnt["none", "Extends"] : b)
   b = only("d", "dform prec declare"); check("d: display forms only", b == "" && cnt["d", "dform"] > 0, b == "" ? "none listed" : b)
   b = only("D", "doc docdocoff");      check("D: documentation only", b == "" && n["D"] > 0, b == "" ? "none listed" : b)
   ok = n["f"] > 0; why = "none listed"
   for (i = 1; i <= n["f"]; i++) { k = ek["f", i]; if (k == "let" || k == "dform" || k == "doc" || k == "Extends" || k == "open") { ok = 0; why = e["f", i] } }
   check("f: formal items only", ok, why)
   ok = n["a"] > 0; why = "none listed"
   for (i = 1; i <= n["f"]; i++) if (!has["a", e["f", i]]) { ok = 0; why = "missing formal " e["f", i] }
   for (i = 1; i <= n["i"]; i++) if (!has["a", e["i", i]]) { ok = 0; why = "missing informal " e["i", i] }
   check("a: every entry of f and of i", ok, why)
   check("Z: unrecognized option, and the shell goes on", index(text["Z"], "ls: unrecognized option '"'"'Z'"'"'") > 0 && seen["end"], "no error text")
   exit fails > 0
}' "$out"
status=$?
[ $status -ne 0 ] && { echo "--- mp output: $out"; exit 1; }
rm -f -- "${out:?}"
echo "ls_options: all checks pass"
