#!/bin/sh
# Pin how the shell resolves an absolute path (Shell_core.dir_of_path).
#
# A first component that names a THEORY (group) wins over a module of the same
# name. So "/itt_supinf" is the theory, "/itt_supinf/itt_supinf" is its module,
# and "/itt_supinf/<rule>" asks for a MODULE named <rule> in that theory and
# fails. A name that is only a module ("/itt_int_base") finds its theory.
# "fs" is the source browser. This precedence is what made Shell.extract read
# every rule of itt_rfun and itt_supinf as depending on itself until extract
# stopped going through dir_of_path; this test keeps the precedence itself
# from changing unseen.
#
# Relative paths (parse_path) are pinned the same way: ".." is the parent,
# "..." the grandparent, "~" the module of the current proof, "." the
# current directory, and a bare name is looked up below the current one.
# A theory component is not checked against the module: from itt_int_base
# (theory itt_core), "../itt_supinf" reaches module itt_supinf, which is in
# theory itt_supinf. That is pinned as it is, not endorsed.
#
# Usage: sh editor/ml/tests/dir_of_path_precedence.sh [MP]
#   from the metaprl root, after a build whose THEORIES include itt_supinf
#   (THEORIES = all does). Every case must print its own anchor, so a build
#   that does not load itt_supinf fails rather than passes.
MP=${1:-editor/ml/mp}
out=${TMPDIR:-/tmp}/dir_of_path_precedence.$$

# Case N is: cd "/"; cd "<path>" for each |-separated part; ls "". Before
# it, cd "/dop_case_N" fails
# with "module dop_case_N does not exist", which marks where case N starts.
set -- \
   '/'                                  'Root Theories Listing:' \
   '/itt_supinf'                        '(itt_supinf) contains:' \
   '/itt_supinf/itt_supinf'             'Module: /itt_supinf' \
   '/itt_supinf/ge_addMono2'            "Theory.get_theory: theory \`\`ge_addMono2'' not found" \
   '/itt_supinf/itt_supinf/ge_addMono2' 'BY ' \
   '/itt_int_base'                      'Module: /itt_int_base' \
   '/fs'                                'OMakeroot' \
   '/itt_supinf/itt_supinf/ge_addMono2|..'  'Extends itt_equal' \
   '/itt_supinf/itt_supinf/ge_addMono2|...' '(itt_supinf) contains:' \
   '/itt_supinf/itt_supinf/ge_addMono2|~'   'Extends itt_equal' \
   '/itt_supinf/itt_supinf|ge2transitive'   'BY ' \
   '/itt_supinf/itt_supinf|.'               'Extends itt_equal' \
   '/itt_int_base|../itt_supinf'            'Extends itt_equal'
{
   n=0; i=1
   while [ $i -le $# ]; do
      eval "p=\${$i}"
      n=$((n + 1))
      printf 'cd "/dop_case_%d";;\ncd "/";;\n' "$n"
      printf '%s\n' "$p" | tr '|' '\n' | while read -r part; do printf 'cd "%s";;\n' "$part"; done
      printf 'ls "";;\n'
      i=$((i + 2))
   done
   printf 'cd "/dop_case_end";;\n'
} | "$MP" -batch 2>&1 | tr -d '\r\016\017\f' | sed 's/\x1b\[[0-9;]*m//g' > "${out:?}"

fail=0
n=0; i=1
while [ $i -le $# ]; do
   eval "p=\${$i}"; eval "a=\${$((i + 1))}"
   n=$((n + 1))
   # The lines strictly between this case's marker and the next one.
   body=$(awk -v s="module dop_case_$n does not exist" '
      index($0, s) { on = 1; next }
      on && /module dop_case_[0-9a-z]+ does not exist/ { exit }
      on' "${out:?}")
   if [ -z "$body" ]; then
      echo "FAIL case $n $p: no output (marker missing or mp did not run)"; fail=1
   elif printf '%s\n' "$body" | grep -F -q -- "$a"; then
      echo "ok   case $n $p"
   else
      echo "FAIL case $n $p: no line containing: $a"; fail=1
   fi
   i=$((i + 2))
done
# Only case 4 may fail to resolve.
k=$(grep -c -F 'Theory.get_theory: theory' "${out:?}")
if [ "$k" = 1 ]; then echo "ok   exactly one unresolved path"; else echo "FAIL $k unresolved paths, expected 1"; fail=1; fi
[ "$fail" = 0 ] || { echo "--- mp output ---"; cat "${out:?}"; }
rm -f -- "${out:?}"
exit $fail
