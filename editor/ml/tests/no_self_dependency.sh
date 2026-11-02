#!/bin/sh
# No rule's grounded check may name the rule ITSELF as its incomplete dependency.
#
# check_all () asks the refiner for each proved rule's dependencies. The refiner
# fetches a rule's proof through Shell_command.extract [module; rule]. Until this
# was fixed, that pair was resolved as a PATH FROM THE ROOT, where a first
# component naming a THEORY (group) wins over a module of the same name, so every
# rule of itt_rfun (theory itt_rfun) and itt_supinf (theory itt_supinf) read
# "complete ungrounded ... depends on an incomplete /<module>/<itself>".
#
# Usage: sh editor/ml/tests/no_self_dependency.sh [MP]
#   from the metaprl root, after a THEORIES = all build.
# Exit 0 iff there is no self-dependency AND the run checked at least 1000 rules
# in at least 50 modules (a run that loads nothing is not a pass).
MP=${1:-editor/ml/mp}
out=${TMPDIR:-/tmp}/no_self_dependency.$$
printf 'check_all ();;\n' | "$MP" -batch 2>&1 | tr -d '\r\016\017' | sed 's/\x1b\[[0-9;]*m//g' > "${out:?}"
# A record starts at "Refiner status:" and may wrap over several lines; join it,
# then read "Refiner status: NAME is a ...".
awk '
   function flush() {
      if (rec == "") return
      gsub(/[ \t]+/, " ", rec)
      n++
      name = rec; sub(/^Refiner status: /, "", name); sub(/ .*/, "", name)
      if (rec ~ /depends on an incomplete \//) {
         dep = rec; sub(/.*depends on an incomplete /, "", dep); sub(/ .*/, "", dep)
         if (dep == "/" m "/" name) { self++; print "SELF-DEPENDENCY " m "/" name }
      }
      rec = ""
   }
   /^Module: \// { flush(); m = substr($2, 2); mods++; next }
   /^Refiner status:/ { flush(); rec = $0; next }
   rec != "" && /^[ \t]/ { rec = rec " " $0; next }
   { flush() }
   END {
      flush()
      printf "no_self_dependency: %d rules checked in %d modules; %d self-dependencies\n", n, mods, self + 0
      exit (self + 0 > 0 || n < 1000 || mods < 50) ? 1 : 0
   }' "${out:?}"
rc=$?
rm -f -- "${out:?}"
exit $rc
