#!/bin/sh
# Proofs whose rule carries a `~labels:` resource annotation must load.
# Archives saved in 2006 store that annotation in the 2005 form
# lab[name]{opt(e)}; before filter_ocaml read that form, the whole rule was
# dropped from the archive and the rule loaded with no proof
# ("0 rule boxes"). The four rules below are in itt/core, so a default
# build links them. Needs a built editor/ml/mp.opt.
#
# LIMIT: the build takes a module's proofs from the NEWEST of its archives
# (mllib/file_base.ml), so this tests the committed .prla only when no newer
# .prlb or older-built .cmoz shadows it, as in a fresh clone; the script
# prints the newest .prla/.prlb. mp runs with -batch, which does not
# auto-save, so the test itself writes no archive.
# Usage: old_labels.sh    (run from anywhere; exit 0 = every proof loads)
here=$(cd "$(dirname "$0")" && pwd)
mp="$here/../mp"
dir="$here/../../../theories/itt/core"
newest=$(ls -t "$dir"/itt_list2.prlb "$dir"/itt_list2.prla 2>/dev/null | head -1)
echo "newest proof archive: $(basename "$newest")"
tmp=$(mktemp -d)
printf 'cd "/itt_list2";;\nstatus_all ();;\n' | "$mp" -batch > "$tmp/raw" 2>&1
tr -d '\r' < "$tmp/raw" | sed 's/\x1b\[[0-9;]*m//g' > "$tmp/out"
fail=0
for r in reduce_mem_cons exists_list_wf2 bexists_list_wf2 map_wf2; do
   line=$(grep -a "^Status: \`$r'" "$tmp/out" | head -1)
   boxes=$(printf '%s\n' "$line" | sed -n 's/.*(\([0-9][0-9]*\) rule boxes.*/\1/p')
   if [ -n "$boxes" ] && [ "$boxes" -gt 0 ]; then
      echo "OK   $r: $boxes rule boxes"
   else
      echo "FAIL $r: ${line:-no status line}"
      fail=1
   fi
done
exit $fail
