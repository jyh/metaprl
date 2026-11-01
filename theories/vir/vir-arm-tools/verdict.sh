#!/bin/sh
# O95 MetaPRL arm, loop 1: the BATCH VERDICT for theories/vir.
# Replays every stored proof of module vir in `mp -batch` (which does not auto-save)
# and compares each rule's status with verdict.expected ("rule status").
# REFUSES (rc 3) if theories/vir/vir.cmoz is newer than .build-stamp (build.sh writes it on rc 0):
# an `mp -cli` session writes vir.cmoz at exit and later sessions load it in
# preference to the stored proof (.prla), so the verdict would read the session,
# not the archive. Remedy: rm vir.cmoz and rebuild (the build regenerates it).
# Usage: verdict.sh ROOT [out] [module]   (module vir by default; vir2 reads verdict2.expected)
#        exit 0 = every rule as expected
# LIMIT: checks status and rule-box count, not the proofs' content.
root=${1:?usage: verdict.sh ROOT [out]}
here=$(cd "$(dirname "$0")" && pwd)
mod=${3:-vir}
sfx=${mod#vir}
out=${2:-$here/verdict$sfx.out}
d="$root/theories/vir"
[ -f "$d/$mod.cmoz" ] && [ -f "$d/.build-stamp" ] || { echo "VERDICT REFUSED rc=3: no vir.cmoz or no .build-stamp in $d (build with build.sh)"; exit 3; }
if [ "$d/$mod.cmoz" -nt "$d/.build-stamp" ]; then
   echo "VERDICT REFUSED rc=3: vir.cmoz is newer than the last green build (an mp -cli session wrote it); delete it and rebuild"
   exit 3
fi
printf 'cd "/vir/%s";;\nstatus_all ();;\n' "$mod" | "$root/editor/ml/mp" -batch 2>&1 | tr -d '\r' \
   | sed 's/\x1b\[[0-9;]*m//g' \
   | awk '/^Status: `/ { r=$2; gsub(/[`'"'"']/,"",r);
          if ($0 ~ /complete proof/ && $0 !~ /incomplete/) s="complete"; else if ($0 ~ /incomplete/) s="incomplete"; else s="other";
          match($0, /\(([0-9]+) rule boxes/); n=substr($0, RSTART+1, RLENGTH-12); print r, s, n }' > "$out"
n=$(wc -l < "$out" | tr -d ' ')
if [ "$n" -eq 0 ]; then echo "VERDICT FAIL rc=2: no Status lines (module not entered?)"; exit 2; fi
if diff "$here/verdict$sfx.expected" "$out" > "$out.diff"; then
   echo "VERDICT OK rc=0: $n rules as expected ($out)"; exit 0
else
   echo "VERDICT DIFF rc=1: see $out.diff"; cat "$out.diff"; exit 1
fi
