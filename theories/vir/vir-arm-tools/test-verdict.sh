#!/bin/sh
# Drive verdict.sh both ways: clean tree (expect 0), a session-written vir.cmoz (expect 3).
R=${VIR_METAPRL:?set VIR_METAPRL to the metaprl checkout}
T=$(cd "$(dirname "$0")" && pwd)
C="$R/theories/vir/vir.cmoz"
rm -f -- "$C"
"$T/build.sh" "$R" || exit 9
"$T/verdict.sh" "$R"; echo "clean rc=$?"
sleep 1; touch "$C"
"$T/verdict.sh" "$R"; echo "session-cmoz rc=$?"
rm -f -- "$C"
"$T/build.sh" "$R" || exit 9
"$T/verdict.sh" "$R"; echo "final rc=$?"
