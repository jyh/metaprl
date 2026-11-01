#!/bin/bash
# Build the VIR clone (omake -j2) and, on rc 0, write theories/vir/.build-stamp.
# NOT under the fleet lock: an OCaml build of ~2 GB (declared on the bus 2026-11-01 00:1x).
# Usage: build.sh ROOT [log]
root=${1:?usage: build.sh ROOT [log]}
here=$(cd "$(dirname "$0")" && pwd)
log=${2:-$here/build.log}
cd "$root" || exit 90
eval "$(opam env --switch=5.4.1 --set-switch)"
T0=$(date +%s)
omake -j2 > "$log" 2>&1
rc=$?
[ $rc -eq 0 ] && touch theories/vir/.build-stamp
echo "BUILD-END rc=$rc wall=$(( $(date +%s) - T0 ))s"
exit $rc
