#!/bin/bash
# Program 3 exploration reset: drop session-written .cmoz (newer than the last green build), rebuild.
R=${VIR_METAPRL:?set VIR_METAPRL to the metaprl checkout}
T=$(cd "$(dirname "$0")" && pwd)
cd "$R" || exit 90
find theories -name '*.cmoz' -newer theories/vir/.build-stamp -print -delete
"$T/build.sh" "$R" "$T/build3.log"
