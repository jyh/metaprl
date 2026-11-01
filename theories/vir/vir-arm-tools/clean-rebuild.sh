#!/bin/bash
# Remove every session-written .cmoz under theories/ that is newer than the last
# green build, then rebuild and run program 1's verdict. (Until metaprl #88 this
# also deleted vir2.prla, which could not load: its id is >= 2^30.)
R=${VIR_METAPRL:?set VIR_METAPRL to the metaprl checkout}
T=$(cd "$(dirname "$0")" && pwd)
cd "$R" || exit 90
find theories -name '*.cmoz' -newer theories/vir/.build-stamp -print -delete
"$T/build.sh" "$R" || exit 1
"$T/verdict.sh" "$R"
