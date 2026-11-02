#!/bin/sh
# `omake install` must work when INSTALL_DIR contains a space. Run after a
# build: this sets INSTALL_DIR in mk/config to a fresh "<tmp>/install dir",
# runs `omake install`, and checks that lib, bin, mk and theories land
# there and that nothing was created at the split path "<tmp>/install".
# mk/config is restored afterwards. The install target copies with OMake's
# own cp, so this runs on Linux, macOS and Windows.
# Usage: install_space.sh    (run from anywhere; exit 0 = pass)
here=$(cd "$(dirname "$0")" && pwd)
# On Windows this shell is Cygwin's: pwd and mktemp print /cygdrive/... and
# /tmp/..., which native Windows omake cannot open, so use D:/... paths
# (as test/unit/run.sh and the filter tests do).
w() { if command -v cygpath > /dev/null 2>&1; then cygpath -m "$1"; else printf '%s' "$1"; fi; }
root=$(w "$(cd "$here/../../.." && pwd)")
tmp=$(w "$(mktemp -d)")
dir="$tmp/install dir"
test -f "$root/mk/config" || { echo "FAIL: no mk/config (build first)"; exit 1; }
cp "$root/mk/config" "$tmp/config.saved"
trap 'cp "$tmp/config.saved" "$root/mk/config"' EXIT
awk -v d="$dir" '/^INSTALL_DIR = / { print "INSTALL_DIR = " d; next } { print }' "$tmp/config.saved" > "$root/mk/config"
grep -q -F "INSTALL_DIR = $dir" "$root/mk/config" || { echo "FAIL: could not set INSTALL_DIR in mk/config"; exit 1; }
(cd "$root" && omake --no--progress install > "$tmp/install.log" 2>&1)
rc=$?
fail=0
for d in lib bin mk theories; do
   if [ -d "$dir/$d" ]; then echo "OK   $dir/$d"; else echo "FAIL $dir/$d is missing"; fail=1; fi
done
if [ -e "$tmp/install" ]; then echo "FAIL the split path $tmp/install was created"; fail=1; fi
if [ "$rc" != 0 ]; then echo "FAIL omake install exited $rc"; fail=1; fi
if [ "$fail" != 0 ]; then tail -30 "$tmp/install.log"; exit 1; fi
echo "OK: omake install wrote to a path with a space"
