#!/bin/sh
# An INSTALL_DIR containing a space must stay one entry of THEORYPATH.
# On Windows the default INSTALL_DIR can be "C:\Program Files"; before the
# fix, mk/config split it into two entries and the next omake run failed
# re-reading mk/config. This regenerates mk/config with a spaced
# INSTALL_DIR, loads it in a scratch omake project, and checks that
# THEORYPATH has three entries, the last "$INSTALL_DIR/theories".
# The tree's own mk/config is kept and restored.
# Usage: install_dir_space.sh    (run from anywhere; needs omake; exit 0 = pass)
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tmp=$(mktemp -d)
probe="$tmp/probe"
mkdir "$probe"
if [ -f "$root/mk/config" ]; then cp "$root/mk/config" "$tmp/config.saved"; fi
restore() {
   if [ -f "$tmp/config.saved" ]; then cp "$tmp/config.saved" "$root/mk/config"; else rm -f "$root/mk/config"; fi
}
trap restore EXIT
dir="$tmp/install dir"
rm -f "$root/mk/config"
# The first run writes mk/config and stops (mk/load_config).
(cd "$root" && INSTALL_DIR="$dir" omake --no--progress > "$tmp/configure.log" 2>&1)
if [ ! -f "$root/mk/config" ]; then
   echo "FAIL: omake did not write mk/config"; cat "$tmp/configure.log"; exit 1
fi
printf 'ROOT = %s\ninclude %s/mk/config\nprintln($"PROBE $(length $(THEORYPATH))")\nprintln($"LAST $(nth 2, $(THEORYPATH))")\n' \
   "$root" "$root" > "$probe/OMakeroot"
: > "$probe/OMakefile"
(cd "$probe" && INSTALL_DIR="$dir" omake --no--progress > "$tmp/probe.log" 2>&1)
n=$(sed -n 's/^PROBE //p' "$tmp/probe.log" | tr -d '\r')
last=$(sed -n 's/^LAST //p' "$tmp/probe.log" | tr -d '\r')
if [ "$n" != 3 ]; then
   echo "FAIL: THEORYPATH has ${n:-no} entries, expected 3"; cat "$tmp/probe.log"; exit 1
fi
case "$last" in
   *"install dir"*theories) echo "OK: THEORYPATH has 3 entries, the last is $last" ;;
   *) echo "FAIL: the last THEORYPATH entry is '$last', expected one ending in 'install dir/theories'"; exit 1 ;;
esac
