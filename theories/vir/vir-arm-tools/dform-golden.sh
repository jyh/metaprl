#!/bin/sh
# Print the B' VIR terms through MetaPRL's display forms (mp -batch, read-only) to stdout:
# the transcription rules tc_U, tc_F, tc_U2, tc_F2 (virtc: the object's terms, expanded) and route_acl_safe's statement (vir3).
# Each listing is cut at its BY line (the goal only; an archive's stale extras are not shown).
# Usage: dform-golden.sh ROOT > dform-bprime.txt
R=${1:?usage: dform-golden.sh ROOT}
printf '%s\n' 'cd "/vir/virtc/tc_U";;' 'ls "";;' 'cd "/vir/virtc/tc_F";;' 'ls "";;' \
  'cd "/vir/virtc/tc_U2";;' 'ls "";;' 'cd "/vir/virtc/tc_F2";;' 'ls "";;' \
  'cd "/vir/vir3/route_acl_safe";;' 'ls "";;' \
  | "$R/editor/ml/mp" -batch 2>&1 | tr -d '\r\f\016\017' | sed 's/\x1b\[[0-9;]*m//g' \
  | awk '/^BY /{skip=1; next} /^Module: |^[?*#] .*<.>/{skip=0} !skip' \
  | grep -v -E '^(User time|Real time|MetaPRL|Current directory)|^[[:space:]]*$'
