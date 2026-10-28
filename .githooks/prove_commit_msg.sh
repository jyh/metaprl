#!/bin/sh
# prove_commit_msg.sh -- RED PROVEN BEFORE GREEN IS BELIEVED, for .githooks/commit-msg.
#
# Drives the hook through a real `git commit` in a scratch repository, never by
# calling the hook directly: a direct call cannot see what git does around it
# (the message file, the exit plumbing, whether HEAD moved).
#
#   PRECONDITION -- each of the five trailer shapes is exactly ONE finding for the
#                   gate itself. A shape the gate lets through would make its
#                   refusal arm vacuous, not strict.
#   RED arms     -- each shape is REFUSED: the commit is not created.
#   GREEN arms   -- a clean message, with Co-Authored-By and a line that merely
#                   NAMES the rule, is committed unchanged.
#   MUTATION     -- a refused message commits with --no-verify, so every refusal
#     CONTROL       above is the hook's and not the fixture's.
#   FAIL CLOSED  -- the gate in no tree and no ref, or the scanner missing: even a
#                   clean message is refused.
#   REF FALLBACK -- the gate absent from the tree but present in origin's default
#                   branch: the hook still refuses a forbidden shape.
#
# ⛔ THE SHAPES ARE NOT RETYPED. They are assembled from the gate's own constants
#    at run time; this is a tracked file that the trailer gate scans.
# ⛔ THE SANDBOX IS REACHED BY ABSOLUTE PATH AND `git -C`, NEVER BY `cd`.
#
# usage:  sh .githooks/prove_commit_msg.sh
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/.." && pwd)
HOOK="$HERE/commit-msg"
SCAN="$HERE/gate_scan.py"
TRAILER_GATE="$REPO/scripts/check_commit_trailers.py"

fail=0
note() { printf '%s\n' "$*"; }
bad()  { printf 'FAIL %s\n' "$*"; fail=$((fail + 1)); }

[ -f "$HOOK" ]         || { note "FAIL: no $HOOK"; exit 2; }
[ -x "$HOOK" ]         || { note "FAIL: $HOOK is not executable -- it would be INERT on this platform"; exit 2; }
[ -f "$SCAN" ]         || { note "FAIL: no $SCAN"; exit 2; }
[ -f "$TRAILER_GATE" ] || { note "FAIL: no $TRAILER_GATE"; exit 2; }

PY=
for c in python3 python py; do
  if "$c" -c "" >/dev/null 2>&1; then PY="$c"; break; fi
done
[ -n "$PY" ] || { note "FAIL: no working python interpreter"; exit 2; }

read_const() {
  "$PY" - "$1" "$2" <<'PYEOF'
import sys, types
src_path, expr = sys.argv[1], sys.argv[2]
mod = types.ModuleType("_gate_under_proof")
mod.__file__ = src_path
with open(src_path, encoding="utf-8") as fh:
    exec(compile(fh.read(), src_path, "exec"), mod.__dict__)
print(eval(expr, mod.__dict__))
PYEOF
}

KEY=$(read_const "$TRAILER_GATE" '_SESSION_KEY') || KEY=
HOST=$(read_const "$TRAILER_GATE" '_HOST.replace(chr(92), "")') || HOST=
KEPT=$(read_const "$TRAILER_GATE" 'PRESERVED') || KEPT=
[ -n "$KEY" ] && [ -n "$HOST" ] && [ -n "$KEPT" ] || { note "FAIL: could not read the shapes out of the gate"; exit 2; }
LOWER_KEY=$(printf '%s' "$KEY" | tr 'A-Z' 'a-z')
SHAPE_1="${KEY}: 0123456789abcdef"
SHAPE_2="see https://${HOST}/code/session_0123456789abcdef"
SHAPE_3="${LOWER_KEY}: 0123456789abcdef"
SHAPE_4="${KEY} : 0123456789abcdef"
SHAPE_5="https://${HOST}/chat/0123456789abcdef"

note "prove_commit_msg: every arm states its expected outcome BEFORE it runs"
note "PRECONDITION  each shape is exactly one finding for the gate itself"
for i in 1 2 3 4 5; do
  eval "shape=\$SHAPE_$i"
  n=$(MSG="$shape" read_const "$TRAILER_GATE" 'len(scan([("m", __import__("os").environ["MSG"])]))') || n=
  if [ "$n" = "1" ]; then
    printf '  ok   shape %s is forbidden by the gate\n' "$i"
  else
    note "FAIL: shape $i is not exactly one gate finding (got '${n}') -- nothing below would be proven"
    exit 2
  fi
done

SBX=$(mktemp -d) || { note "FAIL: mktemp -d"; exit 2; }
cleanup() {
  case "${SBX:-}" in
    /*/*) [ -d "$SBX" ] && rm -rf -- "$SBX" ;;
    *) note "refusing to remove '${SBX:-<empty>}'" ;;
  esac
}
trap cleanup EXIT
W="$SBX/work"
mkdir -p "$W/.githooks" "$W/scripts"
git init -q "$W"
git -C "$W" symbolic-ref HEAD refs/heads/main
git -C "$W" config user.email prover@example.invalid
git -C "$W" config user.name  "commit-msg prover"
git -C "$W" config commit.gpgsign false
git -C "$W" config core.autocrlf false
cp "$HOOK" "$W/.githooks/commit-msg"
chmod +x "$W/.githooks/commit-msg"
cp "$SCAN" "$W/.githooks/gate_scan.py"
cp "$TRAILER_GATE" "$W/scripts/check_commit_trailers.py"
git -C "$W" add -A
git -C "$W" commit -q --no-verify -m "seed: the gate and the hook"
SEED=$(git -C "$W" rev-parse HEAD)
git -C "$W" config core.hooksPath .githooks

OUT="$SBX/out.txt"
n=0
# try_commit <expect: made|refused> <label> <message> [git commit args...]
try_commit() {
  want=$1; label=$2; msg=$3; shift 3
  n=$((n + 1))
  before=$(git -C "$W" rev-parse HEAD)
  printf '%s\n' "$n" > "$W/file.txt"
  git -C "$W" add -- file.txt
  printf '%s\n' "$msg" | git -C "$W" commit -q -F - "$@" > "$OUT" 2>&1
  if [ "$(git -C "$W" rev-parse HEAD)" = "$before" ]; then got=refused; else got=made; fi
  if [ "$got" = "$want" ]; then
    printf '  ok   %-28s commit %s (expected %s)\n' "$label" "$got" "$want"
  else
    printf '  FAIL %-28s commit %s expected=%s\n' "$label" "$got" "$want"
    sed 's/^/         | /' "$OUT"
    fail=$((fail + 1))
  fi
  git -C "$W" reset -q --hard "$before"
}

CLEAN="docs: a clean message

This hook forbids session trailers and chat-service links; naming the rule is fine.

${KEPT}: somebody <nobody@example.invalid>"

note "ARM 1-5  each trailer shape in a message                        expect refused"
for i in 1 2 3 4 5; do
  eval "shape=\$SHAPE_$i"
  try_commit refused "red-shape-$i" "docs: a message with shape $i

${KEPT}: somebody <nobody@example.invalid>
${shape}"
  grep -qF "REFUSED" "$OUT" || bad "red-shape-$i: the refusal did not say REFUSED"
done

note "ARM 6  a clean message, attribution kept, the rule named        expect made"
before=$(git -C "$W" rev-parse HEAD)
printf 'clean\n' > "$W/file.txt"; git -C "$W" add -- file.txt
printf '%s\n' "$CLEAN" | git -C "$W" commit -q -F - > "$OUT" 2>&1
if [ "$(git -C "$W" rev-parse HEAD)" = "$before" ]; then
  bad "green-clean: the hook refused a clean message"; sed 's/^/         | /' "$OUT"
elif [ "$(git -C "$W" log -1 --format=%B)" = "$CLEAN" ]; then
  printf '  ok   %-28s committed, message byte-identical\n' green-clean
else
  bad "green-clean: the committed message differs from the one written"
fi
git -C "$W" reset -q --hard "$before"

note "ARM 7  mutation control: shape 3 with --no-verify               expect made"
try_commit made mutation-control "docs: shape 3, hook bypassed

${SHAPE_3}" --no-verify

note "ARM 8  gate absent from the tree, present in origin/main        expect refused"
git -C "$W" update-ref refs/remotes/origin/main "$SEED"
git -C "$W" rm -q -- scripts/check_commit_trailers.py
git -C "$W" commit -q --no-verify -m "branch: predates the gate"
try_commit refused ref-fallback-refuses "docs: shape 1 on a gateless branch

${SHAPE_1}"
try_commit made ref-fallback-clean "$CLEAN"

note "ARM 9  gate in no tree and no ref: fail closed                  expect refused"
git -C "$W" update-ref -d refs/remotes/origin/main
try_commit refused fail-closed-no-gate "$CLEAN"
grep -qF "cannot find" "$OUT" || bad "fail-closed-no-gate: the refusal did not name the missing gate"
git -C "$W" reset -q --hard "$SEED"

note "ARM 10 the scanner is missing: fail closed                      expect refused"
mv "$W/.githooks/gate_scan.py" "$SBX/gate_scan.py.hidden"
try_commit refused fail-closed-no-scanner "$CLEAN"
mv "$SBX/gate_scan.py.hidden" "$W/.githooks/gate_scan.py"

note ""
if [ "$fail" -eq 0 ]; then
  note "prove_commit_msg: PASS -- 5 trailer shapes REFUSED through a real git commit,"
  note "  each first proven forbidden by the gate; a clean message with attribution"
  note "  commits byte-identical; the mutation control commits with the hook bypassed;"
  note "  the gate is read from origin's default branch when the tree lacks it; and a"
  note "  missing gate or scanner refuses even a clean message."
  exit 0
fi
note "prove_commit_msg: FAILED ($fail arm(s))"
exit 1
