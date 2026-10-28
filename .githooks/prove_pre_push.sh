#!/bin/sh
# prove_pre_push.sh -- RED PROVEN BEFORE GREEN IS BELIEVED, for .githooks/pre-push.
#
# A guard that has only ever been seen to pass is indistinguishable from a guard
# that cannot fail. This prover drives BOTH arms of .githooks/pre-push against a
# real `git push` into a real (scratch, bare) remote:
#
#   GREEN arms  -- a clean push must SUCCEED **and print its receipt**. A silent
#                  success is not evidence: a hook that never ran passes too.
#   RED arms    -- a private-record path in a commit MESSAGE, the same path in a
#                  FILE the commit ADDS, each of the FIVE trailer shapes in a
#                  message, and a path and a URL each ADDED THEN REMOVED inside
#                  one push must each be REFUSED, and the remote ref must NOT
#                  have moved. The add-then-remove arms first show the net-diff
#                  gate alone passing, so they test the population they name.
#                  A lane name in a SUBJECT only, a family reference in a
#                  SUBJECT only, and a lane name in a BODY only are each REFUSED
#                  too (desk QA), each after a control shows the two older arms
#                  passing that range.
#   FAIL CLOSED -- with the scanner missing, a clean push is refused; so it is
#                  with the subject gate missing.
#   DELETE arm  -- deleting a ref pushes no objects and must be ALLOWED.
#   REWIND arm  -- a clean force-push that moves a ref BACKWARDS must be ALLOWED
#                  (desk ML #6: the range picker tests ancestry, not existence).
#   MUTATION    -- the same refused push must SUCCEED with `--no-verify`. Without
#     CONTROL      this arm, every red above is equally consistent with "the push
#                  would have failed anyway", and the prover would prove nothing.
#
# ⛔ THE FIXTURES ARE NOT RETYPED. The forbidden shapes are read OUT OF THE GATE
#    SCRIPTS THEMSELVES (check_private_paths._EMPLOYER and
#    check_commit_trailers._SESSION_KEY), assembled at run time. Two reasons, and
#    the second is not style: a retyped fixture drifts silently when the gate's
#    list changes, AND this prover is a TRACKED FILE that the gate's own tree
#    ratchet scans -- spelling a private path here would make the prover trip the
#    gate it exists to drive.
#
# ⛔ THE SANDBOX IS REACHED BY ABSOLUTE PATH AND `git -C`, NEVER BY `cd`. A
#    fixture that reaches its sandbox by changing directory can, on any early
#    failure, run its git commands against THE REPOSITORY UNDER TEST.
#
# usage:  sh .githooks/prove_pre_push.sh
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/.." && pwd)
HOOK="$HERE/pre-push"
PATHS_GATE="$REPO/scripts/check_private_paths.py"
TRAILER_GATE="$REPO/scripts/check_commit_trailers.py"
SUBJECT_GATE="$REPO/scripts/check_pr_descriptions.py"
INFRA_GATE="$REPO/scripts/check_infra_names.py"
CERT_GATE="$REPO/scripts/check_cert_imports.py"
SUBJECT_BASELINE="$REPO/scripts/subject_debt_baseline.tsv"

fail=0
note() { printf '%s\n' "$*"; }
bad()  { printf 'FAIL %s\n' "$*"; fail=$((fail + 1)); }

[ -f "$HOOK" ]         || { note "FAIL: no $HOOK"; exit 2; }
[ -x "$HOOK" ]         || { note "FAIL: $HOOK is not executable -- it would be INERT on this platform"; exit 2; }
[ -f "$PATHS_GATE" ]   || { note "FAIL: no $PATHS_GATE"; exit 2; }
[ -f "$TRAILER_GATE" ] || { note "FAIL: no $TRAILER_GATE"; exit 2; }
[ -f "$SUBJECT_GATE" ] || { note "FAIL: no $SUBJECT_GATE"; exit 2; }
[ -f "$INFRA_GATE" ] || { note "FAIL: no $INFRA_GATE"; exit 2; }
[ -f "$SUBJECT_BASELINE" ] || { note "FAIL: no $SUBJECT_BASELINE"; exit 2; }

PY=
for c in python3 python py; do
  if "$c" -c "" >/dev/null 2>&1; then PY="$c"; break; fi
done
[ -n "$PY" ] || { note "FAIL: no working python interpreter"; exit 2; }

# ---- fixtures, read out of the gates ---------------------------------------
# Loading a gate as a module runs no main(): both guard it behind __main__.
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

PRIVATE_PATH=$(read_const "$PATHS_GATE" '_EMPLOYER[0] + "/notes/x.md"') || PRIVATE_PATH=
TRAILER_KEY=$(read_const "$TRAILER_GATE" '_SESSION_KEY') || TRAILER_KEY=
TRAILER_HOST=$(read_const "$TRAILER_GATE" '_HOST.replace(chr(92), "")') || TRAILER_HOST=
[ -n "$PRIVATE_PATH" ] || { note "FAIL: could not read the private-path fixture out of the gate"; exit 2; }
[ -n "$TRAILER_KEY" ]  || { note "FAIL: could not read the trailer key out of the gate"; exit 2; }
[ -n "$TRAILER_HOST" ] || { note "FAIL: could not read the trailer host out of the gate"; exit 2; }
SCAN="$HERE/gate_scan.py"
[ -f "$SCAN" ] || { note "FAIL: no $SCAN"; exit 2; }

# THE FIVE TRAILER SHAPES (census D #2). Each is assembled from the gate's own
# constants, and each must be FORBIDDEN BY THE GATE before an arm may use it: a
# shape the gate lets through would make its RED arm vacuous, not strict.
LOWER_KEY=$(printf '%s' "$TRAILER_KEY" | tr 'A-Z' 'a-z')
SHAPE_1="${TRAILER_KEY}: 0123456789abcdef"
SHAPE_2="see https://${TRAILER_HOST}/code/session_0123456789abcdef"
SHAPE_3="${LOWER_KEY}: 0123456789abcdef"
SHAPE_4="${TRAILER_KEY} : 0123456789abcdef"
SHAPE_5="https://${TRAILER_HOST}/chat/0123456789abcdef"
for i in 1 2 3 4 5; do
  eval "shape=\$SHAPE_$i"
  n=$(MSG="$shape" read_const "$TRAILER_GATE" 'len(scan([("m", __import__("os").environ["MSG"])]))') || n=
  [ "$n" = "1" ] || { note "FAIL: trailer shape $i is not exactly one gate finding (got '${n}') -- its arm would prove nothing"; exit 2; }
done

# THE SUBJECT GATE'S WORDS, read out of it: the longest lane word (a short one
# could hide inside an ordinary word of this prover's own output) and the first
# family word. Each must be exactly one finding in a subject, or its arm is
# vacuous. Neither word is ever spelled in this file.
LANE_WORD=$(read_const "$SUBJECT_GATE" 'sorted(lane_words(), key=len)[-1]') || LANE_WORD=
KIN_WORD=$(read_const "$SUBJECT_GATE" '_KIN[0]') || KIN_WORD=
[ -n "$LANE_WORD" ] || { note "FAIL: could not read a lane word out of the subject gate"; exit 2; }
[ -n "$KIN_WORD" ]  || { note "FAIL: could not read a family word out of the subject gate"; exit 2; }
for w in "$LANE_WORD" "$KIN_WORD"; do
  n=$(MSG="tidy the $w notes" read_const "$SUBJECT_GATE" 'len(subject_scan([("s", __import__("os").environ["MSG"], "subject")]))') || n=
  [ "$n" = "1" ] || { note "FAIL: a subject-gate fixture is not exactly one finding (got '${n}') -- its arm would prove nothing"; exit 2; }
done

# The fixture must actually be forbidden, or every RED arm below is vacuous.
if "$PY" "$PATHS_GATE" --self-test >/dev/null 2>&1; then :; else
  note "FAIL: the private-paths gate's own self-test does not pass; nothing here is readable"
  exit 2
fi

# ---- sandbox ----------------------------------------------------------------
SBX=$(mktemp -d) || { note "FAIL: mktemp -d"; exit 2; }
cleanup() {
  case "${SBX:-}" in
    /*/*) [ -d "$SBX" ] && rm -rf -- "$SBX" ;;
    *) note "refusing to remove '${SBX:-<empty>}'" ;;
  esac
}
trap cleanup EXIT

REMOTE="$SBX/remote.git"
W="$SBX/work"
git init -q --bare "$REMOTE"
mkdir -p "$W/.githooks" "$W/scripts"
git init -q "$W"
git -C "$W" symbolic-ref HEAD refs/heads/main
git -C "$W" config user.email prover@example.invalid
git -C "$W" config user.name  "pre-push prover"
git -C "$W" config commit.gpgsign false
git -C "$W" config core.autocrlf false
git -C "$W" config advice.pushUpdateRejected false
git -C "$W" remote add origin "$REMOTE"

# ONLY pre-push is installed. Installing commit-msg too would make the RED arms
# unbuildable: that hook refuses the very trailer this prover must commit.
cp "$HOOK" "$W/.githooks/pre-push"
chmod +x "$W/.githooks/pre-push"
cp "$PATHS_GATE" "$W/scripts/check_private_paths.py"
cp "$TRAILER_GATE" "$W/scripts/check_commit_trailers.py"
cp "$SCAN" "$W/.githooks/gate_scan.py"
cp "$SUBJECT_GATE" "$W/scripts/check_pr_descriptions.py"
cp "$SUBJECT_BASELINE" "$W/scripts/subject_debt_baseline.tsv"
# ARM 4 of the hook (the infrastructure-name ratchet, council 2026-10-07 ruling 3) needs its gate in the
# fixture, or the hook refuses every push as "not in this working tree". No baseline is copied: in the
# fixture every added name is NEW, which is exactly the arm under test.
cp "$INFRA_GATE" "$W/scripts/check_infra_names.py"
# ARM 5 of the hook (the certificates' import rule) runs where its gate is present.
[ -f "$CERT_GATE" ] && cp "$CERT_GATE" "$W/scripts/check_cert_imports.py"
git -C "$W" config core.hooksPath .githooks

commit_file() { # <path> <content> <message>
  printf '%s\n' "$2" > "$W/$1"
  git -C "$W" add -- "$1"
  git -C "$W" commit -q --no-verify -F - <<EOF
$3
EOF
}

OUT="$SBX/out.txt"
run_push() { # <expected-exit> <label> <push args...>
  want=$1; label=$2; shift 2
  git -C "$W" push "$@" > "$OUT" 2>&1
  rc=$?
  if [ "$rc" -eq "$want" ]; then
    printf '  ok   %-22s exit=%s (expected %s)\n' "$label" "$rc" "$want"
    return 0
  fi
  printf '  FAIL %-22s exit=%s expected=%s\n' "$label" "$rc" "$want"
  sed 's/^/         | /' "$OUT"
  fail=$((fail + 1))
  return 1
}

expect_out() { # <label> <fixed string>
  if grep -qF -- "$2" "$OUT"; then
    printf '       +   %s: output carries "%s"\n' "$1" "$2"
  else
    bad "$1: output does NOT carry \"$2\""
    sed 's/^/         | /' "$OUT"
  fi
}

expect_no_out() { # <label> <fixed string>
  if grep -qF -- "$2" "$OUT"; then
    bad "$1: output carries \"$2\""
    sed 's/^/         | /' "$OUT"
  else
    printf '       +   %s: output does not carry "%s"\n' "$1" "$2"
  fi
}

remote_tip() { git -C "$REMOTE" rev-parse --verify --quiet "refs/heads/$1" 2>/dev/null; }

# A RED ARM THAT LEAKED MUST NOT DECIDE THE NEXT ONE. Measured on the unfixed hook
# (2026-09-13): trailer shape 3 landed, so every later push to main was a
# non-fast-forward, and git's OWN rejection (exit 1) scored as a hook refusal.
# Each red arm therefore puts the remote back where it found it.
restore_remote() { git -C "$REMOTE" update-ref refs/heads/main "$BEFORE_TIP"; }

note "prove_pre_push: every arm states its expected exit BEFORE it runs"
note "  sandbox: $SBX (never the repository under test)"
note ""

# ── ARM 1 ── first push of a new ref whose delta reaches the ROOT commit.
note "ARM 1  clean first push (new ref, root commit in the delta)   expect 0"
commit_file seed.txt "a role-worded line: the helm minuted it in its own brief" "seed: the clean base"
run_push 0 green-first-push origin main
expect_out green-first-push "pre-push OK"
expect_out green-first-push "MESSAGE ARM ONLY"
GOOD=$(git -C "$W" rev-parse HEAD)

# ── ARM 2 ── ordinary push onto an existing ref: a TWO-DOT range, so the gate's
# FILE arm runs. This is the positive control for ARM 5, which needs it.
note "ARM 2  clean push onto an existing ref (two-dot range)        expect 0"
commit_file clean2.txt "docs/QUEUE.md is a public path and stays" "clean: an added line the ruling permits"
run_push 0 green-two-dot origin main
expect_out green-two-dot "pre-push OK"
expect_out green-two-dot "delta against the remote tip"
expect_out green-two-dot "added lines scanned"
GOOD=$(git -C "$W" rev-parse HEAD)

# ── ARM 3 ── a NEW branch off an existing one: the merge-base arm.
note "ARM 3  clean push of a brand-new branch (merge-base arm)      expect 0"
git -C "$W" checkout -q -b feature
commit_file feat.txt "another seat's bank carries the superseded value" "feature: role-wording only"
run_push 0 green-new-branch origin feature
expect_out green-new-branch "merge-base with origin/"
git -C "$W" checkout -q main

# ── ARM 3b ── a clean force-push that REWINDS the ref (desk ML finding #6). The old
# remote tip still EXISTS in this clone, so an existence test picks the range
# `<old tip>..<new tip>`, which is EMPTY, and the gate refuses clean content.
# An ancestry test sees the old tip is not an ancestor and falls through.
note "ARM 3b clean force-push that REWINDS main                    expect 0"
commit_file rewind.txt "a line pushed and then rewound away" "clean: a commit the next push rewinds"
run_push 0 green-pre-rewind origin main
git -C "$W" reset -q --hard "$GOOD"
run_push 0 green-rewind -f origin main
expect_out green-rewind "pre-push OK"
if [ "$(remote_tip main)" = "$GOOD" ]; then
  printf '       +   green-rewind: the remote ref rewound to the earlier tip\n'
else
  bad "green-rewind: the remote ref is not at the earlier tip"
fi
# Whatever happened above, the arms below start from the remote at the earlier tip
# (a refused rewind leaves it AHEAD of this clone, and every later push would be
# git's own non-fast-forward rejection, read as the hook's).
git -C "$REMOTE" update-ref refs/heads/main "$GOOD"

# ── ARM 4 ── a private-record path in a COMMIT MESSAGE.
note "ARM 4  private path in a commit MESSAGE                       expect 1"
BEFORE_TIP=$(remote_tip main)
commit_file ok4.txt "nothing wrong with this line" "see $PRIVATE_PATH for the note"
BADSHA=$(git -C "$W" rev-parse HEAD)
run_push 1 red-message-path origin main
expect_out red-message-path "private-record path"
expect_out red-message-path "PUSH REFUSED by .githooks/pre-push"
if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
  printf '       +   red-message-path: the remote ref did NOT move\n'
else
  bad "red-message-path: THE REMOTE REF MOVED -- the refusal did not stop the objects"
fi
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARM 5 ── the same path in a FILE the commit ADDS (the arm a message-only
#             check is structurally blind to).
note "ARM 5  private path in an ADDED FILE LINE                     expect 1"
commit_file leak5.txt "the record is at $PRIVATE_PATH" "docs: a clean message over a dirty line"
run_push 1 red-file-path origin main
expect_out red-file-path "private-record path"
if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
  printf '       +   red-file-path: the remote ref did NOT move\n'
else
  bad "red-file-path: THE REMOTE REF MOVED"
fi
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARM 6 ── the FIVE trailer shapes in a commit message, one push each. v2 of
#             this hook caught shapes 1 and 2 and passed 3, 4 and 5 (census D #2).
#             Committed --no-verify because the commit-msg hook is deliberately
#             not installed in the sandbox.
for i in 1 2 3 4 5; do
  eval "shape=\$SHAPE_$i"
  note "ARM 6.$i trailer shape $i in a commit message                  expect 1"
  printf 'x%s\n' "$i" > "$W/t6.txt"
  git -C "$W" add -- t6.txt
  git -C "$W" commit -q --no-verify -F - <<EOF
docs: a commit whose message carries a forbidden shape

Co-Authored-By: somebody <nobody@example.invalid>
${shape}
EOF
  TRAILER_SHA=$(git -C "$W" rev-parse HEAD | cut -c1-10)
  run_push 1 "red-trailer-shape-$i" origin main
  expect_out "red-trailer-shape-$i" "commit message(s) carry a shape the trailer gate forbids"
  expect_out "red-trailer-shape-$i" "$TRAILER_SHA"
  # A CRASHED scanner also exits 1, and the hook reads 1 as a finding: the
  # refusal above cannot tell them apart (desk PX, driven). The trailer gate
  # hands back a LINE NUMBER, never the text, and the scanner prints it.
  expect_no_out "red-trailer-shape-$i" "Traceback"
  expect_out "red-trailer-shape-$i" "at line "
  if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
    printf '       +   red-trailer-shape-%s: the remote ref did NOT move\n' "$i"
  else
    bad "red-trailer-shape-$i: THE REMOTE REF MOVED"
  fi
  git -C "$W" reset -q --hard "$GOOD"; restore_remote
done

# ── ARM 7 ── deleting a ref sends no objects and must be allowed.
note "ARM 7  deleting a remote ref (local sha all zeros)            expect 0"
run_push 0 delete-allowed origin --delete feature
expect_out delete-allowed "is being DELETED"

# ── ARM 8 ── THE MUTATION CONTROL. Every RED above is only evidence if the same
#             push SUCCEEDS once the hook is out of the way.
note "ARM 8  mutation control: the refused push, with --no-verify   expect 0"
git -C "$W" checkout -q -b mutation-control "$BADSHA"
run_push 0 mutation-control origin --no-verify mutation-control
if [ -n "$(remote_tip mutation-control)" ]; then
  printf '       +   mutation-control: the SAME commit lands once the hook is bypassed\n'
  printf '           => every refusal above was the hook'"'"'s, not an accident of the fixture\n'
else
  bad "mutation-control: the bypassed push did not land -- the RED arms prove nothing"
fi
git -C "$W" checkout -q main

# ── ARM 9 ── ADD-THEN-REMOVE: a private path added by one commit and removed by
#             the next. The net diff is empty, so `--range` cannot see it; both
#             blobs are pushed. CONTROL FIRST: the --range gate alone must PASS on
#             this range, or the arm is not testing the population it names.
note "ARM 9  private path added, then removed, inside one push      expect 1"
commit_file leak9.txt "the record is at $PRIVATE_PATH" "docs: add a note"
ADDED_SHA=$(git -C "$W" rev-parse HEAD | cut -c1-10)
git -C "$W" rm -q -- leak9.txt
git -C "$W" commit -q --no-verify -m "docs: remove the note"
if ( cd "$W" && "$PY" scripts/check_private_paths.py --range "$GOOD..HEAD" ) >/dev/null 2>&1; then
  printf '       +   add-then-remove: CONTROL -- the --range gate alone passes this range\n'
else
  bad "add-then-remove: the --range gate alone already refuses this range, so the arm tests nothing new"
fi
run_push 1 red-add-then-remove origin main
expect_out red-add-then-remove "INTRODUCED by a commit"
expect_out red-add-then-remove "$ADDED_SHA leak9.txt"
if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
  printf '       +   red-add-then-remove: the remote ref did NOT move\n'
else
  bad "red-add-then-remove: THE REMOTE REF MOVED"
fi
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARM 10 ── the same population for a session URL in a FILE line. CI's trailer
#              gate scans the TIP's tracked files, which this range leaves clean.
note "ARM 10 session URL added to a file, then removed              expect 1"
commit_file leak10.txt "$SHAPE_2" "docs: add a link"
ADDED_SHA=$(git -C "$W" rev-parse HEAD | cut -c1-10)
git -C "$W" rm -q -- leak10.txt
git -C "$W" commit -q --no-verify -m "docs: remove the link"
if ( cd "$W" && "$PY" scripts/check_commit_trailers.py --range "$GOOD..HEAD" ) >/dev/null 2>&1; then
  printf '       +   add-then-remove-url: CONTROL -- the trailer gate alone passes this range\n'
else
  bad "add-then-remove-url: the trailer gate alone already refuses this range, so the arm tests nothing new"
fi
run_push 1 red-add-then-remove-url origin main
expect_out red-add-then-remove-url "$ADDED_SHA leak10.txt"
expect_no_out red-add-then-remove-url "Traceback"
expect_out red-add-then-remove-url "at line "
if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
  printf '       +   red-add-then-remove-url: the remote ref did NOT move\n'
else
  bad "red-add-then-remove-url: THE REMOTE REF MOVED"
fi
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARM 10b ── the infrastructure-name arm (ARM 4 of the hook): an added line carrying a host or
# account name is REFUSED and the refusal names the gate, never the name. The word is READ from the
# gate's own assembled list, so this prover spells nothing the tree ratchet would catch.
note "ARM 10b an added line with an infrastructure name (ARM 4)         expect 1"
INFRA_WORD=$(read_const "$INFRA_GATE" 'FORBIDDEN[1]') || INFRA_WORD=
[ -n "$INFRA_WORD" ] || { note "FAIL: could not read a forbidden word out of the infrastructure-name gate"; exit 2; }
PRE_INFRA=$(git -C "$W" rev-parse HEAD)
commit_file infra.txt "the box $INFRA_WORD ran it" "docs: a clean subject, a doc line"
run_push 1 red-infra-arm origin main
expect_out red-infra-arm "the infrastructure-name gate RED"
if grep -qF -- "$INFRA_WORD" "$OUT"; then bad "red-infra-arm: the refusal LEAKS the name"; fi
git -C "$W" reset -q --hard "$PRE_INFRA"; restore_remote

# ── ARM 11 ── FAIL CLOSED: with gate_scan.py absent the hook cannot read the
#              gates' patterns, and a CLEAN push must be refused, not waved on.
note "ARM 11 the scanner is missing: a clean push is refused        expect 1"
mv "$W/.githooks/gate_scan.py" "$SBX/gate_scan.py.hidden"
commit_file clean11.txt "nothing wrong with this line" "clean: nothing forbidden here"
run_push 1 fail-closed-no-scanner origin main
expect_out fail-closed-no-scanner "gate_scan.py is not in this working tree"
mv "$SBX/gate_scan.py.hidden" "$W/.githooks/gate_scan.py"
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARMS 12-14 ── the subject gate (desk QA). Each commit touches only a clean
#                 file, and each CONTROL shows the two older arms passing the
#                 same range, so a refusal here is the new arm's and nobody
#                 else's. The word must never appear in the output.
older_arms_pass() { # <range>
  ( cd "$W" && "$PY" "$SCAN" push --trailers-gate scripts/check_commit_trailers.py \
      --paths-gate scripts/check_private_paths.py "$1" ) >/dev/null 2>&1 \
  && ( cd "$W" && "$PY" scripts/check_private_paths.py --range "$1" ) >/dev/null 2>&1
}
subject_arm() { # <arm-no> <label> <message>
  note "ARM $1 $2   expect 1"
  commit_file "s$1.txt" "nothing wrong with this line" "$3"
  SUBJ_SHA=$(git -C "$W" rev-parse HEAD | cut -c1-12)
  if older_arms_pass "$GOOD..HEAD"; then
    printf '       +   subject-arm-%s: CONTROL -- the per-commit scan and the paths gate pass this range\n' "$1"
  else
    bad "subject-arm-$1: an older arm already refuses this range, so the arm tests nothing new"
  fi
  run_push 1 "red-subject-arm-$1" origin main
  expect_out "red-subject-arm-$1" "the subject gate RED"
  expect_out "red-subject-arm-$1" "commit $SUBJ_SHA"
  expect_no_out "red-subject-arm-$1" "Traceback"
  # Never expect_no_out here: its receipt prints the needle, and this output is
  # a public CI log. Neither branch below prints the word or the output.
  if grep -qF -- "$LANE_WORD" "$OUT"; then
    bad "red-subject-arm-$1: the output ECHOES the lane word (output withheld)"
  else
    printf '       +   red-subject-arm-%s: output does not echo the lane word\n' "$1"
  fi
  if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
    printf '       +   red-subject-arm-%s: the remote ref did NOT move\n' "$1"
  else
    bad "red-subject-arm-$1: THE REMOTE REF MOVED"
  fi
  git -C "$W" reset -q --hard "$GOOD"; restore_remote
}
subject_arm 12 "a lane name in a SUBJECT only      " "tidy the $LANE_WORD notes

a clean body"
expect_out red-subject-arm-12 "SUBJECT: an employer-lane or private project name"
subject_arm 13 "a family reference in a SUBJECT only" "ratified: the $KIN_WORD agreed

a clean body"
expect_out red-subject-arm-13 "SUBJECT: a family reference"
subject_arm 14 "a lane name in a BODY only         " "docs: a clean subject

see the $LANE_WORD notes"
expect_out red-subject-arm-14 "BODY: an employer-lane or private project name"

# ── ARM 16 ── a refused word in the pushed BRANCH NAME, with clean commits. The
#              family word, never a lane word: the push output prints the name.
note "ARM 16 a family reference in the pushed BRANCH NAME          expect 1"
git -C "$W" checkout -q -b "tidy-$KIN_WORD"
commit_file s16.txt "nothing wrong with this line" "docs: a clean subject"
run_push 1 red-ref-name origin "tidy-$KIN_WORD"
expect_out red-ref-name "the pushed ref name carries a refused word"
expect_out red-ref-name "the ref name: a family reference"
expect_no_out red-ref-name "Traceback"
if [ -z "$(remote_tip "tidy-$KIN_WORD")" ]; then
  printf '       +   red-ref-name: the branch did NOT reach the remote\n'
else
  bad "red-ref-name: THE BRANCH REACHED THE REMOTE"
fi
git -C "$W" checkout -q main
git -C "$W" branch -q -D "tidy-$KIN_WORD"

# ── ARM 15 ── FAIL CLOSED again: with the subject gate absent, a clean push is
#              refused rather than waved through on two of three arms.
note "ARM 15 the subject gate is missing: a clean push is refused   expect 1"
mv "$W/scripts/check_pr_descriptions.py" "$SBX/check_pr_descriptions.py.hidden"
commit_file clean15.txt "nothing wrong with this line" "clean: nothing forbidden here"
run_push 1 fail-closed-no-subject-gate origin main
expect_out fail-closed-no-subject-gate "check_pr_descriptions.py is not in this working tree"
mv "$SBX/check_pr_descriptions.py.hidden" "$W/scripts/check_pr_descriptions.py"
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ── ARMS 17-21 ── A TAG WHOSE COMMIT ORIGIN ALREADY HAS (the helm's ask, 2026-10-15).
# An annotated tag on a commit that is already public adds no commit, so every
# range arm listed zero commits and the hook refused it. ARM 17 is the arm that was
# RED on the hook as it stood; 18-18c are the tag-OBJECT arms (the message is the
# only new content, so it is the only place a leak can ride); 19 and 20 are the
# arms that keep the exception from widening.
git -C "$REMOTE" update-ref refs/heads/main "$GOOD"
git -C "$W" reset -q --hard "$GOOD"
remote_tag() { git -C "$REMOTE" rev-parse --verify --quiet "refs/tags/$1" 2>/dev/null; }
tag_not_landed() { # <label> <tag>
  if [ -z "$(remote_tag "$2")" ]; then
    printf '       +   %s: the tag did NOT reach the remote\n' "$1"
  else
    bad "$1: THE TAG REACHED THE REMOTE"
  fi
}

note "ARM 17 clean annotated tag on an ALREADY-PUBLIC commit         expect 0"
git -C "$W" tag -a tag-public-ok -m "a submission tag: the tree a paper cites" "$GOOD"
run_push 0 green-public-tag origin refs/tags/tag-public-ok
expect_out green-public-tag "pre-push OK"
expect_out green-public-tag "already an ancestor of"
expect_out green-public-tag "annotated tag object scanned"
if [ -n "$(remote_tag tag-public-ok)" ]; then
  printf '       +   green-public-tag: the tag reached the remote\n'
else
  bad "green-public-tag: the tag did NOT reach the remote"
fi

note "ARM 17b clean LIGHTWEIGHT tag on an already-public commit      expect 0"
git -C "$W" tag tag-public-light "$GOOD"
run_push 0 green-public-light-tag origin refs/tags/tag-public-light
expect_out green-public-light-tag "LIGHTWEIGHT tag"

note "ARM 18  tag MESSAGE carries a session URL                      expect 1"
git -C "$W" tag -a tag-red-url -m "cut for review: $SHAPE_2" "$GOOD"
run_push 1 red-tag-url origin refs/tags/tag-red-url
expect_out red-tag-url "carries a forbidden shape (named above)"
expect_out red-tag-url "PUSH REFUSED by .githooks/pre-push"
tag_not_landed red-tag-url tag-red-url

note "ARM 18b tag MESSAGE carries a private-record path              expect 1"
git -C "$W" tag -a tag-red-path -m "see $PRIVATE_PATH" "$GOOD"
run_push 1 red-tag-path origin refs/tags/tag-red-path
expect_out red-tag-path "carries a forbidden shape (named above)"
tag_not_landed red-tag-path tag-red-path

# Only a repository that HAS an infrastructure-name gate has this arm: a prover that
# skipped it silently would read as covered, so the skip is said.
if [ -n "${INFRA_WORD:-}" ]; then
  note "ARM 18c tag MESSAGE carries an infrastructure name             expect 1"
  git -C "$W" tag -a tag-red-infra -m "built on $INFRA_WORD" "$GOOD"
  run_push 1 red-tag-infra origin refs/tags/tag-red-infra
  expect_out red-tag-infra "carries a forbidden shape (named above)"
  if grep -qF -- "$INFRA_WORD" "$OUT"; then bad "red-tag-infra: the refusal LEAKS the name"; fi
  tag_not_landed red-tag-infra tag-red-infra
else
  note "ARM 18c SKIPPED: this repository has no infrastructure-name gate (not covered)"
fi

note "ARM 18d the tag NAME carries a refused word                    expect 1"
git -C "$W" tag -a "tidy-$KIN_WORD" -m "a clean message" "$GOOD"
run_push 1 red-tag-name origin "refs/tags/tidy-$KIN_WORD"
expect_out red-tag-name "the pushed tag name carries a refused word"
tag_not_landed red-tag-name "tidy-$KIN_WORD"

# ARM 19 -- the exception must not widen: a tag on an UNPUSHED commit still scans
# that commit. The commit's file line carries the private path; the tag message is clean.
note "ARM 19  tag on an UNPUSHED commit with a dirty line           expect 1"
commit_file leak19.txt "the record is at $PRIVATE_PATH" "docs: a clean message over a dirty line"
git -C "$W" tag -a tag-unpushed-red -m "a clean message" HEAD
run_push 1 red-tag-unpushed origin refs/tags/tag-unpushed-red
expect_out red-tag-unpushed "private-record path"
tag_not_landed red-tag-unpushed tag-unpushed-red
git -C "$W" reset -q --hard "$GOOD"

note "ARM 19b the same shape, CLEAN: still scanned, still passes    expect 0"
commit_file clean19.txt "nothing wrong with this line" "clean: a commit the tag adds"
git -C "$W" tag -a tag-unpushed-ok -m "a clean message" HEAD
run_push 0 green-tag-unpushed origin refs/tags/tag-unpushed-ok
expect_out green-tag-unpushed "commit(s) scanned"
expect_no_out green-tag-unpushed "already an ancestor of"
git -C "$W" reset -q --hard "$GOOD"; restore_remote

# ARM 22 -- THE TAGGER HEADER IS MEASURED BY WHAT IT ADDS (found at the first real
# push, 2026-10-15): the owner's identity is the author and committer of every public
# commit, so a listed word in it tripped the infra-name scan of the tag object and
# the arm refused EVERY tag he makes. ARM 17's fixture carried no listed word and so
# never drove the property the gate keys on. Here the identity IS a listed word.
if [ -n "${INFRA_WORD:-}" ]; then
  note "ARM 22  tagger carries a listed word the tagged commit ALSO carries   expect 0"
  printf '%s\n' "a line by the named identity" > "$W/ident22.txt"
  git -C "$W" add -- ident22.txt
  GIT_AUTHOR_NAME="$INFRA_WORD" GIT_AUTHOR_EMAIL="id@example.invalid" \
  GIT_COMMITTER_NAME="$INFRA_WORD" GIT_COMMITTER_EMAIL="id@example.invalid" \
    git -C "$W" commit -q --no-verify -m "docs: a clean subject by a named identity"
  IDC=$(git -C "$W" rev-parse HEAD)
  git -C "$W" push -q --no-verify origin main 2>/dev/null
  GIT_COMMITTER_NAME="$INFRA_WORD" GIT_COMMITTER_EMAIL="id@example.invalid" \
    git -C "$W" tag -a tag-ident-ok -m "a clean message" "$IDC"
  run_push 0 green-tag-same-identity origin refs/tags/tag-ident-ok
  expect_out green-tag-same-identity "NOT scanned (already public)"
  expect_no_out green-tag-same-identity "$INFRA_WORD"

  note "ARM 22b tagger carries a listed word the tagged commit does NOT   expect 1"
  GIT_COMMITTER_NAME="$INFRA_WORD" GIT_COMMITTER_EMAIL="id@example.invalid" \
    git -C "$W" tag -a tag-ident-red -m "a clean message" "$GOOD"
  run_push 1 red-tag-other-identity origin refs/tags/tag-ident-red
  expect_out red-tag-other-identity "an infrastructure name"
  if grep -qF -- "$INFRA_WORD" "$OUT"; then bad "red-tag-other-identity: the refusal LEAKS the name"; fi
  tag_not_landed red-tag-other-identity tag-ident-red
  git -C "$W" reset -q --hard "$GOOD"; restore_remote
else
  note "ARM 22/22b SKIPPED: this repository has no infrastructure-name gate (not covered)"
fi

# ARM 20 -- an EMPTY branch range is UNCHANGED by the tag branch. Measured on the
# hook as it stood (origin/master 553252d): remote tip == local tip does NOT refuse,
# it exits 0 and prints "adds NO commit that origin does not already have; nothing
# to scan" -- the receipt that says nothing was read. This arm pins that behaviour
# so the tag branch cannot silently turn it into a different verdict. git sends no
# ref line for an up-to-date ref, so the hook is driven directly with the line
# git would send.
# The two verdicts are the two hook generations that exist across the public repos
# (measured 2026-10-15): the generation that carries the ancestry guard on the remote
# tip (desk ML finding #6, ARM 3b) prints the receipt and exits 0; the older one
# refuses "scanned ZERO commits". Which one this repository's hook is, is read from
# the hook; the tag branch must leave EITHER unchanged.
if grep -qF 'merge-base --is-ancestor "$remote_sha"' "$HOOK"; then
  note "ARM 20  empty BRANCH range (tip == tip): receipt, unchanged   expect 0"
  want20=0
else
  note "ARM 20  empty BRANCH range (tip == tip): refused, unchanged   expect 1"
  want20=1
fi
printf 'refs/heads/main %s refs/heads/main %s\n' "$GOOD" "$GOOD" > "$SBX/ref-line.txt"
( cd "$W" && sh .githooks/pre-push origin "$REMOTE" < "$SBX/ref-line.txt" ) > "$OUT" 2>&1
rc=$?
if [ "$rc" -eq "$want20" ]; then
  printf '  ok   %-22s exit=%s (expected %s)\n' empty-branch-range-unchanged "$rc" "$want20"
else
  printf '  FAIL %-22s exit=%s expected=%s\n' empty-branch-range-unchanged "$rc" "$want20"
  sed 's/^/         | /' "$OUT"
  fail=$((fail + 1))
fi
if [ "$want20" -eq 0 ]; then
  expect_out empty-branch-range-unchanged "adds NO commit that origin does not already have; nothing to scan"
else
  expect_out empty-branch-range-unchanged "scanned ZERO commits"
fi
expect_no_out empty-branch-range-unchanged "already an ancestor of"

# ARM 21 -- MUTATION CONTROL for the tag arms: the refused tag lands with --no-verify,
# so ARM 18's refusal is the hook's and not git's.
note "ARM 21  mutation control: the refused tag, --no-verify        expect 0"
run_push 0 mutation-tag --no-verify origin refs/tags/tag-red-url
if [ -n "$(remote_tag tag-red-url)" ]; then
  printf '       +   mutation-tag: the tag landed once the hook was bypassed\n'
else
  bad "mutation-tag: the bypassed push did not land the tag"
fi

# ARM 23 -- the certificates' import rule (hook ARM 5, C1 · A2e): a file under
# SaltC1/Cert54/ that imports the Salt library is REFUSED, the remote unmoved; the
# same file importing Mathlib passes, so the refusal is the import's and not the path's.
git -C "$REMOTE" update-ref refs/heads/main "$GOOD"
git -C "$W" reset -q --hard "$GOOD"
if [ -f "$CERT_GATE" ]; then
  BEFORE_TIP=$(remote_tip main)
  mkdir -p "$W/SaltC1/Cert54"
  note "ARM 23  a Salt import under SaltC1/Cert54/                  expect 1"
  commit_file SaltC1/Cert54/Planted.lean "import Salt.MaynardK.Cert105" "cert: a planted import"
  run_push 1 red-cert-import origin main
  expect_out red-cert-import "refused import"
  expect_out red-cert-import "the certificates' import gate RED"
  if [ "$(remote_tip main)" = "$BEFORE_TIP" ]; then
    printf '       +   red-cert-import: the remote ref did NOT move\n'
  else
    bad "red-cert-import: THE REMOTE REF MOVED"
  fi
  git -C "$W" reset -q --hard "$GOOD"; restore_remote
  note "ARM 23b the same file importing Mathlib                    expect 0"
  mkdir -p "$W/SaltC1/Cert54"
  commit_file SaltC1/Cert54/Planted.lean "import Mathlib.Data.Int.Basic" "cert: a clean import"
  run_push 0 green-cert-import origin main
  expect_out green-cert-import "check_cert_imports OK"
  expect_out green-cert-import "cert-imports --rev"
  git -C "$W" reset -q --hard "$GOOD"; restore_remote
else
  note "ARM 23/23b SKIPPED: this repository has no certificates' import gate (not covered)"
fi

note ""
if [ "$fail" -eq 0 ]; then
  note "prove_pre_push: PASS -- 3 clean pushes each SUCCEED and print a receipt"
  note "  (plus a clean tag on an already-public commit, which is scanned by its"
  note "  tag OBJECT and refused when that carries a leak, a tag on an unpushed"
  note "  commit still scanned, an empty branch range's receipt unchanged);"
  note "  naming the range; 12 leak shapes (message path, added-line path, the 5"
  note "  trailer shapes, a path and a URL each added then removed inside one"
  note "  push, and a lane name or family reference in a subject or a lane name in"
  note "  a body) are each REFUSED with the remote ref unmoved, and so is a branch"
  note "  whose name carries a refused word; a missing scanner"
  note "  or subject gate refuses a clean push; a delete is allowed; and the"
  note "  mutation control lands the same commit with the hook bypassed, so the"
  note "  refusals are the hook's; and a Salt import under SaltC1/Cert54/ is"
  note "  refused where a Mathlib import passes."
  exit 0
fi
note "prove_pre_push: FAILED ($fail arm(s))"
exit 1
