#!/usr/bin/env python3
"""The history scrub was a one-time act. Nothing has watched it since.

WHY THIS EXISTS
---------------
On 2026-07-22 this repository's public history was rewritten to strip a
per-commit trailer that embedded a private chat-session URL. That was a
deliberate, expensive, irreversible act: every SHA before it died, and commits
from that era must now be cited by subject line because their hashes no longer
resolve.

The rule that followed it lives in prose, in a project instruction file. Prose
is read by people who read that file, and this repository has spent a fortnight
cataloguing what happens to a rule that no machine enforces. This is that
pattern's sharpest instance yet, because the cost of a lapse is not a red test:
**it is a second history rewrite, or a permanent leak.** A commit message cannot
be edited after it is pushed and fetched without breaking every clone.

Measured at the time this gate was written: `origin/main` carried **zero**
occurrences across 3067 commits — the scrub held. And **five unmerged commits on
a live feature branch each carried one**, queued to merge. The rule had already
lapsed; only the merge had not happened yet. A guard that arrives the week the
first violation appears is a guard that arrived late, which is the argument for
writing it now rather than after the next scrub.

WHAT IT CHECKS
--------------
Every commit message reachable from HEAD (or a supplied range) against a small
set of forbidden patterns. Not file contents — a URL in a source comment is a
different question with a different answer, and conflating them would make this
gate mean two things.

FAILING CLOSED
--------------
A scan that resolves to zero commits REDS rather than reporting success. An
empty scan and a clean scan produce the same green otherwise, and this
repository has shipped that exact fault twice in one fortnight: a corpus
generator that wrote nothing and reported success, and a resolver that answered
`{}` for a kind it did not recognise. The rule adopted from that, and applied
here in this order: **a gate must be shown to fail on an empty input set before
it is allowed to pass on a full one** (`--self-test` proves both).

WHAT THIS DELIBERATELY DOES NOT DO
----------------------------------
* It does not scan working-tree files. A chat URL pasted into a doc is a
  content question; this is a HISTORY question, and history is the one that
  cannot be fixed with an ordinary commit.
* It cannot see a commit that has not been written yet, which is the whole
  reason it belongs in CI on every push rather than in a local hook only.
* It says nothing about `Co-Authored-By`, which is CORRECT and stays. The scrub
  removed session URLs; it deliberately kept authorship attribution, and a gate
  that swept both would quietly undo a decision it was never asked about.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import pathlib
import subprocess
import sys

# The forbidden shapes. Assembled from parts so that this file's own source can
# be grepped for the literal without matching, and so a commit message
# DESCRIBING the rule (like the one that adds this gate) does not trip it.
_SESSION_KEY = "Claude" + "-Session"
_HOST = r"claude\.ai"

FORBIDDEN = [
    (re.compile(rf"^\s*{re.escape(_SESSION_KEY)}\s*:", re.I | re.M),
     f"a {_SESSION_KEY} trailer"),
    (re.compile(rf"https?://(?:[\w.-]+\.)?{_HOST}/\S+", re.I),
     "a chat-service session URL"),
]

# Attribution the scrub deliberately KEPT. Named here so a future reader does
# not "tidy" it into the forbidden list.
PRESERVED = "Co-Authored-By"

# What a finding prints in place of the matched text. A CI log on a public
# repository is public (desk PX).
WITHHELD = "matched text withheld: this log is public"

ROOT = pathlib.Path(__file__).resolve().parent.parent


def commit_messages(rev_range: str) -> list[tuple[str, str]]:
    """(sha, message) for every commit in `rev_range`, newest first."""
    # Sentinels are passed through git's own %x-escapes rather than as literal
    # argv bytes: a NUL in argv raises ValueError before git is ever reached.
    sep = "@@JASCOMMIT@@"
    out = subprocess.run(
        ["git", "log", f"--format=%H%x1f%B{sep}", rev_range], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8", check=True,
    ).stdout
    rows = []
    for chunk in out.split(sep):
        chunk = chunk.strip("\n")
        if not chunk:
            continue
        sha, _, body = chunk.partition("\x1f")
        rows.append((sha.strip(), body))
    return rows


def tracked_files() -> list[tuple[str, str]]:
    """Every tracked TEXT file, as (path, contents).

    WHY THIS EXISTS. The trailer gate scanned commit MESSAGES only, and said so
    proudly — it is a history gate. But on 2026-08-05 the windows seat found a
    real session URL sitting in his hook's proof script AS TEST DATA, caught it
    by eye, and sanitised it before sending. **Nothing in this repository would
    have caught it.** A forbidden string in a FILE ships to a public repo just
    as surely as one in a commit message, and the message gate is structurally
    blind to it — it is not scanning the wrong thing, it is scanning a
    different thing.

    Same FORBIDDEN list, deliberately: the patterns have exactly one definition
    in this tree and both scans read it.

    This file needs no exemption. Its patterns are assembled from parts
    (`_SESSION_KEY`, `_HOST`) precisely so its own source never matches them —
    verified by the self-test, which would otherwise pass vacuously by
    excluding the only interesting file.
    """
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT,
                         capture_output=True, text=True, encoding="utf-8",
                         check=True)
    rows: list[tuple[str, str]] = []
    missing: list[str] = []
    for rel in out.stdout.split("\0"):
        if not rel:
            continue
        path = ROOT / rel
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, IsADirectoryError):
            continue  # binary, or a submodule directory
        except FileNotFoundError:
            if path.is_symlink():
                continue  # a symlink pointing nowhere is tracked but unreadable
            missing.append(rel)  # a tracked file absent under ROOT: list and tree disagree
            continue
        rows.append((rel, text))
    if missing:
        print(f"FAIL [gate {self_id()}]: {len(missing)} tracked file(s) listed by git but absent under "
              f"{ROOT}: {missing[:3]}{' ...' if len(missing) > 3 else ''}. The file list "
              "and the tree being scanned are not the same repository.")
        raise SystemExit(1)
    return rows


def scan(rows: list[tuple[str, str]]) -> list[tuple[str, str, int]]:
    """(where, what, lineno) for every violation found: the 1-based line on
    which the match begins.

    NEVER the matched text (desk PX). A CI log on a public repository is
    public, and a caller that never receives the text cannot republish it.
    Three fields, because the callers unpack three."""
    bad = []
    for sha, body in rows:
        for pattern, what in FORBIDDEN:
            m = pattern.search(body)
            if m:
                # The trailer pattern's `^\s*` can take the line break before
                # the key with it; the line is the one the key is on.
                start = m.start() + len(m.group(0)) - len(m.group(0).lstrip())
                bad.append((sha, what, body.count("\n", 0, start) + 1))
    return bad


def self_id() -> str:
    """This file's own content hash, printed in every verdict (desk ML, row D
    census #10). The sibling gates name the bytes that printed each verdict;
    this one did not, so a CI log could not say WHICH copy of it ran."""
    try:
        return hashlib.sha256(
            pathlib.Path(__file__).read_bytes()).hexdigest()[:16]
    except OSError:
        return "unreadable"


def self_test() -> int:
    """Prove the gate FAILS on an empty scan and on a planted violation, in
    that order, before trusting any green it reports."""
    failures = []

    # 1. THE EMPTY SET, FIRST. A scan with nothing in it must not read as clean.
    if scan([]) != []:
        failures.append("scan([]) should find nothing to report")
    #    ...and the caller must refuse it. That is the fail-closed contract.
    if not _is_empty_scan_fatal([]):
        failures.append("an empty commit set must be FATAL, not green")

    # 2. A planted violation of each shape must be caught.
    # One shape each, so the count is unambiguous. (The first draft planted a
    # message carrying BOTH and asserted 2; it found 3, because a trailer whose
    # value is a URL is legitimately two findings. The self-test caught the
    # ASSERTION, not the gate -- kept as written because a reader will
    # otherwise make the same arithmetic slip.)
    planted_trailer = [("aaa1", f"Subject\n\n{_SESSION_KEY}: session_x\n")]
    # ASSEMBLED, not written literally — the same trick FORBIDDEN itself uses,
    # and for a sharper reason since 2026-08-05: this gate now scans FILE
    # CONTENTS, and its first run caught THIS LINE, which used to carry the URL
    # verbatim. A detector's test data contains the thing it detects, so a
    # detector that also scans files must never spell its own fixture out.
    planted_url = [("aaa2", "Subject\n\nSee https://" + _HOST.replace(chr(92), "")
                    + "/code/session_abc\n")]
    if len(scan(planted_trailer)) != 1:
        failures.append(f"trailer shape must be caught, got {len(scan(planted_trailer))}")
    if len(scan(planted_url)) != 1:
        failures.append(f"URL shape must be caught, got {len(scan(planted_url))}")
    if len(scan(planted_trailer + planted_url)) != 2:
        failures.append("both shapes together must yield two findings")

    # 3. A clean message, INCLUDING the attribution the scrub kept, must pass.
    clean = [("bbb1", f"Subject\n\nBody.\n\n{PRESERVED}: Claude <noreply@anthropic.com>\n")]
    if scan(clean):
        failures.append(f"{PRESERVED} must not be treated as forbidden")

    # 4. The gate must not fire on a message that merely NAMES the rule, or the
    #    commit adding this gate could not describe what it does.
    meta = [("ccc1", "Subject\n\nThis gate forbids session-URL trailers.\n")]
    if scan(meta):
        failures.append("a message describing the rule must not trip it")

    # 5. THE SCAN MUST NOT DEPEND ON THE CALLER'S CWD. Hand-run from another
    #    repository, `git ls-files` used to list THAT repo's files while the
    #    contents were read from ROOT -- names that did not exist under ROOT were
    #    skipped as "binary", and the gate printed a confident green about the
    #    wrong repository (silicon, 2026-08-27, driven in a throwaway repo).
    import os, tempfile
    here = os.getcwd()
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
        foreign = "FOREIGN-FILE-THAT-ROOT-DOES-NOT-HAVE.txt"
        pathlib.Path(tmp, foreign).write_text("nothing\n", encoding="utf-8")
        subprocess.run(["git", "add", foreign], cwd=tmp, check=True)
        try:
            os.chdir(tmp)
            from_foreign = tracked_files()
        finally:
            os.chdir(here)
    from_root = tracked_files()
    if len(from_foreign) != len(from_root):
        failures.append("tracked_files() must not depend on cwd: "
                        f"{len(from_foreign)} from a foreign repo vs {len(from_root)} from ROOT")
    if any(rel == foreign for rel, _ in from_foreign):
        failures.append("a foreign repo's file list leaked into the scan")

    # THE SELF-ID. A verdict that does not name its instrument cannot be tied
    # to a copy; the id must be a real content hash, never the fallback.
    if not re.fullmatch(r"[0-9a-f]{16}", self_id()):
        failures.append("self_id() must be this file's 16-hex content hash")

    # 6. A FINDING NAMES ITS SITE AND LINE AND NEVER ITS TEXT (desk PX). A CI
    #    log on this repository is public. The scan returns a line number in
    #    place of the text, and main() prints the site, the kind and the line.
    #    Driven through main(). The arm rebinds ROOT and sys.argv, and their
    #    restore is ASSERTED, because the pre-push hook imports this module.
    root_before, argv_before = ROOT, list(sys.argv)
    failures.extend(_withholds_arm())
    if ROOT != root_before or sys.argv != argv_before:
        failures.append("arm 6 did not restore ROOT and sys.argv")

    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    if failures:
        return 1
    print(f"check_commit_trailers SELF-TEST [gate {self_id()}]: OK "
          "(empty scan fatal proven FIRST, both forbidden shapes caught, "
          f"{PRESERVED} preserved, self-describing message safe, cwd-independent, "
          "findings give their site and line and never their text)")
    return 0


def _withholds_arm() -> list[str]:
    """Arm 6. The scan first: its third field is a line number and no field
    carries the text. Then main() against two scratch repos, one with a session
    trailer in a commit message and one with a session URL in a tracked file.
    A planted payload must not reach the output; the sha or path, the kind
    and the line must.

    The trailer carries a URL, as the harness writes it. The trailer pattern
    alone matches only the key, so it is the URL beside it that carries the
    text.
    """
    import contextlib
    import io
    import tempfile
    global ROOT
    found = []
    secret = "zz_withheld_" + "payload"
    url = "https://" + _HOST.replace(chr(92), "") + "/code/" + secret
    trailer = f"subject\n\n{_SESSION_KEY}: {url}\n"

    rows = scan([("w", trailer)])
    if len(rows) != 2 or any(r[2] != 3 for r in rows):
        found.append(f"arm 6: scan must return line 3 for both findings, got "
                     f"{[r[2] if isinstance(r[2], int) else type(r[2]).__name__ for r in rows]}")
    if any(secret in str(field) for r in rows for field in r):
        found.append("arm 6: scan returned the matched text")

    cases = [  # (name, files, message, site, line)
        ("a trailer in a message", {"a.txt": "clean\n"}, trailer, None, 3),
        # The path is nested and longer than twelve characters, so a print
        # that shortened it (to the sha's width, or to its basename) is caught.
        ("a URL in a file", {"sub/planted-path-longer-than-twelve.txt": url + "\n"}, "clean", "sub/planted-path-longer-than-twelve.txt", 1),
    ]
    saved_root, saved_argv = ROOT, sys.argv
    try:
        with tempfile.TemporaryDirectory() as tmp:
            for i, (name, files, message, site, lineno) in enumerate(cases):
                repo = pathlib.Path(tmp, str(i))
                repo.mkdir()
                subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
                for rel, text in files.items():
                    (repo / rel).parent.mkdir(parents=True, exist_ok=True)
                    (repo / rel).write_text(text, encoding="utf-8", newline="\n")
                subprocess.run(["git", "add", "--", *files], cwd=repo, check=True)
                subprocess.run(["git", "-c", "user.email=self@test", "-c", "user.name=self",
                                "-c", "commit.gpgsign=false", "commit", "-q", "--no-verify",
                                "-m", message], cwd=repo, check=True)
                head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                                      capture_output=True, text=True, encoding="utf-8",
                                      check=True).stdout.strip()
                ROOT = repo
                sys.argv = [saved_argv[0]]
                said = io.StringIO()
                with contextlib.redirect_stdout(said):
                    try:
                        rc = main()
                    except SystemExit as e:
                        rc = e.code
                out = said.getvalue()
                if rc != 1:
                    found.append(f"arm 6, {name}: exit {rc}, want 1")
                if secret in out:
                    found.append(f"arm 6, {name}: the matched text reached the output")
                if f"  {site or head[:12]}  " not in out:
                    found.append(f"arm 6, {name}: the finding does not name its site")
                if f"(line {lineno}; {WITHHELD})" not in out:
                    found.append(f"arm 6, {name}: the finding does not give line {lineno}")
    finally:
        ROOT, sys.argv = saved_root, saved_argv
    return found


def _is_empty_scan_fatal(rows) -> bool:
    """The fail-closed rule, as a function so the self-test can prove it."""
    return len(rows) == 0


def is_shallow() -> bool:
    """A shallow clone would let this gate scan ONE commit and call it clean.

    `actions/checkout@v4` defaults to `fetch-depth: 1`. A history gate run
    against a one-commit clone is the decorative instrument this repository
    keeps finding: green, cheap, and measuring almost nothing. The CI step
    therefore sets `fetch-depth: 0`, and this refuses to run without it rather
    than trusting the workflow to stay correct.
    """
    out = subprocess.run(["git", "rev-parse", "--is-shallow-repository"], cwd=ROOT,
                         capture_output=True, text=True, encoding="utf-8")
    return out.stdout.strip() == "true"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--range", default="HEAD",
                    help="git revision range to scan (default: all of HEAD)")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if is_shallow():
        print(f"FAIL [gate {self_id()}]: this is a SHALLOW clone, so history is not all here and a "
              "clean result would be meaningless.\n"
              "      A history gate on a one-commit checkout scans one commit "
              "and reports success.\n"
              "      CI must check out with `fetch-depth: 0` for this job.")
        return 1

    try:
        rows = commit_messages(args.range)
    except subprocess.CalledProcessError as e:
        print(f"FAIL [gate {self_id()}]: could not read history for '{args.range}': {e}")
        return 1

    # FAIL CLOSED: nothing scanned is not the same as nothing wrong.
    if _is_empty_scan_fatal(rows):
        print(f"FAIL [gate {self_id()}]: scanned ZERO commits for '{args.range}'. An empty scan is "
              f"not a clean scan — this gate refuses to report success on it.")
        return 1

    bad = scan(rows)
    if bad:
        print(f"FAIL [gate {self_id()}]: {len(bad)} commit message(s) carry a forbidden trailer.\n")
        print("This repository's public history was rewritten on 2026-07-22 to")
        print("remove exactly this. A commit that reaches a published branch")
        print("cannot be edited without breaking every clone, so this must be")
        print("fixed BEFORE the merge, by rewriting the offending messages.\n")
        # The site and the line, never the text (desk PX).
        for sha, what, lineno in bad:
            print(f"  {sha[:12]}  {what}  (line {lineno}; {WITHHELD})")
        print(f"\nTo repair an unpushed range:  git rebase -i --exec "
              f"'git commit --amend --no-edit' <base>")
        print("For a pushed feature branch, rewrite and force-push THAT branch "
              "before merging — never after.")
        return 1

    # SECOND SUBJECT, added 2026-08-05: the FILE CONTENTS. A forbidden string
    # in a tracked file ships to a public repo exactly as surely as one in a
    # commit message, and the message scan above is structurally blind to it.
    # The windows seat found a real session URL in his hook's proof script, as
    # test data, and caught it BY EYE.
    files = tracked_files()
    if not files:
        print(f"FAIL [gate {self_id()}]: scanned ZERO tracked files. An empty scan is a failure, "
              "not a pass — the ls-files call or the decode filter has drifted.")
        return 1
    bad_files = scan(files)
    if bad_files:
        print(f"FAIL [gate {self_id()}]: {len(bad_files)} tracked file(s) carry a forbidden string.\n")
        print("Unlike a commit message this is trivially fixable — edit the file")
        print("— but only BEFORE it is pushed. This repository is public.\n")
        for path, what, lineno in bad_files:
            print(f"  {path}  {what}  (line {lineno}; {WITHHELD})")
        return 1

    print(f"check_commit_trailers [gate {self_id()}]: OK ({len(rows)} commit messages and "
          f"{len(files)} tracked files scanned, 0 forbidden strings; "
          f"{PRESERVED} attribution untouched)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
