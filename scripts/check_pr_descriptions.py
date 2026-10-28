#!/usr/bin/env python3
"""PR titles and bodies are not git objects. Nothing scanned them.

WHY THIS EXISTS (desk row I(a), commissioned from a sibling seat's audit)
-------------------------------------------------------------------------
The firewall gate beside this file scans commit messages, added lines, the
whole tree, and all of message history — four arms over GIT OBJECTS. A pull
request's TITLE and BODY are none of those: they live only in the forge's
database, they are the prose a reader actually sees first on the public repo
page, and they are EDITABLE FOREVER. The most-read public prose surface was
the one surface no arm covered. Measured before this shipped: one PR body in
this fleet carried a private-record path for five days (found 08/30) while
every git-object arm stayed green, because no git object ever contained it.

THE FOURTH DOOR (same audit, item (f)): a push to the BASE branch fires no
run for the PRs that target it, so a PR can sit green and MERGEABLE while
every one of its verdicts is about a base that no longer exists. Status is a
claim about a PAIR of refs at a moment; the pair moves and the status does
not. So this arm never reads status alone — it re-reads the REFS on every
run and says which object each verdict is actually about (REF-vs-RUN).

WHY IT RUNS FROM THE PUSH WORKFLOW AND NOT A pull_request TRIGGER: the
pull_request event fires on the PR's OWN pushes; it does not fire when the
base moves, and it does not fire when someone EDITS a description after the
checks are green. A push-triggered sweep of ALL open PRs re-reads everything
the forge currently says, every time anything lands — the only cadence that
closes both doors. (The event payload is deliberately never read: a
schedule-triggered run has none, and a guard scoped wider than its event set
fails open — measured in this fleet, 08/30.)

THE SESSION ARM (desk MC, 2026-09-14): a chat-session URL reached a public
PR body and every arm here was green, because this gate read private-record
PATHS and nothing else. The harness that opens PRs instructs every description
to END with its session URL, so every seat that opens a PR meets this. The
commit-trailer gate already owned the session shapes for commit messages; the
same list now reads PR titles and bodies, and a finding names the PR and the
surface but NEVER echoes the matched text, because a CI log on a public repo is
public too.

THE EDITED DOOR (desks SN and WB, 2026-09-21): this check became a REQUIRED
status check on the default branch, so a red one now BLOCKS the merge. The
remedy for forge-side prose is an EDIT on the forge, and an edit is not a
push: `pull_request` defaults to opened/synchronize/reopened, so the fix that
cleared the finding fired no run and its author sat blocked after doing
exactly what this gate told them to. The workflow now lists `edited`, and the
remedy printed below is DERIVED FROM THE WORKFLOW'S BYTES (edited_trigger_armed)
rather than asserted -- it promises a re-run only where the trigger says so,
and the self-test reds if this repository's trigger drops it.

SHAPES: imported from the sibling gate, never re-typed. A fixture is a
snapshot of a vocabulary; a copied pattern list is a stale fixture the day
the sibling moves. One list, one owner, two readers.

THE SUBJECT ARM (desk QA, 2026-09-16): the owner ruled eleven public commit
SUBJECTS -- nine carrying an employer-lane or private project name, two
carrying a family reference -- ACCEPTED AS DECLARED DEBT rather than
rewritten, and commissioned a gate so that no NEW subject or PR title carries
either class. Every one of the nine was written by a commit that was adding
that very name to the sibling gate, whose source is assembled from parts so it
never spells it: the artifact was hardened and the metadata that delivered it
was not. None of the three scrub gates read a subject for a bare word.
  * LANE NAMES are the sibling's own lists, IMPORTED (its ROOTS_DIGEST is
    printed on every PASS line, so each repo's CI log shows which list it
    ran), minus the one personal-lane campaign the ruling scoped out. They
    are refused in commit subjects, PR titles, PR head refs (a merge subject
    quotes the ref), PR bodies, and -- FORWARD ONLY -- commit bodies. The
    commit bodies already public are history this gate does not touch, and
    FORWARD-ONLY IS A PROPERTY OF THE RANGE THE CALLER PASSES: a range that
    lists an already-public commit whose body carries a word reds on it (the
    baseline accepts subjects, never bodies), so a caller passes only the
    commits a push adds. --history reads subjects alone for the same reason.
  * FAMILY REFERENCES are refused in subjects, titles and refs only: a body
    uses these words as code identifiers (a `kids(_:_:)` function) and
    `family` is a technical word here (76 public subjects use it that way).
  * NOT COVERED, by construction: third-party personal names. A word list
    cannot tell a citation of published work from social context, and the
    same people appear in both, so it would refuse a citation. Every PASS
    line says so.
A finding names the commit or PR, the surface and the CLASS -- never the word.
(Measured 2026-09-16 over 10,613 default-branch commits in six public repos:
76 subjects use `family` technically, and the nine lane subjects found by word
pieces agree with an independent census that used literal needles.)
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import hashlib
import html
import io
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unicodedata

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_private_paths as gate  # noqa: E402  (the pattern owner)
import check_commit_trailers as trailers  # noqa: E402  (the session-shape owner)
try:  # the infra-name gate is a sibling in the repos that carry it; a repo without it is DECLARED in the OK line, never skipped silently
    import check_infra_names as infra  # noqa: E402  (the infra-name owner)
except ImportError:
    infra = None


def self_id() -> str:
    try:
        return hashlib.sha256(
            pathlib.Path(__file__).read_bytes()).hexdigest()[:16]
    except OSError:
        return "unreadable"


def scan_description(number, title: str, body: str):
    """Findings for one PR's forge-side prose, via the sibling gate's scan."""
    rows = [(f"PR #{number} TITLE", title or ""),
            (f"PR #{number} BODY", body or "")]
    return gate.scan(rows)


def scan_session(number, title: str, body: str):
    """Chat-session trailers and URLs in one PR's forge-side prose, via the
    commit-trailer gate's FORBIDDEN list (desk MC). Imported, never re-typed."""
    rows = [(f"PR #{number} TITLE", title or ""),
            (f"PR #{number} BODY", body or "")]
    return trailers.scan(rows)


_HTML_COMMENT = re.compile(r"<!--.*?(?:-->|\Z)", re.S)   # unclosed: to the end, as the forge hides it; linear (kent R1)
_EMPHASIS = str.maketrans("", "", "*_~`")


def rendered_text(s: str) -> str:
    """What the forge SHOWS, near enough to match a name in (the helm's commission of 2026-10-18, on systems' G2):
    drop HTML comments (keeping their newlines, so line numbers survive), html.unescape, NFKC, drop Unicode Cf
    (zero-widths, soft hyphen, bidi), drop the markdown emphasis characters * _ ~ `. NOT a renderer: look-alike
    letters from other scripts are not folded, and that is declared in the OK line."""
    s = _HTML_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), s or "")
    s = unicodedata.normalize("NFKC", html.unescape(s))
    return "".join(c for c in s if unicodedata.category(c) != "Cf").translate(_EMPHASIS)


def scan_infra(number, title: str, body: str):
    """Infrastructure names (a host, an account) in one PR's forge-side prose, via the
    infra-name gate's FORBIDDEN list (imported, never re-typed; the helm's order of
    2026-10-18 after a box host name sat in six public PR bodies). Returns
    [(where, line_number)] and NEVER the matched text: this log is public too.
    A repo with no check_infra_names.py returns [] and says so in the OK line."""
    if infra is None:
        return []
    rows = [(f"PR #{number} TITLE", title or ""),
            (f"PR #{number} BODY", body or "")]
    # the SOURCE and its RENDERING both scanned; one finding per (surface, line)
    hits = {(rel, i) for rel, i, _text in infra.scan(rows)}
    hits |= {(rel, i) for rel, i, _text in infra.scan([(rel, rendered_text(s)) for rel, s in rows])}
    order = {rel: k for k, (rel, _s) in enumerate(rows)}
    return sorted(hits, key=lambda h: (order[h[0]], h[1]))


def infra_finding_lines(rows) -> list[str]:
    """Name the PR, the surface and the line number, NEVER the matched text."""
    label = getattr(infra, "_FINDING_LABEL", "an infrastructure name")
    return [f"  {where}, line {i}: {label}" for where, i in rows]


def session_finding_lines(rows) -> list[str]:
    """Name the PR, the surface and the shape, NEVER the matched text: echoing
    a session URL into a public CI log would republish it."""
    return [f"  {where}: {what}" for where, what, _line in rows]


# ---------------------------------------------------------------------------
# THE SUBJECT ARM (desk QA) -- see the module docstring for the ruling.
# ---------------------------------------------------------------------------

# Relations that name a family member. Plain words: they are generic, and no
# gate scans a tree for them, so spelling them discloses nothing.
# ⛔ DELIBERATELY ABSENT, each measured as a technical word in these repos:
# family/families (76 public subjects), parent(s)/child(ren) (the document
# tree), kid(s) (a Swift function), baby. A word that refuses real engineering
# subjects trains its readers to reword past the gate.
_KIN = ("wife", "wives", "husband", "husbands", "spouse", "spouses",
        "daughter", "daughters", "son", "sons", "mom", "moms", "mum", "dad",
        "dads", "mother", "mothers", "father", "fathers", "sister", "sisters",
        "brother", "brothers", "grandmother", "grandfather", "grandma",
        "grandpa", "grandson", "granddaughter", "nephew", "niece", "uncle",
        "aunt", "cousin", "fiance", "fiancee", "girlfriend", "boyfriend",
        "stepson", "stepdaughter")

# The personal-lane campaign the ruling scoped OUT of the lane class (its
# public mentions were left untouched on purpose). Assembled from parts, as the
# sibling assembles it.
_LANE_EXCLUDED = ("ver" + "so",)

LANE = "an employer-lane or private project name"
KIN = "a family reference"

SUBJECT_BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "subject_debt_baseline.tsv")

_SCISSORS = "# ------------------------ >8 ------------------------"


def _pieces(text) -> list[str]:
    """Lower-case word pieces: any run of letters and digits. Every separator
    (`_ - / .` and space) splits, so a multi-piece name matches however it is
    joined, and a whole-word test is a piece comparison, never a substring
    (the employer word inside `local` is not the employer word)."""
    return re.findall(r"[a-z0-9]+", (text or "").lower())


def lane_words() -> list[str]:
    """The sibling's employer-lane and private-project lists, IMPORTED, minus
    the scoped-out campaign. One list, one owner (ruled at desk QA, fork 1)."""
    return [w for w in list(gate._EMPLOYER) + list(gate._PRIVATE_PROJ)
            if w not in _LANE_EXCLUDED]


def _shapes(words) -> set[tuple[str, ...]]:
    """Piece tuples to look for. A multi-piece word is also looked for as its
    pieces run together, the one joining the piece split cannot see."""
    out = set()
    for w in words:
        p = tuple(_pieces(w))
        if not p:
            raise ValueError("a vocabulary entry with no word pieces can never match")
        out.add(p)
        if len(p) > 1:
            out.add(("".join(p),))
    return out


def _hit(pieces: list[str], shapes) -> bool:
    for s in shapes:
        n = len(s)
        if any(tuple(pieces[i:i + n]) == s for i in range(len(pieces) - n + 1)):
            return True
    return False


def subject_scan(rows) -> list[tuple[str, str]]:
    """(where, class) for each (where, text, kind) row. kind is `subject` (both
    classes) or `body` (lane names only). NEVER returns the text."""
    lane, kin = _shapes(lane_words()), _shapes(_KIN)
    bad = []
    for where, text, kind in rows:
        if kind not in ("subject", "body"):
            raise ValueError(f"unknown surface kind {kind!r}")
        p = _pieces(text)
        if _hit(p, lane):
            bad.append((where, LANE))
        if kind == "subject" and _hit(p, kin):
            bad.append((where, KIN))
    return bad


def subject_finding_lines(rows) -> list[str]:
    return [f"  {where}: {what}" for where, what in rows]


def pr_rows(pr) -> list[tuple[str, str, str]]:
    """A PR's three forge-side surfaces. The head ref is subject-class: a
    merge commit's subject quotes it."""
    n = pr.get("number")
    return [(f"PR #{n} TITLE", pr.get("title") or "", "subject"),
            (f"PR #{n} HEAD REF", (pr.get("head") or {}).get("ref") or "", "subject"),
            (f"PR #{n} BODY", pr.get("body") or "", "body")]


def message_rows(text, where: str = "the message") -> list[tuple[str, str, str]]:
    """A commit-message FILE as git will store it under the default cleanup:
    `#` lines dropped, everything below the scissors line dropped, and the
    subject is the first paragraph joined by spaces (what `%s` prints)."""
    lines = []
    for line in (text or "").splitlines():
        if line.startswith(_SCISSORS):
            break
        if not line.startswith("#"):
            lines.append(line)
    while lines and not lines[0].strip():
        lines.pop(0)
    subject = []
    while lines and lines[0].strip():
        subject.append(lines.pop(0).strip())
    return [(f"{where} SUBJECT", " ".join(subject), "subject"),
            (f"{where} BODY", "\n".join(lines), "body")]


def _git(args: list[str], cwd=None) -> str:
    out = subprocess.run(["git"] + (["-C", cwd] if cwd else []) + args,
                         capture_output=True, text=True, encoding="utf-8",
                         errors="replace")
    if out.returncode != 0:
        raise RuntimeError(f"git {args[0]} exit {out.returncode}: "
                           f"{out.stderr.strip()[:200]}")
    return out.stdout


def commits(rev: str, cwd=None) -> list[tuple[str, str, str]]:
    """(sha, subject, body) for every commit `git log <rev>` lists, merges
    included: a merge subject quotes the branch name."""
    raw = _git(["log", "--format=%H%x1f%s%x1f%b%x1e", rev], cwd)
    out = []
    for rec in raw.split("\x1e"):
        rec = rec.strip("\n")
        if rec:
            sha, subject, body = (rec.split("\x1f") + ["", ""])[:3]
            out.append((sha, subject, body))
    return out


def commit_rows(recs, baseline=frozenset()) -> list[tuple[str, str, str]]:
    """Scan rows for commits. A subject whose (sha, digest) is in the accepted
    baseline is skipped; its BODY never is, because the ruling accepted
    subjects and nothing else."""
    rows = []
    for sha, subject, body in recs:
        if subject_key(sha, subject) not in baseline:
            rows.append((f"commit {sha[:12]} SUBJECT", subject, "subject"))
        rows.append((f"commit {sha[:12]} BODY", body, "body"))
    return rows


def subject_key(sha: str, subject: str) -> tuple[str, str]:
    """The baseline's identity for one accepted subject. The subject itself is
    never stored: a baseline that spelled it would republish it."""
    return (sha, hashlib.sha256(subject.encode("utf-8")).hexdigest()[:16])


def load_subject_baseline(path: str) -> set[tuple[str, str]]:
    """The accepted-debt keys. A MISSING file raises FileNotFoundError and a
    malformed line raises ValueError: a missing baseline is no statement, an
    EMPTY one (comments only) is the statement that nothing is accepted, and a
    line the reader cannot parse is never a line it may skip."""
    keys = set()
    with open(path, encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip() or line.startswith("#"):
                continue
            f = line.rstrip("\n").split("\t")
            if (len(f) < 2 or not re.fullmatch(r"[0-9a-f]{40}", f[0])
                    or not re.fullmatch(r"[0-9a-f]{16}", f[1])):
                raise ValueError(f"{os.path.basename(path)} line {n} is not "
                                 f"<sha40><TAB><digest16>")
            keys.add((f[0], f[1]))
    return keys


def _shallow(cwd=None) -> bool:
    return _git(["rev-parse", "--is-shallow-repository"], cwd).strip() == "true"


def history_verdict(baseline, cwd=None):
    """(new, stale, refound, scanned) over every SUBJECT reachable from HEAD.
    Subjects only: the owner accepted subjects, and the commit bodies already
    public are history this gate does not rule on."""
    recs = commits("HEAD", cwd)
    found = set()
    for sha, subject, _body in recs:
        if subject_scan([("s", subject, "subject")]):
            found.add(subject_key(sha, subject))
    return (sorted(found - baseline), sorted(baseline - found),
            sorted(found & baseline), len(recs))


_NOT_COVERED = ("NOT COVERED: third-party personal names (a word list cannot "
                "tell a citation from social context); family references in "
                "bodies; the scoped-out personal-lane campaign; commit bodies "
                "already public (this arm is forward-only).")


def _vocab_id() -> str:
    return (f"lane words {len(lane_words())} from [roots {gate.ROOTS_DIGEST}], "
            f"family words {len(_KIN)}")


def _debt_remedy() -> None:
    print("\nA pushed commit subject cannot be edited without a history rewrite,")
    print("so reword it BEFORE it is pushed: name a lane or a project by ROLE")
    print("(an employer-lane root, a private project) and a person by ROLE,")
    print("never by name or relation.")


def range_mode(rev: str, cwd=None, baseline_path=None) -> int:
    """Every commit in `git log <rev>`: subjects for both classes, bodies for
    lane names (forward only). A baselined subject is accepted, not new."""
    tag = f"[pr-gate {self_id()}]"
    try:
        baseline = load_subject_baseline(baseline_path or SUBJECT_BASELINE)
        recs = commits(rev, cwd)
    except (OSError, ValueError, RuntimeError) as e:
        print(f"FAIL {tag}: --range {rev} could not run: {e}\n"
              "      A scan that could not look is not a clean scan.")
        return 1
    if not recs:
        print(f"FAIL {tag}: --range {rev} lists NO commit. A scan that read "
              "nothing is not a clean scan; the range is wrong.")
        return 1
    bad = subject_scan(commit_rows(recs, baseline))
    accepted = sum(1 for sha, subject, _ in recs
                   if subject_key(sha, subject) in baseline)
    if bad:
        print(f"FAIL {tag}: {len(bad)} finding(s) in {len(recs)} commit(s) of "
              f"{rev} (the word is withheld: this log is public).\n")
        print("\n".join(subject_finding_lines(bad)))
        _debt_remedy()
        return 1
    print(f"check_pr_descriptions --range {rev} {tag}: OK -- {len(recs)} "
          f"commit(s), 0 findings in subjects and bodies, {accepted} accepted-debt "
          f"subject(s) skipped by the baseline. {_vocab_id()}.")
    print(_NOT_COVERED)
    return 0


def history_mode(cwd=None, baseline_path=None) -> int:
    """Every subject reachable from HEAD against the accepted-debt baseline,
    in both directions: new debt reds, and so does an entry no longer found
    (a vocabulary that lost a word, or a history that was rewritten)."""
    tag = f"[pr-gate {self_id()}]"
    path = baseline_path or SUBJECT_BASELINE
    try:
        if _shallow(cwd):
            print(f"FAIL {tag}: --history on a SHALLOW clone: the commits it "
                  "cannot see are exactly the ones it must. Fetch full depth.")
            return 1
        baseline = load_subject_baseline(path)
        new, stale, refound, n = history_verdict(baseline, cwd)
    except FileNotFoundError:
        print(f"FAIL {tag}: no baseline at {os.path.basename(path)}. A missing "
              "baseline is no statement; one holding only comments says that "
              "nothing is accepted.")
        return 1
    except (OSError, ValueError, RuntimeError) as e:
        print(f"FAIL {tag}: --history could not run: {e}")
        return 1
    # No `n == 0` guard: a HEAD that resolves has at least one commit, and a
    # repository with none fails in `git log` above (the self-test drives it).
    if new:
        print(f"FAIL {tag}: {len(new)} commit subject(s) carry a refused word "
              "and are NOT in the accepted-debt baseline:\n")
        for sha, digest in new:
            print(f"  {sha}\t{digest}")
        print("\nOnly the owner accepts debt. If accepted, the lines above are the")
        print("baseline rows; otherwise the commit must not reach a public branch.")
    if stale:
        print(f"FAIL {tag}: {len(stale)} baseline row(s) are NO LONGER FOUND in "
              "history -- the vocabulary lost a word, or history was rewritten:\n")
        for sha, digest in stale:
            print(f"  {sha}\t{digest}")
    if new or stale:
        return 1
    control = (f"{len(refound)} accepted subject(s) re-found, which is this "
               "repository's real-bytes control" if refound else
               "0 accepted subjects, so this repository has NO real-bytes "
               "control; only the self-test's planted commits witness the matcher")
    print(f"check_pr_descriptions --history {tag}: OK -- {n} commit subject(s), "
          f"0 new, 0 stale; {control}. {_vocab_id()}.")
    print(_NOT_COVERED)
    return 0


def msg_file_mode(path: str) -> int:
    """One commit-message file, as the commit-msg hook hands it over."""
    tag = f"[pr-gate {self_id()}]"
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except OSError as e:
        print(f"REFUSED {tag}: cannot read the message file: {e}")
        return 1
    bad = subject_scan(message_rows(text))
    if bad:
        print(f"REFUSED {tag}: this commit message carries a refused word "
              "(withheld).\n")
        print("\n".join(subject_finding_lines(bad)))
        _debt_remedy()
        return 1
    # The session arm too (2026-09-27): this mode is also used as a receipt for
    # a PR's title and body, and until today it ran the subject arm alone while
    # its OK line claimed "body clean" -- a planted session URL passed it.
    subject, _, body = text.partition("\n")
    sess = [(f"MESSAGE {w.split(' ', 2)[-1]}", what, ln)
            for w, what, ln in scan_session(0, subject, body)]
    if sess:
        print(f"REFUSED {tag}: this message carries a chat-session trailer or URL "
              "(withheld).\n")
        print("\n".join(session_finding_lines(sess)))
        return 1
    print(f"check_pr_descriptions --msg-file {tag}: OK -- subject words and "
          "session shapes clean (subject arm + session arm).")
    return 0


def ref_mode(name: str) -> int:
    """One ref name: a branch a push creates, or a PR's head. Subject-class,
    because a merge commit's subject quotes it and the forge writes that
    subject where no local hook runs (two of the eleven accepted subjects are
    exactly that). The finding never echoes the name."""
    tag = f"[pr-gate {self_id()}]"
    if not (name or "").strip():
        print(f"FAIL {tag}: --ref was given an EMPTY name. A check that read "
              "nothing is not a clean check.")
        return 1
    bad = subject_scan([("the ref name", name, "subject")])
    if bad:
        print(f"REFUSED {tag}: the ref name carries a refused word (withheld).\n")
        print("\n".join(subject_finding_lines(bad)))
        print("\nA merge commit's subject will quote this name, and the forge writes")
        print("that subject where no hook runs. Push the work under a neutral name.")
        return 1
    print(f"check_pr_descriptions --ref {tag}: OK -- the ref name carries no "
          f"refused word. {_vocab_id()}.")
    return 0


def ref_vs_run(head_sha: str, run_sha, run_green, behind_by, live_clean=None) -> str:
    """One line saying WHICH OBJECT the PR's verdict is about. Pure, so the
    self-test drives every branch without a forge.

    Never a bare status: a status is a claim about a (head, base) pair at a
    moment, and only the refs say whether that moment is this one."""
    if run_sha is None:
        return "NO RUN on the current head — any green you see is about an OLDER head"
    if run_sha != head_sha:
        return (f"RUN-vs-REF MISMATCH — latest run is on {run_sha[:8]}, head is "
                f"{head_sha[:8]}: the verdict is about a DIFFERENT object")
    if run_green and isinstance(behind_by, int) and behind_by > 0:
        return (f"GREEN BUT STALE — head verdict is green, but the base has moved "
                f"{behind_by} commit(s) since (a base move fires no run): the green "
                f"is about a base that no longer exists")
    if not run_green:
        if live_clean is True:
            # desk SN rec (1), 2026-09-25: the run is pinned to an immutable sha but the prose it
            # judged is editable; when this gate finds NOTHING on the live forge and the recorded
            # run is still red, the reader is one re-run from green and the bare status hides it.
            return ("run on current head NOT green, and THIS GATE'S SURFACES READ CLEAN ON THE LIVE "
                    "FORGE — if the red is this gate's, it is FIXED ON THE FORGE, RUN STALE: re-run "
                    "the failed job to clear (the run judged prose that has since been edited)")
        return "run on current head NOT green"
    return "current — run is on this head and the base has not moved"


def _gh(args: list[str]):
    out = subprocess.run(["gh", "api"] + args, capture_output=True, text=True,
                         encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(out.stderr.strip()[:200])
    return json.loads(out.stdout)


_WORKFLOW = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                         ".github", "workflows", "scrub.yml")


_DEFAULT_TYPES = frozenset({"opened", "synchronize", "reopened"})
_REQUIRED_TYPES = _DEFAULT_TYPES | {"edited"}


def _no_comment(line: str) -> str:
    """A YAML comment is not configuration. None of the values read here can
    contain `#`, so everything from the first one is dropped."""
    return line.split("#", 1)[0]


def pull_request_types(path: str = _WORKFLOW):
    """The Scrub workflow's `pull_request` activity types, as a frozenset: the
    list it declares, or the Actions DEFAULTS when it declares none -- `types:`
    REPLACES the defaults, so the SET matters and not only one member. None when
    no such trigger can be read here: an unreadable workflow is not an unarmed
    one. READ FROM THE WORKFLOW'S BYTES, never asserted, and comments are
    dropped first (a non-author read found `# edited ...` reading as armed)."""
    try:
        with open(path, encoding="utf-8") as fh:
            lines = [_no_comment(l) for l in fh.read().splitlines()]
    except OSError:
        return None
    for i, line in enumerate(lines):
        if line.rstrip() != "  pull_request:":
            continue
        types, in_types = None, False
        for nxt in lines[i + 1:]:
            s = nxt.strip()
            if not s:
                continue
            if not nxt.startswith("    "):
                break  # the next trigger or a top-level key
            if in_types:
                if s.startswith("- "):
                    types.add(s[2:].strip().strip("'\""))
                    continue
                in_types = False
            if s.startswith("types:"):
                inline = s[len("types:"):].strip()
                types = set(re.findall(r"[a-z_]+", inline))
                in_types = not inline
        return frozenset(types) if types is not None else _DEFAULT_TYPES
    return None


def edited_trigger_armed(path: str = _WORKFLOW):
    """True when a PR title/body edit re-runs this check (the trigger lists
    `edited`), False when it does not, None when the trigger is unreadable.
    This is the question the REMEDY needs; the self-test asks the wider one."""
    types = pull_request_types(path)
    return None if types is None else "edited" in types


def rerun_note_lines(armed) -> list[str]:
    """What an author does about the RED once the prose is fixed. A title or
    body edit is not a push, so whether it re-runs this check is a property of
    the workflow's trigger, passed in as `armed`."""
    head = ["", "Where this check is REQUIRED for merge, a red one blocks it."]
    if armed is True:
        return head + [
            "Saving the edit on the forge fires a fresh Scrub run by itself (the",
            "workflow listens for `edited`). If none appears within a minute:",
            "  gh run rerun <run-id> --failed"]
    why = ("the workflow's pull_request types do not list `edited`"
           if armed is False else "the workflow could not be read from here")
    return head + [
        f"A title or body edit fires NO run here ({why}).",
        "After the edit, re-run the failed job:  gh run rerun <run-id> --failed",
        "Never push an empty commit to re-trigger it."]


def open_mode(repo: str) -> int:
    """Scan every OPEN PR's title+body; disclose REF-vs-RUN for each."""
    # desk SN rec (2), 2026-09-25: a CI check is NAMED after one of its N steps, so a red under a
    # job called after something else is read as that job's diagnosis. This first line makes the
    # log self-attributing: which STEP ran, which SURFACE it read, and that the surface is live.
    print(f"check_pr_descriptions --open [pr-gate {self_id()}]: STEP = this script's open mode · "
          f"SURFACE = the OPEN PRs' TITLES and BODIES on the forge, read LIVE at this run "
          f"(editable prose; no git object) · REPO = {repo}")
    try:
        prs = _gh([f"repos/{repo}/pulls?state=open&per_page=100"])
    except RuntimeError as e:
        print(f"FAIL [pr-gate {self_id()}]: could not list open PRs: {e}\n"
              "      An unreadable forge is not a clean forge.")
        return 1
    bad = []
    sess = []
    words = []
    infra_f = []
    notes = []
    for pr in prs:
        n = pr["number"]
        pr_bad = scan_description(n, pr.get("title"), pr.get("body"))
        pr_sess = scan_session(n, pr.get("title"), pr.get("body"))
        pr_infra = scan_infra(n, pr.get("title"), pr.get("body"))
        pr_words = subject_scan(pr_rows(pr))
        bad += pr_bad; sess += pr_sess; words += pr_words; infra_f += pr_infra
        live_clean = not (pr_bad or pr_sess or pr_words or pr_infra)   # desk SN rec (1): what this run READ
        head = pr["head"]["sha"]
        base_ref = pr["base"]["ref"]
        run_sha = run_green = None
        behind = None
        try:
            runs = _gh([f"repos/{repo}/commits/{head}/check-runs?per_page=50"])
            checks = runs.get("check_runs", [])
            if checks:
                run_sha = head
                run_green = all(c.get("conclusion") in ("success", "skipped", "neutral")
                                for c in checks if c.get("status") == "completed") \
                    and any(c.get("status") == "completed" for c in checks)
            cmp_ = _gh([f"repos/{repo}/compare/{head}...{base_ref}"])
            behind = cmp_.get("ahead_by")  # base commits the head has not seen
        except RuntimeError as e:
            notes.append(f"  PR #{n}: REF-vs-RUN unreadable ({e}) — reported, not assumed current")
            continue
        notes.append(f"  PR #{n} head {head[:8]} vs base {base_ref}: "
                     + ref_vs_run(head, run_sha, bool(run_green), behind, live_clean=live_clean))
    if bad:
        print(f"FAIL [pr-gate {self_id()}]: {len(bad)} private-record path(s) in "
              f"OPEN PR descriptions — the forge-side prose, not any git object.\n")
        print("\n".join(gate.finding_lines(bad)))
        print("\nA PR description is EDITABLE: rewrite the reference as a ROLE or a")
        print("bare filename directly on the forge. No push required.")
    if sess:
        print(f"FAIL [pr-gate {self_id()}]: {len(sess)} chat-session trailer/URL "
              f"finding(s) in OPEN PR descriptions (matched text withheld: this log "
              f"is public).\n")
        print("\n".join(session_finding_lines(sess)))
        print("\nThe PR-opening harness appends a session URL; this repository is")
        print("public. Delete that line on the forge. No push required.")
    if infra_f:
        print(f"FAIL [pr-gate {self_id()}]: {len(infra_f)} infrastructure name(s) (a host or an "
              f"account) in OPEN PR titles/bodies (matched text withheld: this log is public).\n")
        print("\n".join(infra_finding_lines(infra_f)))
        print("\nA title or body is EDITABLE on the forge: name the machine by ROLE (\"the Windows box\").")
        print("The forge keeps edit history on a public repo, so the earlier text stays readable there:")
        print("do not paste the name again.")
        print("This check reads EVERY open PR, so a red on a clean PR can come from ANOTHER PR\'s body: after that body is fixed,")
        print("re-run the failed job on the other PRs (an edit re-runs only the edited PR\'s own job).")
    if words:
        print(f"FAIL [pr-gate {self_id()}]: {len(words)} refused word(s) in OPEN PR "
              f"titles, head refs or bodies (withheld: this log is public).\n")
        print("\n".join(subject_finding_lines(words)))
        print("\nA title or body is EDITABLE on the forge: name the lane or the person")
        print("by ROLE. A head ref is not: its merge subject will quote it, so push")
        print("the branch under a neutral name and reopen.")
    if bad or sess or words or infra_f:
        print("\n".join(rerun_note_lines(edited_trigger_armed())))
        return 1
    print(f"check_pr_descriptions --open [pr-gate {self_id()}]: OK — {len(prs)} open "
          f"PR(s), 0 private-record paths and 0 session trailers/URLs in titles/bodies, "
          f"0 refused words in titles, head refs and bodies. {_vocab_id()}.")
    print("infra-name arm: " + ("0 infrastructure names (host or account) in open PR titles/bodies. NOT COVERED by this arm: "
          "look-alike letters from other scripts (confusables are not folded; the source AND its rendering are read: HTML comments, entities, Unicode Cf and * _ ~ ` dropped, then NFKC); "
          "PR and review comments; CLOSED or MERGED PR bodies; more than 100 open PRs (no paging)." if infra is not None
          else "NOT COVERED here: this repository carries no check_infra_names.py (declared, not skipped)."))
    print(_NOT_COVERED)
    if notes:
        print("REF-vs-RUN (which object each verdict is about; never status alone):")
        print("\n".join(notes))
    return 0


def _scratch_repo(spec):
    """A throwaway repository with one empty commit per (subject, body).
    Returns (dir, [sha, ...]). Hooks are pointed at an empty directory so a
    developer's own hooks cannot rewrite the planted messages."""
    d = tempfile.mkdtemp(prefix="pr-gate-selftest-")
    hooks = os.path.join(d, "no-hooks")
    os.mkdir(hooks)
    cfg = ["-c", "user.name=selftest", "-c", "user.email=selftest@example.invalid",
           "-c", "commit.gpgsign=false", "-c", "core.hooksPath=" + hooks]
    _git(["init", "-q"], d)
    shas = []
    for subject, body in spec:
        msg = subject + ("\n\n" + body if body else "")
        _git(cfg + ["commit", "-q", "--allow-empty", "--cleanup=verbatim",
                    "-m", msg], d)
        shas.append(_git(["rev-parse", "HEAD"], d).strip())
    return d, shas


def _quiet(fn, *args):
    """(return code, printed text) -- a mode's output is itself under test."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = fn(*args)
    return rc, buf.getvalue()


def _subject_arms() -> list[str]:
    """ARMS 6-11 (desk QA). A failure message names a vocabulary entry by its
    INDEX, never by its text: this output lands in a public CI log."""
    failures = []
    lane = lane_words()

    # ARM 6 -- the lane vocabulary is the sibling's, minus exactly the one
    # scoped-out word, and that word really is in the sibling (an exclusion of
    # a word the sibling no longer carries guards nothing and reads as a rule).
    if not lane:
        failures.append("the lane vocabulary must be non-empty (imported from the sibling)")
    sib = set(gate._EMPLOYER) | set(gate._PRIVATE_PROJ)
    if set(lane) != sib - set(_LANE_EXCLUDED):
        failures.append("the lane vocabulary must be the sibling's two lists minus the exclusion")
    if not set(_LANE_EXCLUDED) <= sib:
        failures.append("every excluded word must still be in the sibling's lists")

    # The tokenizer, by known answer: digits belong to a word, case does not,
    # every separator splits. (Mutation: a letters-only tokenizer SURVIVED
    # every arm below, because both sides of each comparison used it -- and it
    # would have matched a word whose digit differs.)
    if _pieces("Ab1-c2_D.e/3 f") != ["ab1", "c2", "d", "e", "3", "f"]:
        failures.append("_pieces must split on every separator and keep digits in a word")
    try:
        _shapes(["--"])
        failures.append("a vocabulary entry with no word pieces must be refused, not kept")
    except ValueError:
        pass

    # ARM 7 -- every lane word is caught in a SUBJECT and in a BODY, as the lane
    # class alone; whole words only; any separator, any case.
    for i, w in enumerate(lane):
        if [c for _, c in subject_scan([("s", "wip: tidy " + w + " notes", "subject")])] != [LANE]:
            failures.append(f"lane word #{i} must be caught in a SUBJECT, as the lane class only")
        if [c for _, c in subject_scan([("b", "x\n\nsee " + w + ".", "body")])] != [LANE]:
            failures.append(f"lane word #{i} must be caught in a BODY")
        if subject_scan([("s", w.upper() + " done", "subject")]) == []:
            failures.append(f"lane word #{i} must be caught in upper case")
        if len(_pieces(w)) == 1 and subject_scan(
                [("s", w + "x x" + w + " x" + w + "x", "subject")]):
            failures.append(f"lane word #{i} must match WHOLE words only")
    multi = [w for w in lane if len(_pieces(w)) > 1]
    if not multi:
        failures.append("the separator arm needs a multi-piece lane word and found none")
    for i, w in enumerate(multi):
        p = _pieces(w)
        for sep in ("_", "-", " ", "/", ""):
            if not subject_scan([("s", "add " + sep.join(p) + " root", "subject")]):
                failures.append(f"multi-piece lane word #{i} must be caught joined by {sep!r}")

    # ARM 8 -- a family reference is caught in a SUBJECT, as that class alone,
    # and NOT in a body; the measured technical words are not refused.
    for i, w in enumerate(_KIN):
        if [c for _, c in subject_scan([("s", "ratified (the " + w + " agreed)", "subject")])] != [KIN]:
            failures.append(f"kin word #{i} must be caught in a SUBJECT, as the kin class only")
        if subject_scan([("b", "x\n\nthe " + w + " agreed", "body")]):
            failures.append(f"kin word #{i} must NOT be refused in a BODY (code uses)")
    if not subject_scan([("s", "the " + _KIN[0] + "'s read pending", "subject")]):
        failures.append("a possessive family reference must be caught")
    for i, w in enumerate(("family", "families", "parent", "parents", "child",
                           "children", "kid", "kids", "baby") + _LANE_EXCLUDED):
        if subject_scan([("s", "the " + w + " arm", "subject"),
                         ("b", "the " + w + " arm", "body")]):
            failures.append(f"technical/excluded word #{i} must not be refused")
    try:
        subject_scan([("s", "x", "subjekt")])
        failures.append("an unknown surface kind must raise, never scan as nothing")
    except ValueError:
        pass

    # ARM 9 -- the surfaces: a finding keeps its location, the rendered lines
    # never trip the vocabulary (the word is never echoed), and each PR and
    # message surface carries the classes the ruling gives it.
    w0, k0 = (lane or ["x"])[0], _KIN[0]
    got = subject_scan([("PR #9 TITLE", "x " + w0, "subject"),
                        ("PR #9 TITLE", "x " + k0, "subject")])
    if sorted(got) != sorted([("PR #9 TITLE", LANE), ("PR #9 TITLE", KIN)]):
        failures.append("a finding must keep its location and its class")
    lines = subject_finding_lines(got)
    if len(lines) != 2 or subject_scan([("l", l, "subject") for l in lines]):
        failures.append("a rendered finding must never echo the word it found")
    ref = "helm/tidy-" + (multi or [w0])[0]
    cases = [
        ({"number": 4, "title": "clean", "head": {"ref": ref}, "body": "clean"},
         [("PR #4 HEAD REF", LANE)]),
        ({"number": 4, "title": "clean", "head": {"ref": "x"}, "body": "the " + k0},
         []),
        ({"number": 4, "title": "clean", "head": {"ref": "x"}, "body": "see " + w0},
         [("PR #4 BODY", LANE)]),
        ({"number": 4, "title": "the " + k0, "head": {"ref": "x"}, "body": ""},
         [("PR #4 TITLE", KIN)]),
        ({"number": 4, "title": "clean", "head": {"ref": "tidy-" + k0}, "body": ""},
         [("PR #4 HEAD REF", KIN)]),
        ({"number": 4, "title": None, "head": None, "body": None}, []),
    ]
    for i, (pr, want) in enumerate(cases):
        if subject_scan(pr_rows(pr)) != want:
            failures.append(f"PR surface case {i} must yield exactly its planted findings")
    mcases = [
        ("clean subject\n\nclean body\n# the " + k0 + " and " + w0 + " in a comment\n", []),
        ("clean\n\nbody\n" + _SCISSORS + "\ndiff --git " + w0 + "\n", []),
        ("# a comment\n\ntidy " + w0 + "\n\nbody\n", [("the message SUBJECT", LANE)]),
        ("first line\nsecond line, the " + k0 + "\n\nbody\n", [("the message SUBJECT", KIN)]),
        ("clean\n\nsee " + w0 + "\n", [("the message BODY", LANE)]),
    ]
    for i, (text, want) in enumerate(mcases):
        if subject_scan(message_rows(text)) != want:
            failures.append(f"message case {i} must yield exactly its planted findings")

    # The digest is pinned to the published standard, not to itself: a
    # known-answer test is the one arm a self-consistent wrong hash cannot pass.
    if subject_key("0" * 40, "abc") != ("0" * 40, "ba7816bf8f01cfea"):
        failures.append("subject_key must be the first 16 hex of SHA-256 over the subject")
    a = "a" * 40
    rows = commit_rows([(a, "tidy " + w0, "see " + w0)], {subject_key(a, "tidy " + w0)})
    if subject_scan(rows) != [(f"commit {a[:12]} BODY", LANE)]:
        failures.append("a baselined SUBJECT must be skipped and must NOT excuse its BODY")

    # ARM 10 -- rec (4), end to end in a real repository: a lane word in a
    # SUBJECT ONLY (clean body) is caught; a family reference in a body only is
    # not; a lane word in a body only is. Then the MODES, not the predicates --
    # the range, the empty range, the baseline in both directions, the shallow
    # clone, the message file -- then --open through a fake forge, and main()
    # itself as a subprocess, because a flag that reaches the wrong mode is
    # invisible to every arm that calls the mode directly.
    d = e = s = None
    real_gh = _gh
    try:
        subj = {1: "tidy " + w0 + " notes", 4: "ratified: the " + k0 + "'s read"}
        d, shas = _scratch_repo([
            ("base: clean", ""),
            (subj[1], "a clean body"),
            ("clean subject", "the " + k0 + " agreed"),
            ("clean subject two", "see " + w0),
            (subj[4], ""),
        ])
        got = subject_scan(commit_rows(commits(shas[0] + ".." + shas[3], d)))
        want = [(f"commit {shas[1][:12]} SUBJECT", LANE),
                (f"commit {shas[3][:12]} BODY", LANE)]
        if sorted(got) != sorted(want):
            failures.append("rec (4): the range must find the subject-only and body-only "
                            "lane plants and NOT the body-only family reference")
        k1, k4 = subject_key(shas[1], subj[1]), subject_key(shas[4], subj[4])
        fake = ("f" * 40, "0" * 16)

        def bl(name, text):
            p = os.path.join(d, name)
            with open(p, "w", encoding="utf-8", newline="") as fh:
                fh.write(text)
            return p

        def rowtext(*keys):
            return "".join("\t".join(k) + "\n" for k in keys)
        b_empty = bl("empty.tsv", "# accepted: none\n")
        b_debt = bl("debt.tsv", "# two\n" + rowtext(k1, k4))
        b_k4 = bl("k4.tsv", rowtext(k4))
        b_stale = bl("stale.tsv", rowtext(k1, k4, fake))
        b_bad = bl("bad.tsv", rowtext(k1, k4) + "not a key\n")
        b_none = os.path.join(d, "absent.tsv")
        m_lane = bl("msg-lane.txt", "tidy " + w0 + "\n")
        m_kin = bl("msg-kin.txt", "the " + k0 + " agreed\n\nbody\n")
        m_clean = bl("msg-clean.txt", "clean\n\nbody\n")
        # ASSEMBLED from the sibling gate's host pattern, never spelled out: this
        # file is itself scanned, and a literal fixture is caught by its own gate.
        m_sess = bl("msg-sess.txt", "clean subject\n\nhttps://"
                    + trailers._HOST.replace(chr(92), "") + "/code/session_abc\n")

        if history_verdict(set(), d) != (sorted([k1, k4]), [], [], 5):
            failures.append("history over an empty baseline must report both planted subjects as NEW")
        if history_verdict({k1, k4}, d)[:3] != ([], [], sorted([k1, k4])):
            failures.append("history must RE-FIND baselined subjects and call nothing new")
        if history_verdict({k1, k4, fake}, d)[1] != [fake]:
            failures.append("a baseline entry history no longer carries must be STALE")

        r0 = shas[0] + ".." + shas[3]
        r_kin = shas[3] + ".." + shas[4]
        modes = [
            ("range with a lane plant", range_mode, (r0, d, b_empty), 1),
            ("range with only a body family reference", range_mode,
             (shas[1] + ".." + shas[2], d, b_empty), 0),
            ("an EMPTY range", range_mode, (shas[3] + ".." + shas[3], d, b_empty), 1),
            ("range whose only subject hit is baselined", range_mode,
             (shas[0] + ".." + shas[2], d, b_debt), 0),
            ("range: the baseline never covers a BODY", range_mode, (r0, d, b_debt), 1),
            ("range with a family-reference subject", range_mode, (r_kin, d, b_empty), 1),
            ("range with that subject baselined", range_mode, (r_kin, d, b_debt), 0),
            ("range with no baseline file", range_mode, (r0, d, b_none), 1),
            ("an unreadable range", range_mode, ("no-such-rev..HEAD", d, b_empty), 1),
            ("history, all debt baselined", history_mode, (d, b_debt), 0),
            ("history, no debt baselined", history_mode, (d, b_empty), 1),
            ("history, half the debt baselined", history_mode, (d, b_k4), 1),
            ("history, a stale entry", history_mode, (d, b_stale), 1),
            ("history, a malformed baseline line", history_mode, (d, b_bad), 1),
            ("history, no baseline file", history_mode, (d, b_none), 1),
            ("msg-file, a lane subject", msg_file_mode, (m_lane,), 1),
            ("msg-file, a family-reference subject", msg_file_mode, (m_kin,), 1),
            ("msg-file, a clean message", msg_file_mode, (m_clean,), 0),
            ("msg-file, a session URL in the BODY", msg_file_mode, (m_sess,), 1),
            ("msg-file, unreadable", msg_file_mode, (b_none,), 1),
            ("ref, a lane word joined into a branch name", ref_mode, (ref,), 1),
            ("ref, a family word", ref_mode, ("refs/heads/tidy-" + k0,), 1),
            ("ref, clean", ref_mode, ("refs/heads/jas/tidy-branch",), 0),
            ("ref, EMPTY", ref_mode, ("",), 1),
        ]
        for label, fn, args, want_rc in modes:
            rc, out = _quiet(fn, *args)
            if rc != want_rc:
                failures.append(f"mode case '{label}' must exit {want_rc}, got {rc}")
            if subject_scan([("o", l, "subject") for l in out.splitlines()]):
                failures.append(f"mode case '{label}' echoed a vocabulary word")
        rc, out = _quiet(range_mode, r0, d, b_empty)
        if shas[1][:12] not in out or shas[3][:12] not in out:
            failures.append("a range finding must name the commit it is in")

        e = tempfile.mkdtemp(prefix="pr-gate-selftest-empty-")
        _git(["init", "-q"], e)
        if _quiet(history_mode, e, b_empty)[0] != 1:
            failures.append("history of a repository with NO commits must fail, not pass empty")
        # The shallow clone sees ONLY the last commit, and b_k4 accepts exactly
        # it: without the shallow refusal this would read OK.
        s = tempfile.mkdtemp(prefix="pr-gate-selftest-shallow-")
        _git(["clone", "-q", "--depth", "1", pathlib.Path(d).as_uri(), s])
        if _quiet(history_mode, s, b_k4)[0] != 1:
            failures.append("history of a SHALLOW clone must refuse")

        def forge(prs):
            def fake_gh(args):
                if "/pulls?" in args[0]:
                    return prs
                if "/check-runs" in args[0]:
                    return {"check_runs": []}
                if "/compare/" in args[0]:
                    return {"ahead_by": 0}
                raise RuntimeError("unexpected forge call")
            return fake_gh
        clean_pr = {"number": 4, "title": "clean", "body": "clean",
                    "head": {"ref": "tidy-branch", "sha": a}, "base": {"ref": "main"}}
        for label, prs, want_rc in [
                ("a lane word in a head ref", [dict(clean_pr, head={"ref": ref, "sha": a})], 1),
                ("a clean PR", [clean_pr], 0)]:
            globals()["_gh"] = forge(prs)
            try:
                rc, out = _quiet(open_mode, "owner/repo")
            finally:
                globals()["_gh"] = real_gh
            if rc != want_rc:
                failures.append(f"--open case '{label}' must exit {want_rc}, got {rc}")
            if want_rc and "PR #4 HEAD REF" not in out:
                failures.append(f"--open case '{label}' must name the PR and the surface")
            if subject_scan([("o", l, "subject") for l in out.splitlines()]):
                failures.append(f"--open case '{label}' echoed a vocabulary word")

        me = os.path.abspath(__file__)
        r_subj = shas[0] + ".." + shas[1]
        clis = [
            ("--history --baseline <all debt>", ["--history", "--baseline", b_debt], 0),
            ("--history --baseline <none accepted>", ["--history", "--baseline", b_empty], 1),
            ("--range --baseline <all debt>", ["--range", r_subj, "--baseline", b_debt], 0),
            ("--range --baseline <none accepted>", ["--range", r_subj, "--baseline", b_empty], 1),
            ("--msg-file <lane subject>", ["--msg-file", m_lane], 1),
            ("--msg-file <clean>", ["--msg-file", m_clean], 0),
            ("--baseline beside --open", ["--open", "--baseline", b_debt], 2),
            ("two modes at once", ["--history", "--msg-file", m_clean], 2),
            ("--ref <clean>", ["--ref", "refs/heads/main"], 0),
            ("--ref <family word>", ["--ref", "tidy-" + k0], 1),
            ("--ref <empty>", ["--ref", ""], 1),
            ("--range <empty>", ["--range", ""], 1),
            ("--msg-file <empty>", ["--msg-file", ""], 1),
        ]
        for label, argv, want_rc in clis:
            r = subprocess.run([sys.executable, me] + argv, cwd=d, capture_output=True,
                               text=True, encoding="utf-8", errors="replace",
                               env=dict(os.environ, PYTHONIOENCODING="utf-8"))
            if r.returncode != want_rc:
                failures.append(f"CLI case '{label}' must exit {want_rc}, got {r.returncode}")
            if "Traceback" in r.stdout + r.stderr:
                failures.append(f"CLI case '{label}' crashed instead of answering")
    except (OSError, RuntimeError) as err:
        failures.append(f"the scratch-repository arms could not run: {err}")
    finally:
        globals()["_gh"] = real_gh
        for p in (d, e, s):
            if p:
                shutil.rmtree(p, ignore_errors=True)

    # ARM 11 -- every string this file can print survives the Windows console
    # (cp1252). Docstrings are exempt: they are never printed.
    tree = ast.parse(pathlib.Path(__file__).read_text(encoding="utf-8"))
    docs = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.ClassDef)):
            body = getattr(node, "body", [])
            if body and isinstance(body[0], ast.Expr) and isinstance(
                    getattr(body[0], "value", None), ast.Constant):
                docs.add(id(body[0].value))
    for node in ast.walk(tree):
        if (isinstance(node, ast.Constant) and isinstance(node.value, str)
                and id(node) not in docs):
            try:
                node.value.encode("cp1252")
            except UnicodeEncodeError:
                failures.append(f"line {node.lineno}: a printable string cp1252 cannot encode")
    return failures


def self_test() -> int:
    failures = []
    S = "se" + "at"
    # ARM 1 — a planted forge-side path must be caught, in TITLE and in BODY.
    if not scan_description(1, "cite " + S + "/x/y.md", ""):
        failures.append("a planted path in a TITLE must be caught")
    if not scan_description(1, "", "see " + S + "/x/y.md line 3"):
        failures.append("a planted path in a BODY must be caught")
    # ...and the finding's identity must NAME the PR and the surface.
    got = scan_description(7, "", "see " + S + "/x/y.md")
    if not got or "PR #7 BODY" not in got[0][0]:
        failures.append("a finding must name its PR number and surface")
    # ARM 2 — compliant prose passes; None body (forge returns null) is safe.
    if scan_description(2, "role wording: the helm's brief", None):
        failures.append("role wording must pass; a null body must not crash")
    # ARM 3 — ref_vs_run, every branch, both directions.
    h = "a" * 40
    if "NO RUN" not in ref_vs_run(h, None, False, 0):
        failures.append("no run on head must say NO RUN")
    if "MISMATCH" not in ref_vs_run(h, "b" * 40, True, 0):
        failures.append("a run on another sha must say MISMATCH")
    if "STALE" not in ref_vs_run(h, h, True, 3):
        failures.append("green + moved base must say GREEN BUT STALE")
    if "NOT green" not in ref_vs_run(h, h, False, 0):
        failures.append("a red run on the current head must say so")
    if "current" not in ref_vs_run(h, h, True, 0):
        failures.append("green on current head over an unmoved base is current")
    # desk SN rec (1): the THIRD thing this line alone can know — the live surface is clean
    # while the recorded run is red ⇒ FIXED ON THE FORGE, RUN STALE. Both directions.
    if "FIXED ON THE FORGE" not in ref_vs_run(h, h, False, 0, live_clean=True):
        failures.append("a red run on the current head with CLEAN live surfaces must say FIXED ON THE FORGE, RUN STALE")
    if "FIXED ON THE FORGE" in ref_vs_run(h, h, False, 0, live_clean=False):
        failures.append("a red run with a LIVE finding must NOT claim it is fixed on the forge")
    if "FIXED ON THE FORGE" in ref_vs_run(h, h, False, 0):
        failures.append("with no live reading the line must stay the bare NOT green")
    # ARM 4 — the vocabulary is the SIBLING'S, not a copy: a shape the sibling
    # catches must be caught HERE through the import, so a sibling repair
    # propagates instead of invalidating this file silently.
    if not any("rootless" in w for _, w, _ in
               scan_description(3, "", "in " + "bri" + "efs" + "/x.md")):
        failures.append("the sibling's newest shape must reach this arm via the import")
    # ARM 5 — desk MC: a chat-session URL or trailer in forge-side prose is
    # caught in TITLE and BODY, the finding names its PR and surface, the matched
    # text is never echoed, and the attribution the scrub KEPT still passes.
    # Assembled from parts so this file's own source never matches the shapes.
    url = "https://" + "claude" + ".ai" + "/code/" + "session_" + "PLANTED0000"
    key = "Claude" + "-Session"
    if not scan_session(5, "", "Summary\n\n" + url + "\n"):
        failures.append("a planted session URL in a BODY must be caught")
    if not scan_session(5, "see " + url, ""):
        failures.append("a planted session URL in a TITLE must be caught")
    if not scan_session(5, "", "Summary\n\n" + key + ": abc\n"):
        failures.append("a planted session trailer in a BODY must be caught")
    got = scan_session(8, "", "x\n" + url)
    if not got or "PR #8 BODY" not in got[0][0]:
        failures.append("a session finding must name its PR number and surface")
    if any("PLANTED0000" in l for l in session_finding_lines(got)):
        failures.append("a session finding must NEVER echo the matched text")
    kept = ("Co-Authored-By: Claude <noreply@anthropic.com>\n\nGenerated with "
            "[Claude Code](https://" + "claude" + ".com/claude-code)")
    if scan_session(6, "", kept) or scan_session(6, None, None):
        failures.append("Co-Authored-By, the product link and a null body must pass")
    # ARM 5b -- the helm's order of 2026-10-18 (flask STATUS § 447): a host or account NAME in a PR TITLE or BODY is
    # caught, the finding names the PR, the surface and the line and NEVER the name, role words and a null body pass, and
    # open_mode itself (not only the scanner) reds on it and stays green on a clean PR. The name is read from the infra
    # gate's own list, which assembles it; this file never spells one.
    if infra is None:
        failures.append("this repository must carry check_infra_names.py for the PR-body infra-name arm")
    else:
        nm = infra.FORBIDDEN[0]
        if not scan_infra(11, "", "ran on " + nm + " today"):
            failures.append("a planted infrastructure name in a BODY must be caught")
        if not scan_infra(11, "on " + nm, ""):
            failures.append("a planted infrastructure name in a TITLE must be caught")
        got_i = scan_infra(12, "", "x\nran on " + nm)
        if not got_i or "PR #12 BODY" not in got_i[0][0] or got_i[0][1] != 2:
            failures.append("an infra finding must name its PR, its surface and its line")
        if any(nm.lower() in l.lower() for l in infra_finding_lines(got_i)):
            failures.append("an infra finding must NEVER echo the matched text")
        if scan_infra(13, "the Windows box", "ran on the bench account") or scan_infra(13, None, None):
            failures.append("role words and a null body must pass")
        _real_gh = globals()["_gh"]
        def _fake_gh(path_args, _title="t", _body=""):
            p = path_args[0]
            if "/pulls?" in p:
                return [{"number": 21, "title": _title, "body": _body,
                         "head": {"sha": "a" * 40, "ref": "x"}, "base": {"ref": "main"}}]
            if "/check-runs" in p:
                return {"check_runs": []}
            return {"ahead_by": 0}
        def _drive(body):
            buf = io.StringIO()
            globals()["_gh"] = lambda a: _fake_gh(a, "t", body)
            try:
                with contextlib.redirect_stdout(buf):
                    rc = open_mode("owner/repo")
            finally:
                globals()["_gh"] = _real_gh
            return rc, buf.getvalue()
        rc_bad, out_bad = _drive("ran on " + nm)
        if rc_bad != 1 or "infrastructure name" not in out_bad:
            failures.append("open_mode must RED on a PR body carrying an infrastructure name")
        if nm.lower() in out_bad.lower():
            failures.append("open_mode must NEVER echo the infrastructure name into the log")
        if "ANOTHER PR" not in out_bad:
            failures.append("the infra FAIL block must carry the cross-PR remedy line")
        rc_ok, out_ok = _drive("ran on the Windows box")
        if "confusables are not folded" not in out_ok or "CLOSED or MERGED PR bodies" not in out_ok:
            failures.append("the OK line must DECLARE what the infra arm does not cover")
        if rc_ok != 0 or "infra-name arm: 0 infrastructure names" not in out_ok:
            failures.append("open_mode must stay GREEN on a clean PR and DECLARE the infra arm's scope")
        # ARM 5c -- the helm's commission of 2026-10-18 (systems' G2 on kent's arm): the arm read the SOURCE while the
        # forge shows the RENDERING, so six spellings that RENDER as the name passed. Each is caught after the
        # normalisation; the plain name still matches; a hyphenated near-name and a look-alike letter from another
        # script still do NOT (confusables are not folded, and that is declared); a multi-line comment keeps line numbers.
        a_, b_ = nm[:2], nm[2:]
        rendered_cases = {
            "an HTML comment inside the name": a_ + "<!-- -->" + b_,
            "an HTML entity for one letter": "&#" + str(ord(nm[0])) + ";" + nm[1:],
            "a zero-width space inside": a_ + chr(0x200B) + b_,      # chr(), never a literal: this file is cp1252-linted
            "a soft hyphen inside": a_ + chr(0xAD) + b_,
            "an emphasis split": "**" + a_ + "**" + b_,
            "full-width letters": "".join(chr(ord(ch) + 0xFEE0) for ch in nm),
        }
        for what, s in rendered_cases.items():
            if not scan_infra(14, "", "ran on " + s):
                failures.append("a name that RENDERS through " + what + " must be caught")
            if not scan_infra(14, "on " + s, ""):
                failures.append("a TITLE that renders through " + what + " must be caught")
        if not scan_infra(14, "", "ran on " + nm):
            failures.append("the plain name must still be caught once the normaliser runs")
        look = {"k": chr(0x43A), "y": chr(0x443), "j": chr(0x458), "s": chr(0x455), "c": chr(0x441), "a": chr(0x430)}
        if scan_infra(15, "", "ran on " + nm[:2] + "-" + nm[2:]):
            failures.append("a HYPHENATED near-name is not the name: the normaliser must not drop '-'")
        if nm[0] in look and scan_infra(15, "", "ran on " + look[nm[0]] + nm[1:]):
            failures.append("a look-alike letter from another script is NOT folded (declared): it must not match")
        # kent's R1 (10-18 13:08): an UNCLOSED comment opener repeated was quadratic (64 KiB of "<!--" took 3 s); bounded
        # here at 1 s, ~100x the fixed cost; and a name after an unclosed opener is still caught (by the SOURCE scan)
        import time as _t
        _t0 = _t.monotonic(); rendered_text("<!--" * 16384); _dt = _t.monotonic() - _t0
        if _dt > 1.0:
            failures.append("rendered_text must be linear on unclosed comment openers (64 KiB took %.2f s)" % _dt)
        if not scan_infra(17, "", "<!-- never closed\nran on " + nm):
            failures.append("a name after an UNCLOSED comment opener must still be caught")
        got_c = scan_infra(16, "", "x\n<!-- a\nb -->\nran on " + a_ + "<!-- -->" + b_)
        if [w for w in got_c] != [("PR #16 BODY", 4)]:
            failures.append("a multi-line comment must keep the line numbers (want PR #16 BODY line 4, got " + repr(got_c) + ")")
    # ARM 6 -- desks SN/WB: the remedy promises a re-run on edit ONLY where the
    # workflow's bytes say so. Every state planted, both list forms; the note
    # must not promise what an unarmed trigger cannot deliver; and THIS
    # repository's own workflow must be armed, so dropping `edited` reds here.
    d = tempfile.mkdtemp(prefix="pr-gate-selftest-wf-")
    try:
        def wf(text):
            p = os.path.join(d, "w.yml")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(text)
            return p
        top = "on:\n  push:\n  pull_request:\n"
        if edited_trigger_armed(wf(top + "    types: [opened, synchronize, "
                                   "reopened, edited]\n\njobs:\n")) is not True:
            failures.append("an inline types list naming `edited` must read armed")
        if edited_trigger_armed(wf(top + "    # a comment\n    types:\n      - opened"
                                   "\n      - edited\n\njobs:\n")) is not True:
            failures.append("a block types list naming `edited` must read armed")
        if edited_trigger_armed(wf(top + "\npermissions:\n")) is not False:
            failures.append("a bare pull_request trigger (default types) is NOT armed")
        if edited_trigger_armed(wf(top + "    types: [opened, synchronize]\n")) is not False:
            failures.append("a types list without `edited` is NOT armed")
        if edited_trigger_armed(wf(top + "    types:\n      - opened\n  workflow_dispatch:\n"
                                   )) is not False:
            failures.append("a block list that ends without `edited` is NOT armed")
        # The non-author read's two findings, each planted with its control.
        # (1) A COMMENT IS NOT CONFIGURATION: `edited` in a trailing comment must
        # not read armed -- a false ARMED promises a re-run the trigger cannot give.
        if edited_trigger_armed(wf(top + "    types: [opened, synchronize]  "
                                   "# edited is deliberately NOT listed\n")) is not False:
            failures.append("`edited` inside a trailing COMMENT must NOT read armed")
        if edited_trigger_armed(wf(top + "    types:\n      - opened  # not edited\n"
                                   "      - edited  # re-run on a body edit\n")) is not True:
            failures.append("a block item with a trailing comment must still be read")
        if edited_trigger_armed(wf("on:\n  push:\n  pull_request:  # why\n    types: "
                                   "[edited]\n")) is not True:
            failures.append("a trigger line with a trailing comment must still be found")
        # (2) THE SET, NOT THE MEMBER: `types:` REPLACES the Actions defaults, so
        # `types: [edited]` is armed for the REMEDY while the gate stops running
        # on opened/synchronize. The set is readable, and the defaults are named.
        if pull_request_types(wf(top + "    types: [edited]\n")) != frozenset({"edited"}):
            failures.append("pull_request_types must return the SET it read")
        if pull_request_types(wf(top + "\npermissions:\n")) != _DEFAULT_TYPES:
            failures.append("a bare pull_request trigger means the Actions DEFAULT types")
        if _REQUIRED_TYPES <= pull_request_types(wf(top + "    types: [edited]\n")):
            failures.append("`types: [edited]` must FAIL the required-set test: the "
                            "gate would stop running on opened and synchronize")
        if edited_trigger_armed(wf("on:\n  push:\n")) is not None:
            failures.append("no pull_request trigger at all is UNREADABLE, not unarmed")
        if edited_trigger_armed(os.path.join(d, "absent.yml")) is not None:
            failures.append("a missing workflow is UNREADABLE, not unarmed")
    finally:
        shutil.rmtree(d, ignore_errors=True)
    yes, no, unk = (" ".join(rerun_note_lines(x)) for x in (True, False, None))
    if "by itself" not in yes or "gh run rerun" not in yes:
        failures.append("the armed note must promise the re-run AND name the fallback")
    for label, text in (("unarmed", no), ("unreadable", unk)):
        if "by itself" in text or "gh run rerun" not in text or "NO run" not in text:
            failures.append(f"the {label} note must NOT promise a re-run, and must "
                            "say to re-run the failed job by hand")
    here = pull_request_types()
    if here is None or not _REQUIRED_TYPES <= here:
        read = "unreadable" if here is None else (
            "not listed" if "edited" not in here else
            "missing " + ", ".join(sorted(_REQUIRED_TYPES - here)))
        failures.append("THIS repository's .github/workflows/scrub.yml must list "
                        "ALL of opened, synchronize, reopened and `edited` in its "
                        f"pull_request types (read: {read}) -- `types:` REPLACES the "
                        "defaults, and the remedy this gate prints depends on `edited`")
    failures += _subject_arms()
    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    if failures:
        return 1
    print(f"check_pr_descriptions SELF-TEST [pr-gate {self_id()}] over "
          f"[gate {gate.self_id()}]: OK (title+body arms both directions; "
          f"session arm both surfaces, never echoed; "
          f"ref_vs_run all five branches; sibling vocabulary reached via import; "
          f"pull_request types read from the workflow's bytes as a SET, comments "
          f"dropped, thirteen planted states; "
          f"subject arm: {_vocab_id()}, every word planted in its surfaces, "
          f"rec (4) subject-only plant in a scratch repository, range/history/"
          f"msg-file modes in both directions, --open through a fake forge, "
          f"main() as a subprocess, digest known-answer, cp1252)")
    print(_NOT_COVERED)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="forge-side prose gate (row I(a)) and commit-subject gate (desk QA)")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--open", action="store_true",
                      help="scan every open PR's title, head ref and body via the forge API")
    mode.add_argument("--range", metavar="REV",
                      help="scan every commit `git log REV` lists: subjects, and bodies "
                           "for lane names (forward only)")
    mode.add_argument("--history", action="store_true",
                      help="every subject reachable from HEAD against the accepted-debt "
                           "baseline, both directions (needs full depth)")
    mode.add_argument("--msg-file", metavar="PATH",
                      help="one commit-message file (the commit-msg hook)")
    mode.add_argument("--ref", metavar="NAME",
                      help="one ref name (the pushed branch, or a PR's head): a merge "
                           "subject will quote it")
    ap.add_argument("--baseline", metavar="PATH",
                    help="accepted-debt baseline for --range/--history "
                         "(default: subject_debt_baseline.tsv beside this file)")
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", ""),
                    help="owner/name for --open; defaults to GITHUB_REPOSITORY")
    args = ap.parse_args()
    if args.baseline is not None and not (args.range is not None or args.history):
        # A flag accepted and ignored runs a different check than the one asked.
        ap.error("--baseline applies only to --range and --history")
    if args.self_test:
        return self_test()
    # `is not None`: an EMPTY value was asked for, and must reach the mode that
    # refuses it rather than fall through to the help text.
    if args.range is not None:
        return range_mode(args.range, None, args.baseline)
    if args.history:
        return history_mode(None, args.baseline)
    if args.msg_file is not None:
        return msg_file_mode(args.msg_file)
    if args.ref is not None:
        return ref_mode(args.ref)
    if args.open:
        if not args.repo:
            print("FAIL: no repo — pass --repo owner/name or set GITHUB_REPOSITORY")
            return 1
        return open_mode(args.repo)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
