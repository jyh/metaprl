#!/usr/bin/env python3
"""No infrastructure name (a host, an account) may sit in the public tree.

WHY THIS EXISTS
---------------
The private-paths gate (check_private_paths.py) fires on PATHS into the private
record. The 2026-09-02 refuter pass on the v1 flip package found 41 occurrences of
a class no gate covered: the name of the machine the episodes ran on and the name
of the subscription account that ran them, in frozen documents, evidence READMEs
and harness defaults. They were replaced by role words ("the Studio", "the bench
account", the ssh alias `studio`) and the class is GATED here, so that it is held
by an instrument rather than remembered.

WHAT IT CHECKS
--------------
Every tracked, text file, case-insensitively, for the forbidden names. The names
are ASSEMBLED in this file rather than spelled, for the same reason the trailer
gate assembles its fixture: this gate scans itself.

FAILING CLOSED
--------------
A scan over zero files REDS. `--self-test` proves the empty scan is fatal, that a
planted name is caught in every case and prefix form, and that the role words pass,
before the tree scan is trusted.

WHAT IT DOES NOT DO
-------------------
It does not scan commit MESSAGES. History carried one such message at the time this
gate was written; whether that history is rewritten before the flip is the owner's
decision (PUBLISH-CHECKLIST.md), and a gate that reds on a decision not yet taken is
a gate that gets abandoned.

PORTED TO salt 2026-10-07 BY THE HELM (154th head) UNDER COUNCIL 2026-10-07 RULING 3, his words "ratchet only is
fine": salt's tree carries infrastructure names today (26 lines in 6 files at the port, all documentation and
Lean comments), so here the TREE ARM IS A RATCHET -- it accepts the residue listed in
scripts/infra_names_baseline.tsv (file, line-sha16; never the text, never the name) and REDS on anything NEW.
The push arm (--range) accepts an added line only when it is byte-identical to a baselined line in the same file
(a verbatim move); an EDITED line that still carries a name is NEW, and the remedy is to drop the name from the
line, not to grow the baseline. saltbench's copy (the source of this port) has a clean tree and reds on any hit;
the two files are otherwise kept the same so a fix in one ports to the other.

THE PATH ARM AND THE DIGEST FILE COLUMN (2026-10-07, found porting this gate to a fourth repo)
---------------------------------------------------------------------------------------------
Two defects lived in this script, not in any one repo, and both were measured on a port that failed:
  1. THE BASELINE LEAKED. Its file column was a clear PATH, so a repo whose tracked paths carry a declared name
     wrote those names into its own baseline files -- and the port's own commit was then refused by --tree,
     --history and the hook, while PR CI scans a synthetic merge sha that no history row can name.
  2. THE GATE WAS PATH-BLIND. It read file CONTENTS and never file NAMES, so a new file named for a host
     passed every arm in every repo.
THE FILE COLUMN, both baselines: a clear path OR `sha256:<first 16 hex of sha256(path bytes)>`; the reader takes
either. The WRITER emits the digest exactly when the path itself carries a declared name, and the clear path
otherwise -- so a baseline written for a repo with no such path is byte-identical to the format before this
change, and a baseline written for any repo carries no declared name at all.
THE PATH ARM: --range and --history read the paths a range or commit ADDS or RENAMES TO (`git diff
--name-status`, the same base the line arm uses); --tree reads every tracked path. A path finding is accepted
only by a PATH ROW, keyed by the path's digest and marked `PATH` where a line row carries a number or a line
digest -- tree `sha256:<16><TAB>PATH<TAB><what>`, history `<sha><TAB>sha256:<16><TAB>PATH` -- so a path row
and a line row can never accept each other's finding. Every finding names a name-bearing file by its digest, never in clear.
To find the file a digest names, hash the tracked paths LOCALLY; never paste the answer into a public surface.

EXIT CODES (2026-10-07: until this section existed, a range git could not read was a GREEN)
-------------------------------------------------------------------------------------------
  0  clean: every population the arm was asked to read was read, and nothing NEW was found.
  1  a finding, or a refusal BY NAME: a NEW name, a tree baseline that is missing, a SHALLOW clone under
     --history, an empty scan, a forbidden set smaller than declared, or --history with --range.
  2  usage: argparse refused the command line.
  3  GIT COULD NOT READ what the arm was asked to scan: a range end that does not resolve (a missing sha, an
     empty side, a three-dot range, a FILE name), an object the repository does not hold, or a directory that
     is not a repository. NOTHING was scanned, and the run never prints OK.
WHY 3 EXISTS: the line arm and the path arm read git's stdout and never its exit status, so `--range
<unresolvable sha>..HEAD` read git's EMPTY stdout as "nothing added" and printed OK with rc 0, and so did a
commit whose blob is missing under --history (which then WROTE a shorter baseline). Every git call this gate
makes now checks git's exit status. --range also RESOLVES both ends before it diffs, and every diff ends its
revisions with `--`: without both, a range whose two ends name tracked files diffs the WORKING TREE and exits 0,
and outside a repository git compares the two FILES and exits 0. git's own message is withheld (it can name a
path, and a CI log is public): rerun the named git command locally to read it.

"""
from __future__ import annotations

import argparse
import hashlib
import os
import pathlib
import re
import subprocess
import sys

GIT_UNREADABLE = 3   # the exit code when git could not read what an arm was asked to scan (EXIT CODES above)


class GitReadError(Exception):
    """A git call this gate needs for a verdict exited nonzero. Carries the SUBCOMMAND and rc only: git's own
    message can name a path, and the gate's output lands in a public log."""


def _git(args: list, cwd=None, raw: bool = False):
    """EVERY git call the gate makes for a verdict goes through here, and a nonzero exit RAISES GitReadError
    (rc 3 at the CLI, via run_arm). git's stdout alone cannot tell "nothing" from "could not look": an
    unresolvable revision prints nothing, exactly like an empty diff. `raw` returns bytes (for `-z` lists)."""
    if raw:
        r = subprocess.run(["git"] + args, cwd=cwd, capture_output=True)
    else:
        r = subprocess.run(["git"] + args, cwd=cwd, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise GitReadError(f"`git {args[0]}` exited {r.returncode}")
    return r.stdout


def _root() -> pathlib.Path:
    """The repository this script lives in: the --tree arm's default root. Resolved when an arm needs it, through
    the checked runner, so a copy of the script outside any repository exits 3 and not with a traceback's 1."""
    return pathlib.Path(_git(["rev-parse", "--show-toplevel"], cwd=pathlib.Path(__file__).resolve().parent).strip())

# Assembled, never spelled — this gate scans itself.
#
# ⛔⛔ WIDENED 2026-09-10, on `systems`'s measurement of a FALSE GREEN. This list held exactly ONE
#   stem, because when the gate was written the host and the account SHARED it. The fleet now runs
#   FOUR accounts across FOUR boxes, and a BOX NAME (2 files) and an ACCOUNT NAME (2 files) were sitting
#   on PUBLIC main with Scrub GREEN. The gate was never wrong; it was OUTGROWN, and nothing announced
#   that.  ⇒ 🔑 AN ARM THAT NAMES ONE MEMBER OF A SET GOES VACUOUS WHEN THE SET GROWS.
FORBIDDEN = [
    "kri" + "ter" + "ion",      # a box, and an account: the original single stem
    "yu" + "kon",               # the box the seats run on
    "ke" + "nai",               # a box
    "jao" + "quin",             # a box
    "ja" + "son" + "h",         # an account
    "jy" + "aletheia",          # an account
    "claude-account-" + "ja" + "son",   # see the note below: the bare stem is NOT gateable
    "claude-acct-" + "ja" + "son",      # the SAME account's SECOND config-dir spelling (the roster's live row; kent, 2026-10-07): the acct/account glob trap, closed here
    "salt" + "forge",           # an account, added 2026-09-12 on the Captain's order at council
    "kat" + "mai",              # the run box, RENAMED 2026-09-25 from the first stem (which stays: it is an account too)
    "oto" + "rongo",            # the NAS the private bare repositories moved to (O54 S3, 2026-10-24; the helm's ruling 15:11); not a roster box
]

# ⛔ THE ONE THAT CANNOT BE A BARE SUBSTRING, AND THE REASON IS NOT A TECHNICALITY.
#   One account's name is the Captain's own GIVEN NAME, which appears legitimately in this public
#   repo as AUTHORSHIP -- `CITATION.cff` and `paper/saltbench-v1.tex` (\author{...}, and twice in the
#   bibliography). A bare substring rule would RED the paper's author line, and a gate that reds on
#   correct content is a gate that gets deleted. So that account is gated in its CONFIG-DIR SHAPE
#   only, which no byline can produce.
#   ⇒ 🔑 A NAME THAT IS ALSO A PERSON'S NAME IS GATEABLE ONLY IN THE SHAPES INFRASTRUCTURE USES.
#   ⇒ Anything this shape cannot catch is carried by the CONVENTION instead: a public tree names
#     accounts by anonymised label (ACCOUNT A / ACCOUNT B), with the mapping in the private record.

# ⛔ WHAT THIS TRIPWIRE DOES AND -- MORE IMPORTANTLY -- WHAT IT DOES NOT.
#   It refuses to scan when the forbidden set has SHRUNK below the count declared here. That catches
#   a name being DELETED. It does NOT catch the failure that actually happened, which was the FLEET
#   GROWING while this list stood still: both lines below are edited by the same hand, so they move
#   together and neither can notice a new account or a new box existing.
#   ⇒ 🔑 A DECLARATION AND THE THING IT DESCRIBES, EDITED TOGETHER, CANNOT CHECK EACH OTHER.
#   ⇒ **Completeness is not checkable from inside this repo at all.** The roster lives outside it and
#     MOVES, and CI cannot read it. Only a FLEET-SIDE check that reads the roster can know this set is
#     incomplete; that check is the load-bearing one and this is a second lock, not the lock.
#     (Named by `systems` on the bus, 2026-09-10, correcting this seat's first claim for it.)
#   The count is printed on every run so a reader can compare it against the fleet map rather than
#   trusting a date. Reconciled against the fleet roster on the date below -- its box column and its
#   account column. Adding a box or an account means editing BOTH lines, deliberately.
DECLARED_NAMES = 11
DECLARED_RECONCILED = "2026-10-24"   # the NAS name was added by ruling, not from the roster (the roster has no NAS row): the other ten were reconciled 2026-10-07

# THE RECONCILIATION ITSELF, WRITTEN OUT, so a reader can check COMPLETENESS without re-deriving it.
# The roster carries 6 ACCOUNTS and 4 BOXES -- 10 entities, covered by the 10 stems above because two
# stems each cover a box and an account that share a word. (Since 2026-09-25 the run box has its own
# stem; the first stem stays for the account that shares its old word, and for the tree's history.) Entity -> the stem that catches it:
#
#     account  jy-aletheia      -> its own stem
#     account  ja-son           -> the CONFIG-DIR shape only (see the note above: it is also a byline)
#                                 -- in BOTH its spellings (claude-account- and claude-acct-; the second was missed until 2026-10-07)
#     account  jy-<the box word>-> the box stem, as a substring
#     account  ja-son-h         -> its own stem
#     account  salt-forge       -> its own stem       (added 2026-09-12)
#     account  <box4>-local     -> the box-4 stem, as a substring
#     box      yu-kon           -> its own stem       box  ke-nai   -> its own stem
#     box      kat-mai          -> its own stem       box  jao-quin -> its own stem
#     (the run box, named <the box word> until 2026-09-25; that stem still catches the old name)
#
# ⛔ THIS TABLE IS A SNAPSHOT OF A FILE THAT LIVES ELSEWHERE AND MOVES, exactly like the roots list
#   in the private-paths gate. It is written down not because it stays true but because a reader who
#   suspects it has stopped being true can check it in one pass instead of rebuilding the derivation.


def tracked_paths(root=None) -> list[str]:
    """EVERY tracked path -- binaries, symlinks and gitlinks included: the path arm reads names, not contents."""
    out = _git(["ls-files", "-z"], cwd=root or _root(), raw=True)
    return [rel for rel in out.decode("utf-8").split("\0") if rel]


def tracked_files(root=None) -> list[tuple[str, str]]:
    root = pathlib.Path(root or _root())
    out = _git(["ls-files", "-z"], cwd=root, raw=True)
    rows = []
    for rel in out.decode("utf-8").split("\0"):
        if not rel:
            continue
        p = root / rel
        if not p.is_file():
            continue
        data = p.read_bytes()
        if b"\0" in data:
            continue  # binary
        rows.append((rel, data.decode("utf-8", errors="replace")))
    return rows


def scan(rows: list[tuple[str, str]]) -> list[tuple[str, int, str]]:
    found = []
    for rel, text in rows:
        for i, line in enumerate(text.splitlines(), 1):
            low = line.lower()
            if any(n in low for n in FORBIDDEN):
                found.append((rel, i, line.strip()[:160]))
    return found


# ⛔⛔ THE FINDING LINE WITHHOLDS THE MATCHED TEXT — desk row `PX`, the Captain's word 2026-09-16
#   ("yes, accept rec"), executed by the 79th helm head.
#
#   WHY. This gate exists to stop an infrastructure name entering a PUBLIC repo. Until this change it
#   REPORTED each finding as `  <file>:<line>: <the whole matched line>` — and on a public repo that
#   report lands in a world-readable Actions log. ⇒ 🔑 THE MECHANISM BUILT TO STOP A PRIVATE STRING
#   ENTERING THE RECORD PUBLISHED A SAMPLE OF EXACTLY WHAT IT CAUGHT.
#
#   ⭐ DRIVEN BEFORE THE CHANGE, ON A SCRATCH REPO: a planted line printed the account name, the home
#   path AND an unrelated marker that happened to share the line. **The leak is not bounded by the
#   name it matched** — it is the whole line, to 160 characters.
#
#   ⭐ MEASURED AT THE FORGE, the reason this was not hypothetical: across 92 failed Scrub runs on the
#   five gated public repos, 25 carried a gate FAIL block, and the home-directory / host / account
#   classes appear in saltbench runs ONLY — because this file is the only UNTRUNCATED echoer and it
#   runs in this repo alone (404 in salt, saltworks, jas, x86lean).
#
#   ⛔ WHAT IS KEPT, AND WHY IT IS NOT A BARE COUNT. Row I(c) (08/31) already paid for that mistake:
#   *"a count is not a scope; the verdict carries its scope or it carries nothing."* A fixer needs to
#   find the occurrence, so the FILE and the LINE NUMBER stay. What goes is the TEXT.
_FINDING_LABEL = "an infrastructure name (account or host)"


# ---------------------------------------------------------------------------
# THE FILE COLUMN AND THE PATH ARM (2026-10-07; the docstring's last section says why).
# A path is shown and written CLEAR unless it carries a declared name, and then ONLY as its digest -- in a
# finding, in a baseline row, everywhere. The reader accepts either form, so every baseline written before
# this change stays valid byte for byte.
# ---------------------------------------------------------------------------
DIGEST_PREFIX = "sha256:"
PATH_KIND = "PATH"   # where a LINE row carries a line digest (tree) or a count (history); never 16 hex, never a number
PATH_LABEL = "an infrastructure name in a file PATH"


def names_in(s: str) -> bool:
    low = s.lower()
    return any(n in low for n in FORBIDDEN)


def path_digest(rel: str) -> str:
    return DIGEST_PREFIX + hashlib.sha256(rel.encode("utf-8", "replace")).hexdigest()[:16]


def file_field(rel: str) -> str:
    """What a finding PRINTS and a baseline WRITES for a file: its digest when the path carries a name."""
    return path_digest(rel) if names_in(rel) else rel


def file_keys(rel: str) -> tuple:
    """What a baseline row may hold for this file -- the clear path or its digest. Both are READ."""
    return (rel, path_digest(rel))


def path_hits(paths) -> list:
    """The path arm: every path that itself carries a declared name, in the order given."""
    return [p for p in paths if names_in(p)]


def finding_line(rel: str, i: int) -> str:
    """The one place a finding is rendered. File + line + CATEGORY, never the matched text."""
    return f"  {file_field(rel)}:{i}: {_FINDING_LABEL}"


def path_finding_line(rel: str) -> str:
    """A PATH finding names the file by its digest only: the path IS the matched text."""
    return f"  {path_digest(rel)}: {PATH_LABEL}"


def _line_row_accepts(base, rel: str, sha16: str):
    """The accepted LINE row for this finding, or None. A path row cannot match: its second key is PATH."""
    for k in file_keys(rel):
        if (k, sha16) in base:
            return (k, sha16)
    return None


def _path_row_accepts(base, rel: str):
    """The accepted PATH row for this path, or None. Keyed by DIGEST only: a clear row would carry the name."""
    k = (path_digest(rel), PATH_KIND)
    return k if k in base else None


def self_test() -> int:
    failures = []
    # 1. The empty set is FATAL, first.
    if scan([]) != []:
        failures.append("scan([]) must find nothing")
    if not _is_empty_scan_fatal([]):
        failures.append("an empty file set must be FATAL, not green")
    # 2. EVERY name is planted, in every case and prefix form -- not just FORBIDDEN[0]. A per-name
    #    loop is the arm that a widened list cannot silently outgrow.
    for stem in FORBIDDEN:
        for form in (stem, stem.capitalize(), "x" + stem, "ssh " + stem + "-lan 'x'", stem.upper()):
            if len(scan([("f.md", f"a line\n{form} here\n")])) != 1:
                failures.append(f"planted form {form!r} must be caught exactly once")
    # 2b. THE TRIPWIRE ITSELF, driven: a set smaller than the declaration must be FATAL. Without this
    #     arm the declaration is a comment, and a comment cannot fail.
    if _declared_ok(FORBIDDEN[:-1]):
        failures.append("a set smaller than DECLARED_NAMES must be FATAL")
    if not _declared_ok(FORBIDDEN):
        failures.append("the live set must satisfy its own declaration")
    # 2c. The author's given name, standing alone as a byline, must PASS -- it is authorship, not
    #     infrastructure, and it is in this repo's own CITATION.cff and paper.
    if scan([("CITATION.cff", "  given-names: Ja" + "son\n\\author{Ja" + "son Hickey}\n")]):
        failures.append("an author byline must not be caught")
    # 3. The role words pass.
    clean = [("g.md", "on the Studio, on the bench account, STUDIO=\"${STUDIO:-studio}\", ssh studio 'x'\n")]
    if scan(clean):
        failures.append("role words must pass")
    # 4. The gate scans itself and is clean (it assembles, never spells).
    me = pathlib.Path(__file__).read_text(encoding="utf-8")
    if scan([("scripts/check_infra_names.py", me)]):
        failures.append("this file must not spell the name it forbids")
    # 5. ⛔⛔ THE FINDING LINE MUST NOT CARRY THE MATCHED TEXT — desk `PX`. This is the arm that makes
    #    the withholding a PROPERTY and not a habit: the renderer is driven on a real finding and the
    #    output is checked for the very thing it must never contain.
    #    ⚠️ THE LEAK WAS NEVER BOUNDED BY THE NAME IT MATCHED — the old form printed the WHOLE line, so
    #    anything sharing that line went to a public log too. The control below plants exactly that:
    #    a secret-shaped neighbour with no infrastructure name of its own.
    planted_name = "salt" + "forge"
    neighbour = "SIDECAR-SECRET-XYZ"
    probe_line = f"export CFG=/Users/jyh/.claude-account-{planted_name}/x  # {neighbour}"
    hits = scan([("cfg.sh", probe_line + "\n")])
    if len(hits) != 1:
        failures.append("the finding-line probe must produce exactly one hit to render")
    else:
        rel, i, matched = hits[0]
        rendered = finding_line(rel, i)
        if planted_name in rendered:
            failures.append("the finding line LEAKS the matched infrastructure name")
        if neighbour in rendered:
            failures.append("the finding line LEAKS a neighbour string sharing the matched line")
        if matched in rendered:
            failures.append("the finding line LEAKS the matched text")
        # ⭐ AND IT MUST STILL BE ACTIONABLE — row I(c): a count is not a scope. A renderer that
        #   withheld the file or the line number would pass every check above and be useless.
        if f"{rel}:{i}" not in rendered:
            failures.append("the finding line must still name the FILE and the LINE NUMBER")
        # ⭐ THE VACUITY CONTROL: the old form must FAIL the very checks the new form passes, or the
        #   arm proves nothing about the change.
        old_form = f"  {rel}:{i}: {matched}"
        if planted_name not in old_form or neighbour not in old_form:
            failures.append("CONTROL: the pre-change form should have leaked; this arm is vacuous")

    # 6. THE RATCHET, on the pure verdict (salt, ruling 3): a baselined line passes; the same line EDITED is
    #    NEW; a missing baseline with findings is UNARMED-FATAL (never a pass); an accepted line that vanished
    #    is debt PAID, not red; a baselined line MOVED to another file is NEW (keyed by file -- stated).
    nm = "salt" + "forge"
    base_line = f"ran on {nm} last night"
    f1 = scan_with_lines([("d.md", base_line + "\n")])
    if len(f1) != 1:
        failures.append("ratchet fixture must produce exactly one finding")
    else:
        key = {("d.md", line_sha(base_line))}
        new, paid, unarmed = tree_verdict(f1, key)
        if new or paid or unarmed:
            failures.append("a baselined line must PASS the tree ratchet")
        edited = scan_with_lines([("d.md", base_line + " again\n")])
        new, paid, unarmed = tree_verdict(edited, key)
        if len(new) != 1 or len(paid) != 1 or unarmed:
            failures.append("an EDITED baselined line must be NEW and leave the old entry as debt paid")
        new, paid, unarmed = tree_verdict(f1, None)
        if not unarmed:
            failures.append("a MISSING baseline with findings must be UNARMED-FATAL")
        new, paid, unarmed = tree_verdict([], key)
        if new or unarmed or len(paid) != 1:
            failures.append("a vanished accepted line must read as debt PAID, not red")
        moved = scan_with_lines([("e.md", base_line + "\n")])
        new, _paid, _u = tree_verdict(moved, key)
        if len(new) != 1:
            failures.append("a baselined line MOVED to another file must be NEW (keyed by file)")
        if line_sha(base_line) in finding_line("d.md", 1) or nm in finding_line("d.md", 1):
            failures.append("the finding line must carry neither the digest nor the name")
    path_receipt = _self_test_paths(failures)
    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    if failures:
        return 1
    print(f"check_infra_names SELF-TEST: OK (empty scan fatal proven FIRST, "
          f"{len(FORBIDDEN) * 5} planted forms caught across {len(FORBIDDEN)} name(s), "
          f"the shrunk-set tripwire fires, an author byline passes, role words pass, self clean, "
          f"the finding line withholds the matched text and still names file:line; the tree ratchet: baselined passes, edited is new, missing baseline is fatal, vanished is paid, moved is new; "
          f"{path_receipt})")
    return 0


class _FixtureError(Exception):
    """A scratch-repo git step failed. Carries the SUBCOMMAND and rc only: the fixture paths carry declared names,
    and git's own message would print them into a public log."""


def _self_test_paths(failures: list) -> str:
    """Arms 7-11: THE PATH ARM AND THE DIGEST FILE COLUMN (2026-10-07), and arms 12-16 (git's exit status), which
    run first. The git arms drive the SAME mode functions the CLI runs, on scratch repositories built here. No
    failure text ever carries a fixture path or git output."""
    import contextlib
    import io
    import tempfile

    def leaks(text: str) -> bool:
        return names_in(text)

    # 7. PURE -- the renderer and the two row kinds.
    p_bad = "notes/" + FORBIDDEN[1].capitalize() + "-setup.md"      # a box stem, in a capitalised form
    p_ren = "ops/" + FORBIDDEN[4] + "-readme.md"                     # an account stem
    d_bad, d_ren = path_digest(p_bad), path_digest(p_ren)
    if not (names_in(p_bad) and names_in(p_ren)):
        failures.append("CONTROL: the fixture paths must carry a declared name, or every path arm is vacuous")
    if leaks(finding_line(p_bad, 3)) or f"{d_bad}:3" not in finding_line(p_bad, 3):
        failures.append("a LINE finding in a name-bearing file must name the file by digest, never in clear")
    if leaks(path_finding_line(p_bad)) or d_bad not in path_finding_line(p_bad):
        failures.append("a PATH finding must name the path by digest, never in clear")
    if file_field("docs/clean.md") != "docs/clean.md" or finding_line("docs/clean.md", 2) != f"  docs/clean.md:2: {_FINDING_LABEL}":
        failures.append("a clean path must stay CLEAR in a finding and in a baseline row")
    probe = "x " + FORBIDDEN[2]
    if len(tree_verdict([(p_bad, 1, probe)], {(d_bad, PATH_KIND)})[0]) != 1:
        failures.append("COLLISION: a tree PATH row must not accept a LINE finding in the same file")
    if len(tree_verdict([], {(d_bad, line_sha(probe))}, [p_bad])[0]) != 1:
        failures.append("COLLISION: a tree LINE row keyed by the path digest must not accept the PATH finding")
    if len(tree_verdict([], {(p_bad, PATH_KIND)}, [p_bad])[0]) != 1:
        failures.append("a CLEAR path row (it would itself carry the name) must not accept a path finding")
    if len(hist_verdict({("abc123def456", p_bad): 1}, set(), {("abc123def456", d_bad, PATH_KIND)})[0]) != 1:
        failures.append("COLLISION: a history PATH row must not accept a LINE finding")
    if len(hist_verdict({}, {("abc123def456", p_bad)}, {("abc123def456", d_bad)})[1]) != 1:
        failures.append("COLLISION: a history LINE row keyed by the path digest must not accept the PATH finding")

    # 11. (iv) THE LIVE BASELINES PARSE -- every data row is a well-formed LINE row or PATH row, and no clear file
    #     field carries a declared name (that would be the leak itself). Row numbers only, never row text.
    digest_re = re.compile(r"sha256:[0-9a-f]{16}")
    for label, live in (("tree", TREE_BASELINE), ("history", HIST_BASELINE)):
        if not os.path.exists(live):
            continue
        with open(live, encoding="utf-8") as fh:
            for n, raw in enumerate(fh, 1):
                if not raw.strip() or raw.startswith("#"):
                    continue
                parts = raw.rstrip("\n").split("\t")
                if label == "tree":
                    ok = len(parts) >= 2 and (
                        (parts[1] == PATH_KIND and digest_re.fullmatch(parts[0]) is not None)
                        or (re.fullmatch(r"[0-9a-f]{16}", parts[1]) is not None and parts[0] != ""))
                    field = parts[0] if parts else ""
                else:
                    ok = len(parts) >= 3 and re.fullmatch(r"[0-9a-f]{7,40}", parts[0]) is not None and (
                        (parts[2] == PATH_KIND and digest_re.fullmatch(parts[1]) is not None)
                        or (parts[2].isdigit() and parts[1] != ""))
                    field = parts[1] if len(parts) > 1 else ""
                if not ok:
                    failures.append(f"(iv) the live {label} baseline's row {n} is neither a LINE row nor a PATH row")
                elif names_in(field):
                    failures.append(f"(iv) the live {label} baseline's row {n} carries a declared name in CLEAR")

    # 8-10. THE GIT ARMS, on a scratch repository. GIT_* is cleared for the duration, so a caller's GIT_DIR (a
    #       hook) cannot point these at the repository under test.
    saved = {k: os.environ.pop(k) for k in [k for k in os.environ if k.startswith("GIT_")]}
    try:
        with tempfile.TemporaryDirectory(prefix="infra-names-selftest-", ignore_cleanup_errors=True) as tmp:
            # git's exit status FIRST: every arm after it reads git, and a runner that misreads git breaks them all.
            _self_test_git_rc(failures, pathlib.Path(tmp), contextlib, io)
            _self_test_git(failures, pathlib.Path(tmp), p_bad, d_bad, p_ren, d_ren, leaks, contextlib, io)
            _self_test_write_merge(failures, pathlib.Path(tmp), contextlib, io)
    except _FixtureError as e:
        failures.append(f"the scratch-repo fixture FAILED at {e} -- the path arms did NOT run (never a pass)")
    except Exception as e:  # the type only: a message could carry a fixture path
        failures.append(f"the scratch-repo fixture raised {type(e).__name__} -- the path arms did NOT run (never a pass)")
    finally:
        os.environ.update(saved)
    return ("the path arm: a name-bearing path is refused under --range, --tree and --history (added and renamed-to), "
            "a digest row accepts it, a rename out is no finding, path and line rows never cross, findings name it "
            "by digest; written baselines carry no name; pre-change clear-path baselines parse and pass and are "
            "re-written byte for byte; git's exit status is read: an unresolvable range (a missing sha either side, "
            "three dots, an empty side, file names, an empty string, and through the CLI) exits 3 and never OK, and "
            "so do a missing object under --range, --history and --history --write-baseline (which writes nothing) "
            "and a non-repository under --tree, --history, --range and the CLI; an empty VALID range still passes, "
            "as do a ref or HEAD that shares a tracked file's name; a shallow clone under --history still refuses "
            "by name with exit 1")


def _fixture_git(cwd, nohooks, *args) -> str:
    """The scratch repositories' git: identity, no signing, no hooks, and a failure is a _FixtureError, never a pass."""
    r = subprocess.run(["git", "-c", "user.name=infra-names self-test", "-c", "user.email=self-test@example.invalid",
                        "-c", "commit.gpgsign=false", "-c", "core.autocrlf=false", "-c", "init.defaultBranch=main",
                        "-c", "core.hooksPath=" + str(nohooks),
                        # ADH: NO AUTOMATIC PACKING. Control (d) removes ONE loose object by path, so the object must be
                        # loose; a runner whose gitconfig packs after a commit made that control fail at random (2026-10-15).
                        "-c", "gc.auto=0", "-c", "maintenance.auto=false", "-c", "receive.autogc=false"] + list(args),
                       cwd=cwd, capture_output=True)
    if r.returncode != 0:
        raise _FixtureError(f"git {args[0]} (rc {r.returncode})")
    return r.stdout.decode("utf-8", "replace").strip()


def _ensure_loose(repo, blob):
    """ADH: make `blob` a LOOSE object in `repo` and return its path, or None with the reason in .why.

    Control (d) removes one object by file path, so the object must be a file under objects/XX/. If it is in a pack
    (a runner that packs after a commit), the packs are moved aside and re-exploded with `git unpack-objects`: every
    object in them becomes loose, and the repository is the same repository. A failure is returned, never skipped."""
    objdir = repo / ".git" / "objects"
    obj = objdir / blob[:2] / blob[2:]
    if obj.is_file():
        return obj, ""
    stash = repo / ".git" / "adh-packs-aside"
    stash.mkdir(exist_ok=True)
    packs = sorted((objdir / "pack").glob("*.pack"))
    for p in packs:
        for ext in (".pack", ".idx", ".rev", ".bitmap", ".mtimes", ".keep"):
            q = p.with_suffix(ext)
            if q.exists():
                q.replace(stash / q.name)
    for p in sorted(stash.glob("*.pack")):
        r = subprocess.run(["git", "-c", "gc.auto=0", "unpack-objects", "-q"], cwd=repo,
                           stdin=open(p, "rb"), capture_output=True)
        if r.returncode != 0:
            return None, f"git unpack-objects failed on {p.name} (rc {r.returncode})"
    if obj.is_file():
        return obj, ""
    cnt = subprocess.run(["git", "count-objects", "-v"], cwd=repo, capture_output=True).stdout.decode("utf-8", "replace")
    ver = subprocess.run(["git", "--version"], capture_output=True).stdout.decode("utf-8", "replace").strip()
    return None, (f"{ver}; {len(packs)} pack(s) moved aside; count-objects: " + " ".join(cnt.split()))


def _self_test_git(failures, tmp, p_bad, d_bad, p_ren, d_ren, leaks, contextlib, io) -> None:
    repo = tmp / "r"
    repo.mkdir()
    nohooks = tmp / "no-hooks"

    def git(*args) -> str:
        return _fixture_git(repo, nohooks, *args)

    def put(rel: str, text: str) -> None:
        f = repo / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_bytes(text.encode("utf-8"))

    def commit(msg: str) -> str:
        git("add", "-A")
        git("commit", "-q", "--no-verify", "-m", msg)
        return git("rev-parse", "HEAD")

    def drive(fn, *a, **kw):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = fn(*a, **kw)
        return rc, buf.getvalue()

    def arms(c_lo, c_hi, tree_b, hist_b):
        return (("--range", range_mode, (f"{c_lo}..{c_hi}",), {"cwd": str(repo), "baseline": str(tree_b)}),
                ("--tree", tree_mode, (False,), {"root": repo, "baseline": str(tree_b)}),
                ("--history", history_mode, (False,), {"cwd": str(repo), "baseline": str(hist_b)}))

    git("init", "-q")
    old_line = "ran on " + FORBIDDEN[2] + " once"
    put("README.md", "a readme\n")
    put("docs/old.md", "clean\n" + old_line + "\n")
    c1 = commit("c1")

    # 11. (iv) PRE-CHANGE CLEAR-PATH BASELINES PARSE AND PASS, and the writer re-emits them BYTE FOR BYTE.
    old_tree_b = (_TREE_HEADER + f"docs/old.md\t{line_sha(old_line)}\t{_FINDING_LABEL}\n").encode("utf-8")
    old_hist_b = (_HIST_HEADER + f"{c1[:12]}\tdocs/old.md\t1\n").encode("utf-8")
    old_tree, old_hist = tmp / "old-tree.tsv", tmp / "old-hist.tsv"
    old_tree.write_bytes(old_tree_b)
    old_hist.write_bytes(old_hist_b)
    empty_tree, empty_hist = tmp / "empty-tree.tsv", tmp / "empty-hist.tsv"
    empty_tree.write_bytes(_TREE_HEADER.encode("utf-8"))
    empty_hist.write_bytes(_HIST_HEADER.encode("utf-8"))
    if drive(tree_mode, False, root=repo, baseline=str(old_tree))[0] != 0:
        failures.append("(iv) a pre-change CLEAR-path tree baseline must still pass")
    if drive(history_mode, False, cwd=str(repo), baseline=str(old_hist))[0] != 0:
        failures.append("(iv) a pre-change CLEAR-path history baseline must still pass")
    if drive(tree_mode, False, root=repo, baseline=str(empty_tree))[0] != 1 or \
            drive(history_mode, False, cwd=str(repo), baseline=str(empty_hist))[0] != 1:
        failures.append("CONTROL (iv): without its clear-path row the old finding must RED, or the passes prove nothing")
    w1t, w1h = tmp / "w1-tree.tsv", tmp / "w1-hist.tsv"
    drive(tree_mode, True, root=repo, baseline=str(w1t))
    drive(history_mode, True, cwd=str(repo), baseline=str(w1h))
    if w1t.read_bytes() != old_tree_b or w1h.read_bytes() != old_hist_b:
        failures.append("(iv) with no name-bearing path the WRITERS must emit the pre-change format byte for byte")

    # 8. (i) A NEW FILE WHOSE PATH CARRIES A NAME is refused under all three arms; its CONTENT is clean, so only the
    #    path arm can fire (control first).
    put(p_bad, "clean words only\n")
    c2 = commit("c2")
    if scan_with_lines(added_rows(c1, c2, str(repo))):
        failures.append("CONTROL (i): the fixture file's CONTENT must be clean, or the line arm could be what fires")
    if p_bad not in added_paths(c1, c2, str(repo)):
        failures.append("(i) added_paths must report an ADDED path")
    for label, fn, a, kw in arms(c1, c2, old_tree, old_hist):
        rc, out = drive(fn, *a, **kw)
        if rc != 1:
            failures.append(f"(i) a new file whose PATH carries a name must be REFUSED under {label}")
        if leaks(out):
            failures.append(f"(i) the {label} refusal must not print the name")
        if d_bad not in out:
            failures.append(f"(i) the {label} refusal must name the path by its digest")

    # 9. (ii) THE SAME PATH, ACCEPTED BY A DIGEST ROW, PASSES -- hand-written rows, so the READER is tested apart
    #    from the writer.
    ok_tree, ok_hist = tmp / "ok-tree.tsv", tmp / "ok-hist.tsv"
    ok_tree.write_bytes(old_tree_b + f"{d_bad}\t{PATH_KIND}\t{PATH_LABEL}\n".encode("utf-8"))
    ok_hist.write_bytes(old_hist_b + f"{c2[:12]}\t{d_bad}\t{PATH_KIND}\n".encode("utf-8"))
    for label, fn, a, kw in arms(c1, c2, ok_tree, ok_hist):
        rc, out = drive(fn, *a, **kw)
        if rc != 0:
            failures.append(f"(ii) a name-bearing path ACCEPTED by its digest row must pass under {label}")
        if leaks(out):
            failures.append(f"(ii) the {label} pass must not print the name")

    # 10. (iii) A BASELINE WRITTEN FOR A REPO WITH A NAME-BEARING PATH CARRIES NO DECLARED NAME -- asserted over the
    #     written BYTES. The file's content now carries a name too, so the writer must emit a LINE row and a PATH
    #     row for it; the count is the control that the writer wrote about the file at all.
    put(p_bad, "clean words only\nran on " + FORBIDDEN[2] + " today\n")
    c3 = commit("c3")
    w3t, w3h = tmp / "w3-tree.tsv", tmp / "w3-hist.tsv"
    drive(tree_mode, True, root=repo, baseline=str(w3t))
    drive(history_mode, True, cwd=str(repo), baseline=str(w3h))
    for label, f in (("tree", w3t), ("history", w3h)):
        data = f.read_bytes().decode("utf-8", "replace")
        if leaks(data):
            failures.append(f"(iii) the WRITTEN {label} baseline carries a declared name (it would leak into its own repo)")
        if data.count(d_bad) != 2:
            failures.append(f"CONTROL (iii): the written {label} baseline must name the name-bearing file by digest, twice")
    if drive(tree_mode, False, root=repo, baseline=str(w3t))[0] != 0 or \
            drive(history_mode, False, cwd=str(repo), baseline=str(w3h))[0] != 0:
        failures.append("(iii) a written baseline must accept the tree and history it was written for")

    # 8b. (i) A RENAME TO a name-bearing path is refused too; 8c. a rename OUT of one is a repair, never a finding.
    (repo / p_ren).parent.mkdir(parents=True, exist_ok=True)
    os.replace(repo / "README.md", repo / p_ren)
    c4 = commit("c4")
    if p_ren not in added_paths(c3, c4, str(repo)):
        failures.append("(i) added_paths must report a RENAMED-TO path")
    for label, fn, a, kw in arms(c3, c4, w3t, w3h):
        rc, out = drive(fn, *a, **kw)
        if rc != 1:
            failures.append(f"(i) a RENAME TO a name-bearing path must be REFUSED under {label}")
        if leaks(out) or d_ren not in out:
            failures.append(f"(i) the {label} rename refusal must name the path by digest and never in clear")
    os.replace(repo / p_ren, repo / "ops" / "readme.md")
    c5 = commit("c5")
    rc, out = drive(range_mode, f"{c4}..{c5}", cwd=str(repo), baseline=str(w3t))
    if rc != 0:
        failures.append("(i) a rename OUT of a name-bearing path is a repair and must not be a finding under --range")

    # 8d. (i) A BINARY file at a name-bearing path adds NO line at all, so only a path arm that runs before the
    #     line arm's empty-rows skip can see it; and --tree must read it although its content scan skips binaries.
    w5t, w5h = tmp / "w5-tree.tsv", tmp / "w5-hist.tsv"
    drive(tree_mode, True, root=repo, baseline=str(w5t))
    drive(history_mode, True, cwd=str(repo), baseline=str(w5h))
    p_bin = "img/" + FORBIDDEN[3] + ".bin"
    (repo / "img").mkdir()
    (repo / p_bin).write_bytes(b"\x00\x01\x02")
    c6 = commit("c6")
    if added_rows(c5, c6, str(repo)):
        failures.append("CONTROL (i): a binary add must contribute NO added line, or this arm tests nothing new")
    for label, fn, a, kw in arms(c5, c6, w5t, w5h):
        rc, out = drive(fn, *a, **kw)
        if rc != 1 or leaks(out) or path_digest(p_bin) not in out:
            failures.append(f"(i) a BINARY file at a name-bearing path must be refused under {label}, by digest")


def _self_test_write_merge(failures, tmp, contextlib, io) -> None:
    """--write-baseline MUST PRESERVE WHAT A READER WROTE (systems, 2026-10-17, O83 item 13; the sibling of
    check_private_paths' item 12, saltbench #356). Both writers REGENERATED their file from the scan, so an annotation
    (a ruling, a desk row's text) was erased by the next write while every gate stayed green. The arms drive the two
    REAL write modes on a scratch repository against ANNOTATED baselines: every `#` line survives; --history is
    APPEND-ONLY (the old file is a byte prefix of the new one, a row the scan no longer sees is kept); --tree keeps its
    comments and live rows verbatim, drops a PAID row by name, and appends the new rows."""
    repo = tmp / "wm"
    repo.mkdir()
    nohooks = tmp / "no-hooks-wm"
    nm = FORBIDDEN[0]

    def git(*args) -> str:
        return _fixture_git(repo, nohooks, *args)

    git("init", "-q")
    (repo / "a.md").write_bytes(f"first {nm} line\n".encode("utf-8"))
    git("add", "-A")
    git("commit", "-q", "--no-verify", "-m", "c0")
    sha0 = git("rev-parse", "HEAD")[:12]
    (repo / "b.md").write_bytes(f"second {nm} line\n".encode("utf-8"))
    (repo / f"{nm}-notes.md").write_bytes(b"plain\n")
    git("add", "-A")
    git("commit", "-q", "--no-verify", "-m", "c1")
    note = "# ON THE CAPTAIN'S WORD -- an annotation between rows\n#   and its second line\n"
    cases = {
        "tree": (tree_mode, {"root": str(repo)},
                 f"a.md\t{line_sha(f'first {nm} line')}\t{_FINDING_LABEL}\tKEPT-FOURTH-FIELD\n",
                 "gone.md\t0000000000000000\ta paid row\n", 3),
        "history": (history_mode, {"cwd": str(repo)},
                    f"{sha0}\ta.md\t1\n", "000000000000\tgone.md\t1\n", 4),
    }
    for kind, (mode, kw, live, stale, want_rows) in cases.items():
        bpath = tmp / f"wm-{kind}.tsv"
        before = "# HEADER a reader wrote\n" + live + note + stale
        bpath.write_bytes(before.encode("utf-8"))
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            try:
                rc = mode(True, baseline=str(bpath), **kw)
            except Exception as e:  # the type only
                rc = f"raised {type(e).__name__}"
        out = buf.getvalue()
        if rc != 0:
            failures.append(f"--{kind} --write-baseline over an annotated baseline must succeed (rc {rc})")
            continue
        after = bpath.read_bytes().decode("utf-8")
        for l in before.splitlines():
            if l.startswith("#") and l not in after.splitlines():
                failures.append(f"--{kind} --write-baseline DROPPED an annotation line: {l[:50]!r}")
        if live not in after:
            failures.append(f"--{kind} --write-baseline must keep an existing live row VERBATIM")
        rows = [l for l in after.splitlines() if l.strip() and not l.startswith("#")]
        if len(rows) != want_rows:
            failures.append(f"--{kind} --write-baseline must keep the live rows and APPEND the new ones "
                            f"({len(rows)} rows, want {want_rows})")
        if kind == "tree":
            if stale in after:
                failures.append("--tree --write-baseline must DROP a paid row (it shrinks after a repair)")
            if "gone.md" not in out:
                failures.append("--tree --write-baseline must NAME each row it drops")
        elif not after.startswith(before):
            failures.append("--history --write-baseline must be APPEND-ONLY: the old file must be a byte prefix "
                            "of the new one (this list does not shrink)")
        if nm in after.lower():
            failures.append(f"--{kind} --write-baseline must never write the name in clear")


def _self_test_git_rc(failures, tmp, contextlib, io) -> None:
    """Arms 12-16: GIT'S EXIT STATUS IS READ (2026-10-07; the docstring's EXIT CODES section says why). They drive
    run_arm, the CLI's own door into every arm, and the CLI itself in a child process, on scratch repositories built
    here. Each arm was proven red first, by reverting its fix as a mutant."""
    repo = tmp / "rc"
    repo.mkdir()
    nohooks = tmp / "no-hooks"
    ok_mark = ": OK ("     # every arm's OK line carries it; no FAIL line does

    def git(*args, cwd=None) -> str:
        return _fixture_git(cwd or repo, nohooks, *args)

    def put(rel: str, text: str) -> None:
        f = repo / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_bytes(text.encode("utf-8"))

    def commit(msg: str) -> str:
        git("add", "-A")
        git("commit", "-q", "--no-verify", "-m", msg)
        return git("rev-parse", "HEAD")

    def drive(label, fn, *a, **kw):
        """rc -1 when the arm RAISED past run_arm: a crash is no exit code, and it must fail the arm that names it."""
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            try:
                rc = run_arm(label, fn, *a, **kw)
            except Exception:
                rc = -1
        return rc, buf.getvalue()

    def cli(args, cwd, script=None):
        r = subprocess.run([sys.executable, str(script or pathlib.Path(__file__).resolve())] + args,
                           cwd=cwd, capture_output=True)
        return r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace")

    def unreadable(label, rc, out) -> None:
        """Exit 3, no OK line, and none of git's own message."""
        if rc != GIT_UNREADABLE:
            failures.append(f"{label} must exit {GIT_UNREADABLE} (git could not read it), got {rc}")
        if ok_mark in out:
            failures.append(f"{label} must never print OK")
        if "fatal" in out:
            failures.append(f"{label} must withhold git's own message")

    git("init", "-q")
    put("a.md", "clean\n")
    put("HEAD", "a tracked FILE named HEAD: without `--`, `git rev-list HEAD` is ambiguous and exits 128\n")
    c1 = commit("rc1")
    git("branch", "b.md")      # a BRANCH named like the file below: without `--`, `git diff b.md ...` exits 128
    put("b.md", "clean too\n")
    c2 = commit("rc2")
    empty_tree, empty_hist = tmp / "rc-empty-tree.tsv", tmp / "rc-empty-hist.tsv"
    empty_tree.write_bytes(_TREE_HEADER.encode("utf-8"))
    empty_hist.write_bytes(_HIST_HEADER.encode("utf-8"))
    rk = {"cwd": str(repo), "baseline": str(empty_tree)}
    hk = {"cwd": str(repo), "baseline": str(empty_hist)}

    # 12. (a) AN UNRESOLVABLE RANGE FAILS: exit 3, never OK. The missing sha is shown absent first (control).
    missing = "0123456789abcdef" * 2 + "01234567"
    if subprocess.run(["git", "cat-file", "-e", missing], cwd=repo, capture_output=True).returncode == 0:
        failures.append("CONTROL (a): the 'missing' sha must not be an object in the scratch repo")
    for r in (f"{missing}..{c2}",     # the measured false green: a low end that names nothing
              f"{c1}..{missing}",     # the high end
              f"{c1}...{c2}",         # three dots: the split leaves `.<sha>`, which names nothing
              f"{c1}..",              # an empty side
              "a.md..a.md",           # FILE names: with no `--` and no resolve, git diffs the WORKING TREE, exit 0
              ""):                    # an empty range
        unreadable(f"(a) --range {r!r}", *drive(f"--range {r}", range_mode, r, **rk))
    # ... and through the CLI in a child process: the exit code a caller sees, and the empty-string trap, which
    #     used to fall through to the TREE arm and print the tree's OK.
    for r in (f"{missing}..{c2}", ""):
        unreadable(f"(a) the CLI's --range {r!r}", *cli(["--range", r], repo))

    # 13. (b) AN EMPTY BUT VALID RANGE STILL PASSES -- and so do a clean range, the hook's one-sha root form, a range
    #     whose end is a branch named like a tracked file, and --history over a tree with a file named HEAD (the
    #     last two need the `--` that ends every revision list).
    for what, fn, a, kw in (("an EMPTY valid range", range_mode, (f"{c2}..{c2}",), rk),
                            ("a clean range", range_mode, (f"{c1}..{c2}",), rk),
                            ("the one-sha root form", range_mode, (c1,), rk),
                            ("a range from a branch named like a tracked file", range_mode, (f"b.md..{c2}",), rk),
                            ("--history beside a tracked file named HEAD", history_mode, (False,), hk)):
        rc, out = drive(what, fn, *a, **kw)
        if rc != 0 or ok_mark not in out:
            failures.append(f"(b) {what} must PASS, got exit {rc}")
    rc, out = cli(["--range", f"{c2}..{c2}"], repo)
    if rc != 0 or ok_mark not in out:
        failures.append(f"(b) the CLI must pass an EMPTY but valid range, got exit {rc}")

    # 14. (c) A SHALLOW CLONE under --history still refuses BY NAME with exit 1 (not 3, never OK), and the write
    #     arm writes nothing there.
    shallow = tmp / "rc-shallow"
    git("clone", "-q", "--depth", "1", repo.as_uri(), str(shallow), cwd=tmp)
    if git("rev-parse", "--is-shallow-repository", cwd=shallow) != "true":
        failures.append("CONTROL (c): the --depth 1 clone must be shallow, or this arm proves nothing")
    rc, out = drive("--history", history_mode, False, cwd=str(shallow), baseline=str(empty_hist))
    if rc != 1 or "SHALLOW" not in out or ok_mark in out:
        failures.append(f"(c) a SHALLOW clone under --history must refuse BY NAME with exit 1, got exit {rc}")
    wb = tmp / "rc-shallow-hist.tsv"
    rc, out = drive("--history --write-baseline", history_mode, True, cwd=str(shallow), baseline=str(wb))
    if rc != 1 or "SHALLOW" not in out or wb.exists():
        failures.append(f"(c) a SHALLOW clone under --history --write-baseline must refuse by name and write "
                        f"nothing, got exit {rc}")

    # 15. (d) AN OBJECT THE REPOSITORY DOES NOT HOLD: a commit whose blob is gone. git exits 128 with EMPTY stdout,
    #     which the unchecked runner read as "this commit added nothing" -- under --range and --history, and under
    #     --history --write-baseline, which then WROTE a shorter baseline. Control first: intact, the commit's
    #     name-bearing line is SEEN (exit 1), so the arm is about the missing object and nothing else.
    put("c.md", "clean\nran on " + FORBIDDEN[2] + " once\n")
    c3 = commit("rc3")
    d_arms = (("--range", range_mode, (f"{c2}..{c3}",), rk), ("--history", history_mode, (False,), hk))
    for label, fn, a, kw in d_arms:
        if drive(label, fn, *a, **kw)[0] != 1:
            failures.append(f"CONTROL (d): intact, the planted line must be SEEN under {label} (exit 1)")
    blob = git("rev-parse", f"{c3}:c.md")
    obj, why = _ensure_loose(repo, blob)
    if obj is None:
        failures.append("CONTROL (d): the planted blob must be a LOOSE object, or this arm cannot remove it "
                        "(it could not be made loose: " + why + ")")
    else:
        os.chmod(obj, 0o644)     # git writes objects read-only, and Windows will not unlink a read-only file
        obj.unlink()
        for label, fn, a, kw in d_arms:
            unreadable(f"(d) a missing object under {label}", *drive(label, fn, *a, **kw))
        hb = tmp / "rc-hist-written.tsv"
        hb.write_bytes(b"SENTINEL\n")
        unreadable("(d) a missing object under --history --write-baseline",
                   *drive("--history --write-baseline", history_mode, True, cwd=str(repo), baseline=str(hb)))
        if hb.read_bytes() != b"SENTINEL\n":
            failures.append("(d) a missing object must not WRITE a history baseline (a short one is a quiet shrink)")

    # 16. (e) NOT A REPOSITORY: --tree's ls-files, --history's first read and --range's resolve all exit 3 -- the
    #     last over two FILES, where `git diff` outside a repository compares them and exits 0 -- and so does the
    #     CLI run from a copy of this script outside any repository (it raised a traceback's 1 at import).
    #     GIT_CEILING_DIRECTORIES stops git walking up into whatever holds the scratch directory.
    nr = tmp / "not-a-repo"
    nr.mkdir()
    (nr / "a.md").write_bytes(b"clean\n")
    loose = nr / "check_infra_names.py"
    loose.write_bytes(pathlib.Path(__file__).read_bytes())
    os.environ["GIT_CEILING_DIRECTORIES"] = os.pathsep.join(sorted({str(tmp), str(tmp.resolve())}))
    try:
        if subprocess.run(["git", "rev-parse", "--git-dir"], cwd=nr, capture_output=True).returncode == 0:
            failures.append("CONTROL (e): the scratch directory must not be inside a repository")
        tb = tmp / "rc-tree-written.tsv"
        tb.write_bytes(b"SENTINEL\n")
        unreadable("(e) --tree outside a repository",
                   *drive("--tree", tree_mode, False, root=nr, baseline=str(empty_tree)))
        unreadable("(e) --tree --write-baseline outside a repository",
                   *drive("--tree --write-baseline", tree_mode, True, root=nr, baseline=str(tb)))
        if tb.read_bytes() != b"SENTINEL\n":
            failures.append("(e) --tree --write-baseline outside a repository must write nothing")
        unreadable("(e) --history outside a repository",
                   *drive("--history", history_mode, False, cwd=str(nr), baseline=str(empty_hist)))
        unreadable("(e) --range over two FILES outside a repository",
                   *drive("--range", range_mode, "a.md..a.md", cwd=str(nr), baseline=str(empty_tree)))
        unreadable("(e) the CLI's --tree from a copy outside any repository", *cli(["--tree"], nr, loose))
    finally:
        os.environ.pop("GIT_CEILING_DIRECTORIES", None)


def _is_empty_scan_fatal(rows) -> bool:
    return len(rows) == 0


def _declared_ok(names) -> bool:
    """The forbidden set must not be SMALLER than what was reconciled against the roster."""
    return len(names) >= DECLARED_NAMES



# ---------------------------------------------------------------------------
# THE TREE RATCHET (salt, 2026-10-07, ruling 3). Mirrors check_private_paths.py --tree exactly in form:
# (file, line-sha16), a MISSING baseline with findings is UNARMED-FATAL (never "write it now"), an EMPTY
# baseline with findings reds, baseline entries no longer present are debt PAID and reported, never red.
# ---------------------------------------------------------------------------
TREE_BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "infra_names_baseline.tsv")


def line_sha(line: str) -> str:
    return hashlib.sha256(line.encode("utf-8", "replace")).hexdigest()[:16]


_TREE_HEADER = ("# infra_names_baseline.tsv -- ACCEPTED residue for the tree ratchet (check_infra_names.py --tree).\n"
                "# file<TAB>line-sha16<TAB>what. NEVER the line and NEVER the name. Shrink it after a repair with\n"
                "# --tree --write-baseline; a growth is a reviewed diff (council 2026-10-07 ruling 3: ratchet only).\n")


def load_tree_baseline(path=None):
    """set of accepted (file, line-sha16) LINE rows and (path-digest, PATH) PATH rows, or None when no baseline
    file exists. None != empty. The file field may be a clear path or its digest (file_keys reads both)."""
    try:
        with open(path or TREE_BASELINE, encoding="utf-8") as fh:
            return {tuple(l.rstrip("\n").split("\t")[:2]) for l in fh if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return None


def scan_with_lines(rows: list) -> list:
    """Like scan(), but keeps the WHOLE line (for its digest). The digest is all that ever leaves this function."""
    found = []
    for rel, text in rows:
        for i, line in enumerate(text.splitlines(), 1):
            low = line.lower()
            if any(n in low for n in FORBIDDEN):
                found.append((rel, i, line))
    return found


def tree_verdict(found: list, baseline, path_found=()) -> tuple:
    """PURE: (new, paid, unarmed_fatal). `found` is scan_with_lines output; `path_found` the tracked paths that
    carry a name; baseline is a set or None. A NEW path finding is reported as (path, 0, None)."""
    if baseline is None and (found or path_found):
        return (list(found) + [(p, 0, None) for p in path_found], set(), True)
    base = baseline or set()
    matched, new = set(), []
    for f in found:
        k = _line_row_accepts(base, f[0], line_sha(f[2]))
        if k is None:
            new.append(f)
        else:
            matched.add(k)
    for p in path_found:
        k = _path_row_accepts(base, p)
        if k is None:
            new.append((p, 0, None))
        else:
            matched.add(k)
    return (new, base - matched, False)


def merge_write_baseline(path: str, header: str, key_of, rows: list, shrink: bool) -> tuple:
    """Write a baseline WITHOUT erasing what a reader wrote in it (systems, 2026-10-17, O83 item 13; the same writer as
    check_private_paths' item 12, saltbench #356, kept standalone because each gate ships as one file).

    `rows` is [(keys, line)] for every finding the scan sees, where `keys` is EVERY key an existing row may hold for that
    finding (a file field is the clear path OR its digest, file_keys); `key_of(line)` reads an existing row's key. Every
    `#` and blank line is kept IN PLACE and every existing row VERBATIM. shrink=False (history: "does not shrink"):
    nothing is dropped, so the old file is a byte prefix of the new one. shrink=True (tree: "shrink it after a repair"):
    an existing row no finding claims is dropped and returned, so the caller NAMES it. Unclaimed findings are appended
    in the order given. A missing file gets `header`. Returns (kept, added, dropped_lines).
    ⛔ Until 2026-10-17 both writers REGENERATED the file from the scan, so a write erased every annotation.
    """
    live = set()
    for keys, _line in rows:
        live.update(keys)
    out, seen, dropped = [], set(), []
    kept = 0
    if os.path.exists(path):
        with open(path, encoding="utf-8", newline="") as fh:
            old = fh.read()
        if old and not old.endswith("\n"):
            old += "\n"
        for line in old.splitlines(keepends=True):
            body = line.rstrip("\r\n")
            if not body.strip() or body.startswith("#"):
                out.append(line)
                continue
            k = key_of(body)
            if shrink and k not in live:
                dropped.append(body)
                continue
            out.append(line)
            seen.add(k)
            kept += 1
    else:
        out.append(header)
    added = 0
    for keys, line in rows:
        if not seen.intersection(keys):
            out.append(line + "\n")
            seen.update(keys)
            added += 1
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write("".join(out))
    return kept, added, dropped


def _row_key(line: str) -> tuple:
    """An existing baseline row's key: (field, field) for a LINE row, and a PATH row keeps PATH_KIND in its key."""
    parts = line.split("\t")
    if len(parts) >= 3 and parts[2] == PATH_KIND:
        return (parts[0], parts[1], PATH_KIND)
    return tuple(parts[:2])


def tree_mode(write: bool, root=None, baseline=None) -> int:
    baseline = baseline or TREE_BASELINE
    rows = tracked_files(root)
    if _is_empty_scan_fatal(rows):
        print("FAIL: zero tracked text files -- refusing to call an empty scan clean")
        return 1
    found = scan_with_lines(rows)
    paths = tracked_paths(root)
    path_found = path_hits(paths)
    if write:
        rows = [(tuple((k, line_sha(line)) for k in file_keys(rel)),
                 f"{file_field(rel)}\t{line_sha(line)}\t{_FINDING_LABEL}")
                for rel, _i, line in sorted(found, key=lambda f: (file_field(f[0]), line_sha(f[2])))]
        rows += [(((d, PATH_KIND),), f"{d}\t{PATH_KIND}\t{PATH_LABEL}")
                 for d in sorted(path_digest(p) for p in path_found)]
        # a tree PATH row's key is (digest, PATH): two fields, the same shape load_tree_baseline reads
        kept, added, dropped = merge_write_baseline(baseline, _TREE_HEADER, lambda l: tuple(l.split("\t")[:2]),
                                                    rows, shrink=True)
        for d in dropped:
            print(f"  dropped (paid): {d}")
        print(f"check_infra_names --tree --write-baseline: {len(found)} accepted residue line(s) in "
              f"{len({r for r, _, _ in found})} file(s) in {os.path.basename(baseline)} ({kept} kept in place, "
              f"{added} appended, {len(dropped)} paid row(s) dropped; every # line kept)"
              + (f"; {len(path_found)} name-bearing path(s) written BY DIGEST" if path_found else ""))
        return 0
    new, paid, unarmed = tree_verdict(found, load_tree_baseline(baseline), path_found)
    if unarmed:
        print(f"FAIL: --tree has NO BASELINE and the tree carries {len(found) + len(path_found)} finding(s), named below. "
              f"Write the baseline deliberately with --tree --write-baseline (a reviewed act, not a fix).")
        for rel, i, _line in found:
            print(finding_line(rel, i))
        for p in path_found:
            print(path_finding_line(p))
        return 1
    new_lines = [f for f in new if f[2] is not None]
    new_paths = [f[0] for f in new if f[2] is None]
    if new_lines:
        print(f"FAIL TREE RATCHET: {len(new_lines)} infrastructure-name line(s) in the tree that "
              f"{os.path.basename(baseline)} does not accept (NEW, or an accepted line EDITED). "
              f"Drop the name from the line; do not grow the baseline for it.")
        for rel, i, _line in new_lines:
            print(finding_line(rel, i))
    if new_paths:
        print(f"FAIL TREE PATH ARM: {len(new_paths)} tracked path(s) carry an infrastructure name that "
              f"{os.path.basename(baseline)} does not accept by digest (named by digest below). "
              f"Rename the file; do not grow the baseline for it.")
        for p in new_paths:
            print(path_finding_line(p))
    if new:
        return 1
    paid_lines = {r for r in paid if r[1] != PATH_KIND}
    paid_paths = paid - paid_lines
    print(f"check_infra_names --tree: OK ({len(found)} accepted residue line(s) in "
          f"{len({r for r, _, _ in found})} file(s), all in the baseline; {len(paid_lines)} baseline entr"
          f"{'y' if len(paid_lines) == 1 else 'ies'} no longer present"
          + (" -- debt paid; shrink the baseline with --tree --write-baseline" if paid_lines else "") + "). 0 NEW."
          + f" PATH ARM: {len(paths)} tracked path(s) read, {len(path_found)} carry a name, all accepted by digest"
          + (f"; {len(paid_paths)} path row(s) no longer present -- debt paid" if paid_paths else "") + ".")
    return 0


# ---------------------------------------------------------------------------
# ⛔⛔ THE HISTORY AND RANGE ARMS, ADDED 2026-09-11.
# Measured that night, on the helm's ruling about the SIBLING gate: this file
# had `[-h] [--self-test]` and nothing else. No range arm, no history arm, no
# message arm. It scanned the tracked TREE and had never read a single commit —
# and it is the gate on HOST AND ACCOUNT NAMES, the class the fleet has an
# explicit law about and the one that actually leaked.
#   ⇒ Measured over saltbench's 360 commits the first time this ran:
#       current tree   0 occurrences        ✅
#       history      107 occurrences in 36 commits, NONE of them still in the tree
#   ⇒ 🔑 A GATE WITH ONE ARM IS CLEAN ABOUT THE ONLY POPULATION IT CAN SEE, and
#     the tree is the population that MOVES. Everything it ever caught and
#     everything anyone ever tidied away is still in a public clone.
#
# ⛔ THE RATCHET IS NOT A REPAIR AND MUST NOT READ AS ONE. A pushed commit's
# content cannot be changed without a force-push, ruled out 08/30 and in any
# case a Captain-level call on a public repo an arXiv paper now cites. This
# freezes the population and COUNTS it. It stops tomorrow's commit and says
# nothing whatever about yesterday's.
# ---------------------------------------------------------------------------
HIST_BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "infra_names_history_baseline.tsv")
EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"


_HIST_HEADER = ("# infra_names_history_baseline.tsv -- ACCEPTED historical commits whose ADDED "
                "LINES carry an infrastructure name (check_infra_names.py --history).\n"
                "# sha<TAB>file<TAB>count. NEVER the line and NEVER the name: an excerpt would "
                "put the name into the tree, where the tree arm correctly reds on it.\n"
                "# This list does not shrink without a force-push, which is a Captain-level call "
                "on a public repo. A GROWTH is a reviewed diff.\n")


def load_hist_baseline(path=None) -> set:
    """Accepted (sha, file) LINE pairs and (sha, path-digest, PATH) PATH triples -- a triple never equals a
    pair, so the two kinds cannot accept each other's finding. An absent file is an EMPTY set, never a pass."""
    path = path or HIST_BASELINE
    out = set()
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) >= 3 and parts[2] == PATH_KIND:
                out.add((parts[0], parts[1], PATH_KIND))
            elif len(parts) >= 2:
                out.add((parts[0], parts[1]))
    return out


def _hist_line_accepted(base_set, sha: str, rel: str) -> bool:
    return any((sha, k) in base_set for k in file_keys(rel))


def _hist_path_accepted(base_set, sha: str, rel: str) -> bool:
    return (sha, path_digest(rel), PATH_KIND) in base_set


def hist_verdict(per, path_per, base_set) -> tuple:
    """PURE: (new line keys, new path keys). per: {(sha12, file): count}; path_per: {(sha12, path)}."""
    return ([k for k in sorted(per) if not _hist_line_accepted(base_set, k[0], k[1])],
            [k for k in sorted(path_per) if not _hist_path_accepted(base_set, k[0], k[1])])


def added_rows(base: str, sha: str, cwd=None) -> list:
    """(path, added text) for what this commit ADDS. A deletion is never a finding."""
    out = _git(["diff", "--unified=0", "--no-color", base, sha, "--"], cwd)
    rows, path = [], "?"
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
        elif line.startswith("+") and not line.startswith("+++"):
            rows.append((path, line[1:]))
    return rows


def added_paths(base: str, sha: str, cwd=None) -> list:
    """The paths this range or commit ADDS, COPIES TO or RENAMES TO -- the path arm's population. The same base as
    added_rows. A deletion, a modification and the OLD side of a rename are never findings: leaving is a repair."""
    out = _git(["diff", "--name-status", "-z", "-M", "--diff-filter=ACR", "--no-color", base, sha, "--"], cwd)
    toks, paths, i = out.split("\0"), [], 0
    while i < len(toks):
        st = toks[i]
        if not st:
            i += 1
            continue
        if st[0] in "RC":          # R<score> old new
            if i + 2 < len(toks):
                paths.append(toks[i + 2])
            i += 3
        else:                      # A path
            if i + 1 < len(toks):
                paths.append(toks[i + 1])
            i += 2
    return paths


def _is_shallow(cwd=None) -> bool:
    return _git(["rev-parse", "--is-shallow-repository"], cwd).strip() == "true"


def history_mode(write: bool, cwd=None, baseline=None) -> int:
    baseline = baseline or HIST_BASELINE
    # ⛔⛔ A SHALLOW CLONE FAILS, AND THIS GUARD WAS MISSING FOR ONE CI RUN.
    #   Driven, and caught only by reading the COUNT in a PASSING line rather than the
    #   colour beside it: this arm's first CI run printed
    #       check_infra_names --history: OK (1 commits scanned; 40 accepted, 0 new)
    #   while the sibling in the same workflow printed 358. The job checks out at the
    #   default depth, and without this guard a one-commit history scans the truncation
    #   and reports success -- a green that means nothing, in a gate whose whole job is
    #   to report a negative.
    #   ⇒ 🔑 THE WORKFLOW WAS ALSO FIXED (fetch-depth: 0), AND THAT IS NOT THE REPAIR.
    #     A script that depends on its caller being configured correctly has moved the
    #     guard to the one place a reader of the script cannot see it.
    if _is_shallow(cwd):
        print("FAIL: this is a SHALLOW clone. A full-history ratchet on a truncated "
              "history scans the truncation, not the history.\n"
              "      CI must check out with `fetch-depth: 0` for this job.")
        return 1
    shas = _git(["rev-list", "HEAD", "--"], cwd).split()
    if not shas:
        print("FAIL: scanned ZERO commits from HEAD. An empty scan is not a clean scan.")
        return 1
    per = {}
    path_per = set()
    total = 0
    n_paths = 0
    for sha in shas:
        parents = _git(["rev-list", "--parents", "-n", "1", sha, "--"], cwd).split()
        # ⛔ first parent, so a merge is charged for what it BRINGS, not for the
        #   whole branch; and a root commit against the empty tree, because the
        #   first commit is exactly where a pre-gate name sits.
        base = parents[1] if len(parents) > 1 else EMPTY_TREE
        # ⛔ THE PATH ARM RUNS BEFORE THE EMPTY-ROWS SKIP: a commit that adds an EMPTY file, or a binary, adds no
        #   line at all -- and its path is exactly as public as any line.
        added = added_paths(base, sha, cwd)
        n_paths += len(added)
        for p in path_hits(added):
            path_per.add((sha[:12], p))
        rows = added_rows(base, sha, cwd)
        if not rows:
            continue
        for rel, _i, _line in scan(rows):
            per.setdefault((sha[:12], rel), 0)
            per[(sha[:12], rel)] += 1
            total += 1
    if write:
        out_rows = [(tuple((k[0], f) for f in file_keys(k[1])), (k[0], file_field(k[1]), str(per[k]))) for k in per]
        out_rows += [(((sha, path_digest(p), PATH_KIND),), (sha, path_digest(p), PATH_KIND)) for sha, p in path_per]
        kept, added, _ = merge_write_baseline(baseline, _HIST_HEADER, _row_key,
                                              [(keys, "\t".join(r)) for keys, r in sorted(out_rows, key=lambda x: x[1])],
                                              shrink=False)
        print(f"check_infra_names --history --write-baseline: {len(per)} accepted (commit, file) "
              f"pair(s), {total} occurrence(s), in {os.path.basename(baseline)} (APPEND-ONLY: {kept} kept, "
              f"{added} appended; every # line kept)"
              + (f"; {len(path_per)} (commit, name-bearing path) row(s) written BY DIGEST" if path_per else ""))
        return 0
    base_set = load_hist_baseline(baseline)
    n_path_rows = sum(1 for k in base_set if len(k) == 3)
    new, new_paths = hist_verdict(per, path_per, base_set)
    if new:
        print(f"FAIL: {len(new)} NEW infrastructure-name finding(s) in history, not in "
              f"{os.path.basename(baseline)} ({len(shas)} commits scanned):")
        for sha, rel in new[:20]:
            print(f"  {sha}  {file_field(rel)}")
    if new_paths:
        print(f"FAIL HISTORY PATH ARM: {len(new_paths)} commit(s) ADD or RENAME TO a path carrying an infrastructure "
              f"name that {os.path.basename(baseline)} does not accept by digest ({len(shas)} commits scanned):")
        for sha, p in new_paths[:20]:
            print(f"  {sha}  {path_digest(p)}  ({PATH_LABEL})")
    if new or new_paths:
        return 1
    print(f"check_infra_names --history: OK ({len(shas)} commits scanned; "
          f"{len(base_set) - n_path_rows} accepted historical (commit, file) pair(s), 0 new)"
          f" PATH ARM: {n_paths} added or renamed path(s) read, {len(path_per)} carry a name, "
          f"{n_path_rows} accepted (commit, path) row(s), 0 new.")
    return 0


def range_mode(rev_range: str, cwd=None, baseline=None) -> int:
    """The arm CI runs on a push: what THIS delta adds, against nothing."""
    lo, hi = rev_range.split("..", 1) if ".." in rev_range else (EMPTY_TREE, rev_range)
    # Both ends RESOLVE before anything is diffed (EXIT CODES above): an end that names nothing raises here, and
    # so does a directory that is not a repository, where `git diff` would compare two FILES and exit 0.
    for end in (lo, hi):
        _git(["rev-parse", "--verify", "--end-of-options", end + "^{tree}"], cwd)
    rows = added_rows(lo, hi, cwd)
    paths = added_paths(lo, hi, cwd)
    found = scan_with_lines(rows)
    # the ratchet's one allowance at the delta: an added line byte-identical to a baselined line of the SAME
    # file (a verbatim move or re-add). An edited line hashes anew and is NEW. The path arm's twin: an added
    # path whose digest row is in the tree baseline (a verbatim re-add); any other name-bearing path is NEW.
    base = load_tree_baseline(baseline) or set()
    found = [f for f in found if _line_row_accepts(base, f[0], line_sha(f[2])) is None]
    path_found = [p for p in path_hits(paths) if _path_row_accepts(base, p) is None]
    for rel, i, _line in found:
        print(finding_line(rel, i))
    for p in path_found:
        print(path_finding_line(p))
    if found:
        print(f"FAIL: {len(found)} NEW infrastructure-name occurrence(s) added by {rev_range} "
              f"(ratchet: an edited line that keeps a name is new; drop the name from the line)")
    if path_found:
        print(f"FAIL: {len(path_found)} PATH(s) added or renamed to by {rev_range} carry an infrastructure name "
              f"(named by digest above). Rename the file before it is pushed: a path is history once it is.")
    if found or path_found:
        return 1
    print(f"check_infra_names --range {rev_range}: OK ({len(rows)} added lines, 0 new occurrences;"
          f" PATH ARM: {len(paths)} added or renamed path(s), 0 new)")
    return 0


def run_arm(label: str, fn, *a, **kw) -> int:
    """The CLI's one door into an arm, and the self-test's: a git call that could not read becomes exit 3 and a FAIL
    line naming the arm, the git subcommand and git's rc. Never OK, and never git's own message (it can name a path)."""
    try:
        return fn(*a, **kw)
    except GitReadError as e:
        print(f"FAIL {label}: git could not read what this arm was asked to scan ({e}). NOTHING was scanned, so "
              f"this is not a pass (exit {GIT_UNREADABLE}): an unresolvable range or object is never a clean scan. "
              f"git's own message is withheld because it can name a path; rerun that git command locally to read it.")
        return GIT_UNREADABLE


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--history", action="store_true",
                    help="ratchet: added lines of EVERY commit in history vs the committed baseline")
    ap.add_argument("--range", default=None,
                    help="scan the added lines of a git revision range (the push arm)")
    ap.add_argument("--tree", action="store_true",
                    help="ratchet: every tracked text file vs scripts/infra_names_baseline.tsv (the default)")
    ap.add_argument("--write-baseline", action="store_true",
                    help="with --history or --tree: write that arm's accepted baseline")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    # `is not None`, never truthiness: an EMPTY --range (an unset variable in a caller) used to fall through to the
    # TREE arm and print the tree's OK; now it is a range that does not resolve, and exits 3.
    if a.history and a.range is not None:
        print("FAIL: --history and --range are separate arms; run them separately so a red names its arm.")
        return 1
    if not _declared_ok(FORBIDDEN):
        print(f"FAIL: {len(FORBIDDEN)} forbidden name(s) against DECLARED_NAMES={DECLARED_NAMES} "
              f"(reconciled {DECLARED_RECONCILED}) -- a set that has shrunk is a gate that has been "
              f"quietly narrowed; refusing to scan.")
        return 1
    wb = " --write-baseline" if a.write_baseline else ""
    if a.history:
        return run_arm("--history" + wb, history_mode, a.write_baseline)
    if a.range is not None:
        return run_arm(f"--range {a.range}", range_mode, a.range)
    return run_arm("--tree" + wb, tree_mode, a.write_baseline)
    rows = tracked_files()  # unreachable in salt: the bare run IS the tree ratchet (kept so the source diff vs saltbench stays small)
    if _is_empty_scan_fatal(rows):
        print("FAIL: zero tracked text files -- refusing to call an empty scan clean")
        return 1
    found = scan(rows)
    for rel, i, _line in found:
        print(finding_line(rel, i))
    if found:
        print(f"FAIL: {len(found)} infrastructure-name occurrence(s) in {len({r for r, _, _ in found})} file(s)")
        return 1
    print(f"check_infra_names: OK ({len(rows)} tracked text files, 0 occurrences; "
          f"{len(FORBIDDEN)} names WATCHED BY NAME, reconciled against the fleet roster {DECLARED_RECONCILED} -- \n"
          f"  the count is printed so a reader can compare it against the fleet map instead of trusting the date.)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
