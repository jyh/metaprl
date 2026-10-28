#!/usr/bin/env python3
"""Council 5b ruled the firewall line at PATHS. Nothing enforced it.

WHY THIS EXISTS
---------------
On 2026-08-25 at 10:49:22 the council ruled, in the Captain's words as minuted:
**paths into the private record are forbidden on public repos; bare filenames
are softened opportunistically; role-wording is the standard.** The minute also
recorded that the CI gate for it was "booked construction" — booked, not built.

Booked is not built, and the gap was measured rather than assumed. Of the 9
commits that landed on this repository at or after that stamp, **3 carried a
path-shaped string** — one of them 1 minute 41 seconds after the ruling, and one
of them written by the seat that then built this gate. Nothing anywhere tested
for it: the sibling gate in this directory scans commit messages and file
contents for a session trailer and a chat URL, and for nothing else.

That 3-of-9 rate is the justification. A rule obeyed by remembering is obeyed
for exactly as long as it is remembered, and the first lapse arrived inside two
minutes.

⭐ **AND THE FIRST CENSUS OF THAT RATE WAS RIGHT BY ARITHMETIC AND WRONG BY
MEMBERSHIP -- WHICH IS WORSE THAN BEING WRONG.** The hand census that justified
this gate scanned COMMIT MESSAGES ONLY and named three commits. This gate, run
over the same window with both arms and the ruled definition, also finds three
-- but not the same three. One named commit drops out (its absolute path points
into a PUBLIC tool, and the ruling forbade paths into the PRIVATE record, not
absolute paths generally). One unnamed commit enters, seven minutes after the
ruling, because it added a private path into a tracked FILE, which a
message-only census is structurally blind to.

TWO INDEPENDENT ERRORS CANCELLED INTO A MATCHING COUNT. Had the totals been
compared without the membership, the agreement would have read as
corroboration of a set that was one-third wrong. A count is not a scope, and
two counts agreeing is not two measurements agreeing.

WHAT COUNTS AS THE PRIVATE RECORD
---------------------------------
Not a guess — the fleet map is the authority, and these are the roots it names
as never-public: the seat repo (PRIVATE FOREVER), the employer-lane repos, the
the private project repos (FOUR since row IB), the per-seat runtime config directories, the kit run
surface, and the fleet bus. They are assembled from parts below so that this
file's own source does not match its own patterns. That is not cleverness; a
detector whose documentation trips it is a shape this fleet has hit repeatedly,
and the sibling gate carries the same defence for the same reason.

**AND THIS FILE TRIPPED ITSELF ON ITS FIRST RUN, THREE TIMES.** The patterns
were assembled from parts, correctly -- but the PROSE explaining them spelled
two forbidden shapes out verbatim, as examples of what is forbidden. The
explanation of a rule is a carrier of the rule. Nothing here spells a forbidden
shape literally now; every example is assembled or described in words.

WHAT IS DELIBERATELY *NOT* FORBIDDEN
------------------------------------
* **A bare filename.** The ruling softens these explicitly. The bus file's bare
  name passes; the same name suffixed with a colon and a line number does not,
  because a line-anchored citation is a pointer INTO the private record's
  contents rather than a mention of its name. (Neither form is spelled out
  anywhere in this file, deliberately -- see the note on carriers below.) That
  reading is a judgement this gate makes visible rather than hides: it is a
  separate shape with its own label, so it can be struck on its own.
* **Role-wording**, which the ruling names as the standard: "the helm's brief",
  "another seat's bank", "the private record". This gate must never make the
  compliant form harder than the forbidden one.
* **Absolute paths into PUBLIC repos.** `/Users/x/projects/claude/saltworks/...`
  reveals machine layout, but the ruling forbade paths into the PRIVATE RECORD
  and said nothing about this. Measured here at the time of writing: 33 tracked
  files and 78 occurrences carry that shape. Sweeping them in would be quietly
  extending an instrument past its ruling — the exact move the same council's
  law harvest condemned ("declare an instrument's blind spot, never quietly
  extend it"). DECLARED, therefore, and left alone.

* **Wiki-style card links.** The fleet's memory cards point at one another with
  a card slug wrapped in doubled square brackets. That notation names a card in
  the private record without spelling a path, so the path patterns cannot see it
  and neither could a message-only census. The class is ruled KEEP (council
  2026-09-06), so this is a declaration and not a deferral.

      ref                            occurrences  files  distinct
      saltworks  master   d92a48a        159        60      56
      salt       main     c36096fc         2         1       2
      jas        main     6fc16192         1         1       1

  Snapshots taken 2026-09-06, not properties, and each row names its ref for the
  reason the frame block below gives: a repo does not have a count, a ref does.
  ⛔ AND THE DISCRIMINATOR, IF ONE IS EVER BUILT, MUST KEY ON THE NOTATION AND
  NEVER ON WHETHER THE LINK RESOLVES. The mirror lags the live banks and a
  renamed card stops resolving, so non-resolution is not evidence of
  non-pointer: a gate testing "does this link resolve?" goes quiet in the
  DANGEROUS direction. That is a seat's finding, not this file's, and it is
  recorded here because the next author of this section will reach for the
  resolve test first.
  ⛔ AND THE COUNTING RULE, LEARNED BY GETTING IT WRONG WHILE WRITING THIS
  PARAGRAPH. The same notation spells array-of-array types, build-manifest table
  headers and proof-assistant literals in ordinary code, so a bare count of the
  bracket shape is not a count of this class: it reads 36 in salt and 655 in jas,
  where the true figures are 2 and 1. The criterion is a HYPHENATED lower-case
  slug. Controlled against a relaxed criterion that also admits single-word
  names, the extra hits are manifest table headers and one literal -- no card
  links -- so the strict rule loses nothing at these refs. A NUMBER HERE MUST
  NAME THE OBJECT IT WAS MEASURED ON; the first draft of this bullet carried
  three figures that matched no ref of any of these repos.
  DECLARED, therefore, and left alone.

THE FRAME THIS INSTRUMENT MEASURES (it travels; it must say)
------------------------------------------------------------
This file is byte-identical in every PUBLIC repo of this fleet that carries the
firewall: salt, saltworks, jas and tt-neural-dataflow-fabric as of 2026-09-08.

⛔ THAT LIST IS A SNAPSHOT, AND ITS PREVIOUS VERSION WAS WRONG FOR TWO WEEKS IN
THE ONE DIRECTION A READER CANNOT SEE. It read "salt, saltworks and jas", and
every word of it was TRUE of the copies that existed -- while a FOURTH public
repo carried none of the layers and therefore held no copy of this sentence to
be wrong in. An enumeration of installs, written inside the thing installed,
CANNOT NAME THE PLACE IT IS ABSENT. It reads as a population and is only ever a
census of the already-compliant.
  ⇒ 🔑 SO DO NOT AUDIT COVERAGE FROM THIS LINE. The population is what the
    forge answers for public visibility (`gh repo list --visibility public`);
    this line is a claim about BYTE-IDENTITY among the copies, nothing more.
    Ported to the fourth repo 2026-09-08 by evidence (saltworks lead), desk row
    HU, after silicon and the helm measured the gap the sentence could not.

Every number below was measured by this gate, and each row NAMES ITS REF.

⛔ THE FIRST VERSION OF THIS BLOCK SAID "salt · 2142 commits · 0 findings" AND
THAT WAS MEASURED ON THE DEFAULT BRANCH ALONE. A long-lived branch of the same
repo carried ELEVEN. I NAMED A REPO WHERE I HAD MEASURED A REF -- not false,
but under-scoped, which is worse: it reads as a repo-level clean bill, and it
was quoted as a frame disclosure for four hours. A REPO DOES NOT HAVE A FINDING
COUNT; A REF DOES.

    ref                        commits  tracked  message-arm findings
    saltworks  master             2138      850  14
    salt       main               2145     1426   0
    salt       math/w1-e3-port    2579     1463   0   <- was 11; a Captain-ruled
                                                         purge cleared them
    jas        main               3192     2115   5   <- genuine, all one shape,
                                                         all predating the ruling
    tt-ndf     main  0e71905        15       32   0   <- measured at the ref the
                                                         port landed on, 09-08

These are SNAPSHOTS taken 2026-08-25, not properties. A branch that forked
before this gate landed has never been scanned end to end; if you own a
long-lived branch, one full-range run is cheap and yours to own.

No repo contains a directory whose top-level name collides with a private-record
root, checked in all three before this shipped -- a repo that did would red on
every ordinary reference to its own tree.

WHY THE SCAN IS A DELTA, NOT ALL OF HISTORY
-------------------------------------------
Measured before this gate was written, over 2127 commits and 847 tracked files:
history already carries ~15 commits and ~50 files with these shapes, all of them
predating the ruling and protected by the commencement clause (no ex post
facto). A full-history scan would therefore be permanently red, which is the
red-sweep-gets-abandoned failure the sibling workflow's own header documents and
solves the same way. The enforceable content of the ruling is **"no NEW path
into the private record enters a public repo"**, so that is what this scans:
the pushed delta's commit messages, and the delta's added/modified file lines.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import os
import hashlib
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

def self_id() -> str:
    """This file's own content hash, printed in every verdict.

    WHY. A ruling made this gate's verdict a required receipt, and the criterion
    was "the MECHANISM'S verdict". Four copies of it existed across two repos and
    two refs at that moment; had any differed, the receipt would have named four
    objects and nobody would have noticed. I checked them by hand and they
    matched -- but a receipt whose instrument must be identified BY HAND is one
    unverified step from meaningless.

    AN INSTRUMENT THAT DOES NOT NAME ITSELF MAKES EVERY RECEIPT ABOUT IT
    UNFALSIFIABLE. Now every line this tool prints carries the bytes that printed
    it, and a reader can reproduce or refute the number without trusting the run.
    """
    try:
        return hashlib.sha256(
            pathlib.Path(__file__).read_bytes()).hexdigest()[:16]
    except OSError:
        return "unreadable"


# ---------------------------------------------------------------------------
# THE PRIVATE-RECORD ROOTS. Assembled from parts so this file's own prose above
# never matches the patterns below. Verified by the self-test, which would
# otherwise pass vacuously by excluding the one file that matters.
# ---------------------------------------------------------------------------
_SEAT = "se" + "at"                    # the commons/memory-mirror repo
_EMPLOYER = ["lo" + "ca", "ho" + "ll", "pcc-" + "bios", "safe_" + "dav1d", "safe_" + "gif",
             "anu" + "bis"]   # EMPLOYER lane, commissioned at council 2026-09-09
# ⛔⛔ ROW IB — TWO PRIVATE TREES WERE UNWATCHED FOR TWO WEEKS AND THIS FILE SAID SO ON EVERY RUN.
#   Measured 2026-09-08 by evidence WITH A POSITIVE CONTROL: one synthetic commit carrying four
#   private roots, one line each. This gate CAUGHT the seat repo and an employer root (so the
#   instrument and the invocation were both fine) and PASSED CLEAN over the other two.
#   Both are PRIVATE per the fleet map; one is the tree the map calls NEVER public.
#   ⇒ 🔑 THE DISCLOSURE BELOW ("ROOTS ARE A HAND-COPIED SNAPSHOT ... Last reconciled") WAS HONEST,
#     PRINTED ON EVERY SINGLE RUN, AND NOBODY ACTIONED IT FOR TWO WEEKS. A KNOWN HOLE IS ONLY
#     BETTER THAN AN UNKNOWN ONE IF SOMEBODY IS COUNTING THE DAYS — and nothing was, because the
#     disclosure had no age, no owner and no re-measure date. It has all three now, below.
#   ⛔ Assembled from parts like every other root here: this file must not match its own patterns.
# ⛔⛔ ROW VD (2026-09-22) — TWO MORE PRIVATE-FOREVER TREES, BORN AT COUNCIL 2026-09-18, AND NO COPY OF THIS GATE
#   WATCHED EITHER FOR FOUR DAYS while the disclosure below told every run that a newly born root would not be
#   watched. Measured before this edit: no path into either had EVER reached a gated public repo (all six trees,
#   diff history and commit messages, each against a control that fired). Their names are ORDINARY WORDS, so they
#   take the durable local tier's shape (QUALIFIED forms only, below), never a bare root: one of them is every CI
#   runner's home directory. The social seat's run directory is a distinctive name and IS a root.
#   ⇒ WHAT FOUND THIS WAS NOT THE DISCLOSURE: a reader of x86lean #45's output, looking for something else.
#     The fleet side now DERIVES the population (a census of the private trees on disk, mapped by the fleet
#     map, tested against every gate's own scan()), so a birth no longer waits on this list's date.
# content + studio ADDED 2026-09-27 (fleet map bullets, born 2026-09-26; scrub-roots-census UNWATCHED 12 pairs → 0), ordinary words ⇒ qualified forms only, like home and social.
# jaguar ADDED 2026-10-09 (the private-lane tree, O63, born 2026-10-02; the Captain at council 2026-10-09, "ABS (a)": its NAME is
#   watched by the public gates, never its contents; scrub-roots-census UNWATCHED 6 pairs → 0), an ordinary word ⇒ qualified forms only.
# tutor ADDED 2026-10-20 (the coaching tree, O87, born 2026-10-19 at council ⑩; local-only; the fleet map lists it private;
#   scrub-roots-census UNWATCHED 6 pairs → 0), an ordinary word ⇒ qualified forms only.
_LOCALONLY = ["ho" + "me", "soc" + "ial", "con" + "tent", "stu" + "dio", "jag" + "uar", "tu" + "tor"]
_PRIVATE_PROJ = ["soc" + "ial-run", "si" + "la", "mor" + "pho", "eman" + "uensis", "ver" + "so"]
# ⛔⛔ ROW XK (2026-09-24) — A PRIVATE TREE THAT IS A *FAMILY*, WATCHED BY PATTERN, NEVER BY LIST. The Captain,
#   council 2026-09-23, "Yes (a)": the benchmark harness tree and every worktree of it are a PRIVATE RECORD. Its
#   worktrees are named `<tree>-<suffix>` and the family grew 22 -> 23 -> 26 in two days, so a list of names is
#   false within a day of being written. The root below matches the tree AND any `-suffix` of it. It never matches
#   the public benchmark repo, whose name is this root's prefix without the second word.
_FAMILY = ["saltbench-" + "sys" + "tems"]
_FAMILY_RE = [f + r"(?:-[A-Za-z0-9_.]+)*" for f in _FAMILY]
# ⛔⛔ THE SEGMENT SET, NOT ONE SEGMENT — AND IT WAS WRONG FOR THE WHOLE MIGRATION (row UI,
#   2026-09-20). This read `"\\.claude-" + _SEAT + "-…"` and matched the SUPERSEDED convention
#   (`.claude-<seat>-*`, the directories deleted 2026-09-15). Measured against the fleet roster's
#   config column, which is the authority, it matched 0 OF 6 real shapes — in SIX public repos,
#   while reading green throughout.
#   ⇒ 🔑 THE GATE WAS RIGHT WHEN WRITTEN AND AGED OUT FROM UNDER ITS SUBJECT.
#   The live segments are `account` and `acct`; one live seat uses the SHORT one, so a pattern
#   written from the obvious shape covers five of six and misses a real seat. The superseded
#   segment is KEPT: history still carries it and a scrub gate must see the past too.
#   ⛔ Assembled from parts, like every other root here: this file must not match its own patterns.
_CFG_SEGS = ["acc" + "ount", "ac" + "ct", _SEAT]
_CFGDIR = r"\.claude-(?:" + "|".join(_CFG_SEGS) + r")-[A-Za-z0-9_-]+"
_KIT_RE = "Documents" + r"[/" + chr(92)*2 + r"]+" + _SEAT   # separator-agnostic
_KIT = "Documents/" + _SEAT                                      # display form only
_BUS = "FLEET" + r"\.md"

# ⛔ ROW IB (b): the disclosure now carries an OWNER and a DUE DATE, because "last reconciled"
#   alone is a fact nobody is accountable for. THE FLEET MAP (~/projects/claude/CLAUDE.md) IS THE
#   AUTHORITY for this list; when a tree is born or turns private there, it belongs here.
#   ⇒ EDIT ALL THREE OF THESE TOGETHER WITH THE ROOTS ABOVE. A reconcile that moves the list and
#     not the date leaves the next reader trusting a stale stamp -- which is this row's own defect.
ROOTS_RECONCILED = "2026-10-20"
ROOTS_OWNER = "evidence (PM)"
ROOTS_REMEASURE_DUE = "2026-11-20"

_ROOTS = [_SEAT] + _EMPLOYER + _PRIVATE_PROJ
_ROOT_ALT = "|".join(_ROOTS + _FAMILY_RE)   # ROW XK: the family joins as a PATTERN

# ⛔⛔ ROW MK, 2026-09-14 — THE STAMP IS A CACHE OF A MEASUREMENT AND IT DRIFTED WHILE THE THING IT
#   CACHES DID NOT MOVE AT ALL. Measured at origin across all six gated public repos: the ROOT SETS
#   were IDENTICAL -- set-digest 603bc87c77, n=11, every repo -- and only the hand-typed date
#   differed: salt, x86lean, jas and tt-neural-dataflow-fabric at 2026-09-08, saltworks at
#   2026-09-13, and saltbench with NO STAMP CONSTANTS AT ALL -- its date inline in the disclosure
#   at 2026-09-09, with no owner and no re-measure date. The row that minted this read the STAMP
#   LINE and inferred the lists had diverged; they had not.
#   ⛔ AN EARLIER DRAFT OF THIS VERY COMMENT SAID saltbench CARRIED "no stamp at all". Measured:
#     it carries a disclosure, and that disclosure already prints len(_ROOTS) -- a DERIVED
#     quantity -- with the reason that "the count is printed so a reader can compare it against
#     the fleet map instead of trusting the date, which is the check the date alone cannot carry."
#     ⇒ saltbench had ALREADY REASONED ITS WAY TO THIS ROW'S CONCLUSION and was one step short:
#     a COUNT cannot see a SUBSTITUTION. Driven: swap one root for another and n stays 11 while
#     the digest moves 603bc87c77 -> 7d672e9b18. The digest strictly dominates the count, and
#     saltbench's count clause is KEPT rather than replaced -- a byte-identical port would have
#     deleted the destination's own repair.
#   ⇒ 🔑 A HAND-TYPED DATE CANNOT DISAGREE WITH THE ROOTS, SO IT CANNOT DETECT A REAL DIVERGENCE
#     EITHER — it is evidence about a keystroke. ROOTS_DIGEST is DERIVED from _ROOTS at import, so
#     two repos with the SAME digest are PROVABLY reconciled and two with different digests have
#     genuinely different lists. The date stays as prose for the re-measure clock and decides nothing.
#   ⛔ SORTED, so the digest is a property of the SET and not of the order somebody typed it in.
#   ⛔ AND IT CARRIES NO ROOT: a digest of the list is safe to print and to quote across repos,
#     which a diff of the list itself would not be.
# ROW VD: the ordinary-word trees are PART OF THE SET the digest certifies, or two copies that differ only in
#   them would print the same digest and read as reconciled. Marked "~" so no bare root can collide.
# ROW XK: the family is part of the certified set too, marked "*" so no literal root can collide.
ROOTS_DIGEST = hashlib.sha256("|".join(sorted(_ROOTS) + sorted("~" + w for w in _LOCALONLY)
                                       + sorted("*" + f for f in _FAMILY)).encode()).hexdigest()[:10]

# ⛔ THE DURABLE LOCAL TIER (born 2026-08-25) IS A PRIVATE ROOT WHOSE NAME IS AN
# ORDINARY WORD, so it CANNOT join _ROOTS. Measured before deciding: a bare
# root of that name matches EIGHT existing occurrences in one sibling repo --
# every one of them the standard system prefix under a slash, in a CI workflow
# and two docs. Adding it unqualified would red that repo on ordinary content,
# which is how a gate earns the reputation that gets it deleted.
#
# So it is matched ONLY in the two forms that actually identify the private
# tier rather than any directory of that name: prefixed by the fleet parent, or
# as a bare-repository name. Both assembled from parts.
# DECLARED CONSEQUENCE: an unqualified reference to a directory of that name is
# NOT caught. That is a real hole, chosen with its measurement in hand.
_LOCALWORD = "lo" + "cal"
_BS = chr(92)
_SEPCLASS = "[/" + _BS + _BS + "]+"
_FLEETPARENT = "projects" + _SEPCLASS + "claude"
_LOCAL_QUALIFIED = (_FLEETPARENT + _SEPCLASS + _LOCALWORD
                    + "(?:[/" + _BS + _BS + "]|" + _BS + "b)")
_LOCAL_BAREREPO = _LOCALWORD + _BS + ".git"
# ROW VD: the ordinary-word private trees above, in the two forms that identify them rather than any
# directory of that name — fleet-qualified, or a bare repository — exactly as the local tier is matched.
_LOCALONLY_ALT = "|".join(_LOCALONLY)
_LOCALONLY_QUALIFIED = (_FLEETPARENT + _SEPCLASS + "(?:" + _LOCALONLY_ALT + ")"
                        + "(?:[/" + _BS + _BS + "]|" + _BS + "b)")
_LOCALONLY_BAREREPO = "(?<![A-Za-z0-9_.-])(?:" + _LOCALONLY_ALT + ")" + _BS + ".git"
# The backup volume that holds it is itself a private-record location.
_BACKUPVOL = ("Volumes" + _SEPCLASS + "Content[ _]HD" + _SEPCLASS
              + "Salt" + "works")
# The NAS home the Saltworks bare repositories moved to (O54 S3, 2026-10-24) is a private-record location too: the
# same words, assembled from pieces like the line above, so the gate source never spells the path it forbids.
_NASHOME = ("vol" + "ume1" + _SEPCLASS + "git" + _SEPCLASS + "Salt" + "works")

# ⛔ ROOTLESS SHAPES — helm codebook-law 2026-08-30 (desk row J, ruled on the
# Captain's question). A path can identify the private record with NO root in
# front of it: the record's own top-level directory names, followed by a
# separator and a component, point into it from anywhere. The live specimen is
# a public commit message that transcribed two such shapes IN THE ACT of
# listing them as the defect (accepted into the message baseline by the same
# ruling). Ruled INSIDE the gate going forward; existing residue and history
# are BASELINED by the two ratchets — accepted, never rewritten — and bare
# FILENAMES stay softened exactly as the 08/25 ruling stands.
# DECLARED CONSEQUENCE: only WORD-START shapes are caught. The left guard also
# excludes '.', '/' and the backslash — unlike _INTO's, deliberately: the
# rooted forms are already _INTO's to catch, and a mid-path component of these
# ordinary names inside some public tree must not red on ordinary content.
# Checked in all three repos before this shipped: current-tree hits at the
# time of writing were 4 (salt), 3 (saltworks), 0 (jas), all pre-ruling
# residue, all baselined in the same act that landed the shape.
_ROOTLESS = ["bri" + "efs", "fle" + "et"]
_ROOTLESS_ALT = "|".join(_ROOTLESS)
_ROOTLESS_INTO = ("(?<![A-Za-z0-9_./" + _BS + _BS + "-])(?:"
                  + _ROOTLESS_ALT + ")" + _SEPCLASS + "[A-Za-z0-9_.-]+")

# A path REACHES INTO a root when the root name is followed by a separator and
# at least one more component. A bare root name in prose is not a path; the root
# plus a separator plus a component is.
#
# ⛔ THE LEFT GUARD EXCLUDES WORD CHARACTERS ONLY, AND THAT IS THE WHOLE POINT.
# The first draft also excluded `/` and `.`, to stop a root name appearing mid
# path. It did stop that -- and it stopped the ABSOLUTE form too, because an
# absolute path into the private record has a `/` immediately before the root.
# That is the single case this gate most exists for, and the first draft was
# structurally blind to it. Caught by the self-test's real-instance fixture,
# not by reading. Plural and suffixed forms are excluded by the RIGHT side
# instead: a public clone path has another letter after the root, never a
# separator, so it cannot match.
# ⛔ SEPARATOR CLASS, NOT A LITERAL SLASH -- ADDED AFTER A MEASUREMENT, 08/25.
# The first shipped version required a forward slash. Driven against six path
# shapes, FOUR WERE BLIND: a backslash-separated path, a half-normalised mixed
# path, a UNC double-backslash form, and a drive-letter absolute path. This
# fleet has a Windows seat, so those are authored shapes, not exotica.
#
# ⚠️ AND THE FIX IS IN THE PATTERN, NOT IN THE CI MATRIX. Wiring this gate onto
# a Windows runner does NOT make it see a backslash: both arms read git OBJECT
# bytes (measured -- no CR in either arm's output, and diff path headers are
# forward-slash on every platform), so the same regex over the same objects
# returns the same verdict wherever it executes. A lane changes WHERE a gate
# runs; only the pattern changes WHAT it can match.
_SEP = r"[/\\]+"
# ⛔ THE LEFT GUARD EXCLUDES A PRECEDING DOT (2026-09-09, row JC). `_ROOTLESS_INTO` has
# carried "." in its lookbehind since it was written; this pattern did not, so a DOT-PREFIXED
# directory whose name is a root matched the root itself. Measured on a live branch: 27
# findings, 23 of them a cell-local scratch dir. ⇒ A GUARD THAT REFUSES FOR A WRONG REASON IS
# HOW A GUARD GETS BYPASSED. "/" is deliberately NOT added: an absolute path carries a slash
# immediately before the root and MUST still be caught.
_INTO = rf"(?<![A-Za-z0-9_.-])(?:{_ROOT_ALT}){_SEP}[A-Za-z0-9_.-]+"
# ⛔⛔ A PATH THAT ENDS *AT* A ROOT (systems, 2026-10-16, the helm's item 11). Every pattern here wants a CHILD after the
#   root, so `<host>:~/projects/claude/<tree>-v3-export-0d97b68 (marker…)` — bench's line on saltbench #354 — passed in BOTH
#   pushes, beside two flagged twins that continued with `/harness/…`. Driven one variable at a time: the `host:` prefix is
#   irrelevant (with a trailing child the same line is caught); the missing CHILD is the whole cause.
# ✅ THE FORM: the root as the LAST segment of a path that has a path anchor before it — `~`, `<seg>:`, or at least two
#   segments — plus the scp form `<host>:<root>`. ⛔ A bare owner/repo COORDINATE (one segment, `jyh/<tree>`) is a NAME, not
#   a path: it is left alone, as the bare root in prose already is, because frozen amendments carry it and it discloses no
#   location. MEASURED before adding, across the six gated repos' tracked trees: 4 new lines here (frozen amendments,
#   accepted residue in the baseline) · 1 in saltworks · 0 in salt, jas, x86lean, tt-neural-dataflow-fabric.
_PSEG = r"[A-Za-z0-9_.$>-]+"
# kent's read of saltbench #355 (2026-10-16 23:49:51): `(?![A-Za-z0-9_.-])` read a sentence-final `.` as part of the name,
#   so `…/<root>.` hid the root; now a `.` ends the name unless a name character follows it. `./` and `../` are anchors: a
#   RELATIVE sibling-checkout path is a location, not a coordinate.
_END_NAME = r"(?![A-Za-z0-9_-])(?!\.[A-Za-z0-9_-])"
# kent's delta read of saltbench #355 (2026-10-17 00:02:08): the anchor took ZERO directories before the root, so
#   `~/bench-dry/<root>`, `host:~/dir/<root>` and `/srv/<root>` passed. An anchor (`~`, `.`, `..`, `<host>:`) now takes any
#   number of directories after it, and a LEADING `/` (not preceded by a name character) is an anchor too. `jyh/<root>` and
#   `dir/<root>` stay names.
_END_ROOT = (rf"(?:(?:~|\.\.?|{_PSEG}:~?)(?:{_SEP}{_PSEG})*|{_PSEG}{_SEP}{_PSEG}|(?<![A-Za-z0-9_.>~$:-])(?:{_SEP}{_PSEG})+)"
             rf"{_SEP}(?:{_ROOT_ALT}){_END_NAME}(?!{_SEP}[A-Za-z0-9_.-])"
             rf"|(?<=[A-Za-z0-9>_-]):(?:{_ROOT_ALT}){_END_NAME}")

FORBIDDEN = [
    (re.compile(_INTO),
     "a path into a private-record repo"),
    (re.compile(_END_ROOT),
     "a path ending AT a private-record root"),
    (re.compile(_CFGDIR),
     "a per-" + _SEAT + " runtime config directory"),
    (re.compile(rf"(?<![A-Za-z0-9_-]){_KIT_RE}(?:{_SEP}|\b)"),
     "the kit run surface"),
    (re.compile(rf"{_BUS}:\d+"),
     "a line-anchored citation into the fleet bus"),
    (re.compile(_LOCAL_QUALIFIED),
     "a path into the durable local tier"),
    (re.compile(_LOCAL_BAREREPO),
     "the durable local tier's bare repository"),
    (re.compile(_LOCALONLY_QUALIFIED),
     "a path into a local-only private tree (row VD)"),
    (re.compile(_LOCALONLY_BAREREPO),
     "a local-only private tree's bare repository (row VD)"),
    (re.compile(_BACKUPVOL),
     "the backup volume holding the private record"),
    (re.compile(_NASHOME),
     "the NAS home holding the private record"),
    (re.compile(_ROOTLESS_INTO),
     "a rootless path into the private record ("
     + _ROOTLESS[0] + "-/" + _ROOTLESS[1] + "-shape)"),
]

# Named so a future reader does not "tidy" these into the forbidden list.
PRESERVED = [
    "a bare bus filename (the ruling softens bare filenames)",
    "role-wording: the helm's brief, another " + _SEAT + "'s bank",
    "absolute paths into PUBLIC repos (declared out of scope, not overlooked)",
    "wiki-style card links (the doubled-bracket card-slug notation, ruled KEEP)",
]


# ---------------------------------------------------------------------------
# THE PRESERVED-RECORD EXEMPTION — Captain's ruling, 2026-08-25 21:1x.
#
# Five sites on one long-lived branch cite the private record and are PRESERVED
# BY RULING: they are records of observations, and a record of an observation
# must not change. The purge that cleared that branch's commit messages was
# message-only and correctly did not touch them.
#
# ⛔ WHAT WAS GRANTED IS NOT A MUTE. The ruling's words: green while each is
# preserved EXACTLY, RED THE MOMENT ONE DRIFTS -- "an exemption that just mutes
# them is not what was granted". So each site is pinned by the SHA-256 of its
# exact line, and drift-sensitivity falls out in both directions:
#
#   line EDITED   -> the new text hashes differently -> matches no pin
#                    -> it is an ORDINARY FINDING and the gate REDS. Automatic.
#   line GONE     -> the pin stops resolving at its ref -> the PIN AUDIT REDS.
#                    A delta scan alone is blind to this; that is why the audit
#                    exists as a second arm rather than a nicety.
#
# ⚠️ SCOPED BY REPO **AND** REF, and that is not caution -- it is measured. This
# file ships byte-identical to three public repos, and `docs/QUEUE.md` EXISTS IN
# TWO OF THEM AS COMPLETELY DIFFERENT FILES. A path-scoped exemption would mute
# a finding in the wrong repository, which is the adjacent-object trap wearing a
# ruling's authority. An exemption is granted for SITES, never for STRINGS.
EXEMPT = [
    {"repo": "salt", "ref": "math/w1-e3-port",
     "file": "docs/QUEUE.md",
     "sha": "3953079dbac0d60e"},
    {"repo": "salt", "ref": "math/w1-e3-port",
     "file": "docs/QUEUE.md",
     "sha": "8cf038855c616f6b"},
    {"repo": "salt", "ref": "math/w1-e3-port",
     "file": "docs/blueprints/arc.md",
     "sha": "429bb871b876cbe4"},
    {"repo": "salt", "ref": "math/w1-e3-port",
     "file": "docs/exploration/wf3-waveb-design.md",
     "sha": "4a6445edfc087eab"},
    {"repo": "salt", "ref": "math/w1-e3-port",
     "file": "docs/exploration/wf3-waveb-design.md",
     "sha": "dace3b578b8b23f8"},
]


def repo_slug() -> str:
    """This repo's name from its origin URL. EXACT match, never a substring --
    two of the three repos this file ships to differ by a suffix."""
    out = subprocess.run(["git", "config", "--get", "remote.origin.url"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace")
    url = out.stdout.strip()
    if not url:
        return ""
    return url.rstrip("/").rsplit("/", 1)[-1].removesuffix(".git")


def pins_for(slug: str, pins: list) -> list:
    """EXACT repo match, never a substring — two of the three repos this file
    ships to differ by a suffix, so a substring selector hands one repo's
    grant to another. Parameterised so the self-test drives the SELECTOR, not
    the data."""
    return [e for e in pins if e["repo"] == slug]


def active_exemptions() -> list:
    """Only the pins granted for THIS repo. Elsewhere the list is empty and the
    gate behaves as though no exemption exists -- which is correct: the ruling
    exempted five sites in one repository, not five strings everywhere."""
    return pins_for(repo_slug(), EXEMPT)


def line_sha(text: str) -> str:
    return hashlib.sha256(text.strip().encode("utf-8")).hexdigest()[:16]


def partition(findings, exempt):
    """Split findings into (violations, exempted) by BYTE-EXACT line hash.

    A finding is exempted only when its file AND the sha of its exact line both
    match a pin. One changed character produces a different sha and the finding
    survives as a violation -- which is the whole mechanism, not a side effect.
    """
    pins = {(e["file"], e["sha"]) for e in exempt}
    viol, exm = [], []
    for f in findings:
        ident, what, line = f
        (exm if (ident, line_sha(line)) in pins else viol).append(f)
    return viol, exm


def audit_pins(exempt):
    """(intact, drifted, unresolvable, local_only) -- does each pin still match?

    ⛔ RESTORED 2026-08-31 (desk row I(b)): the port that made this file
    byte-identical across the three repos took the SIBLING'S older version,
    and both documented repairs below returned as live regressions — the dead
    `ref` knob (with main() again paying it tribute) and local-ref-first
    resolution. A port inherits the destination's repairs, or it deletes
    them; the fixture arms in the self-test are what make this stick.

    THE ARM A DELTA SCAN CANNOT HAVE. If a preserved line is deleted or edited,
    a delta of the same push may show nothing at all; the pin stops resolving,
    and only a look at the tree can say so. A pin whose ref is not present in
    this checkout is UNRESOLVABLE, never 'intact' -- reported, never assumed.

    ⛔ THERE IS DELIBERATELY NO `ref` PARAMETER, AND THAT IS A REPAIR. This
    function shipped as `audit_pins(exempt, ref="HEAD")`, and `main()` dutifully
    passed it the scanned range's endpoint -- while the first statement of the
    loop below rebound that same name to None. The argument was discarded before
    it was ever read: driven with 'HEAD', a garbage ref, '' and None, all four
    returned the identical verdict. Behaviour was right (each pin is audited at
    ITS OWN ref, which is what the ruling scopes), but the signature advertised a
    scoping knob that did not exist and the call site paid it tribute, so a
    reader of `main()` came away believing this audit was bounded by the push.
    AN INTERFACE THAT ADVERTISES A CAPABILITY IT DOES NOT HAVE IS A DEAD ARM
    WEARING A DRIVEN ARM'S SIGNATURE -- the shape this file names 'decoy' three
    times, found in the second arm written to be the independent one. The
    loop-local is `found_ref` now so the shadow cannot silently return.
    """
    intact, drifted, unresolvable, local_only = [], [], [], []
    for e in exempt:
        # ⛔ THE REF AND THE FILE ARE SEPARATE QUESTIONS, AND CONFLATING THEM
        # FAILS OPEN. First draft treated "git show ref:file failed" as
        # UNRESOLVABLE, which is right when the REF is absent (this checkout
        # simply does not have that branch) and WRONG when the ref is present
        # and the FILE was deleted -- that is the preserved record being
        # destroyed, reported as "not applicable". Found by driving the arm.
        # ⛔ THE PUBLISHED REF FIRST, AND THE ORDER IS THE WHOLE POINT. The
        # ruling preserved sites on a PUBLISHED branch, so origin/<ref> is the
        # object it scoped; a bare local branch of the same name is a DIFFERENT
        # OBJECT. This resolved the bare ref first until 08/26, and both
        # directions were wrong -- measured, not reasoned: with the published
        # line DESTROYED and a stale local checkout still holding it, the gate
        # returned INTACT. A false green on a firewall gate, produced by the
        # adjacent-object trap inside the function written to defend against it.
        found_ref, from_local = None, False
        for cand, is_local in ((f'origin/{e["ref"]}', False), (e["ref"], True)):
            if subprocess.run(["git", "rev-parse", "--verify", "--quiet", cand],
                              capture_output=True).returncode == 0:
                found_ref, from_local = cand, is_local
                break
        if found_ref is None:
            unresolvable.append(e)          # the branch is not in this checkout
            continue
        if from_local:
            # Resolved, but NOT from the published record. Reported so a
            # local-only verdict cannot read as a statement about what is
            # published -- naming the object the answer is about.
            local_only.append(e)
        blob = subprocess.run(["git", "show", f'{found_ref}:{e["file"]}'],
                              capture_output=True, text=True, encoding="utf-8", errors="replace")
        if blob.returncode != 0:
            drifted.append(e)               # ref IS here and the FILE is gone
            continue
        if any(line_sha(l) == e["sha"] for l in blob.stdout.splitlines()):
            intact.append(e)
        else:
            drifted.append(e)
    return intact, drifted, unresolvable, local_only


def finding_lines(rows) -> list[str]:
    """(ident, what, line) -> the printable report, one entry per finding.

    SHARED BY EVERY FAIL PATH — armed and unarmed — so no path can regress
    into a bare count. Row I(c), 08/31: both unarmed-FAIL paths printed
    'carries N finding(s)' and N was the entire report — the reader was sent
    to arm a baseline over findings nobody had named. A count is not a scope;
    the verdict carries its scope or it carries nothing."""
    out = []
    for ident, what, line in rows:
        out.append(f"  {str(ident)[:40]}  {what}")
        if line:
            # ⛔ THE MATCHED TEXT IS NEVER PRINTED — council 2026-09-17 ⑲, desk PX.
            #    These verdicts land in PUBLIC CI logs. Until this landed the line
            #    was echoed as `line[:110]`, TRUNCATED AND NOT REDACTED, and it had
            #    already fired 25 times across 4 public repos (salt · saltworks ·
            #    saltbench · jas), 228 echoed lines, most recent the same day.
            #    The LABEL line above carries identity and shape, which is what a
            #    reader needs in order to act; the digest lets two findings be told
            #    apart, and a maintainer confirm a fix, WITHOUT republishing them.
            #    ⭐ IT ALSO CLOSES A SECOND HAZARD FOR FREE: a byte/character slice
            #    of arbitrary text can emit a PARTIAL UTF-8 CHARACTER, which makes
            #    the interactive grep refuse the WHOLE FILE and return a silent
            #    false zero. Emitting no slice at all cannot do that.
            #    ⭐ THE DIGEST IS `line_sha`, THE SAME KEY THE BASELINES AND PINS
            #    ARE STORED UNDER — so the withheld line is not merely
            #    distinguishable, it is LOOKUP-ABLE: an operator reads this
            #    digest straight into a pin or a baseline row without ever
            #    needing the text. A digest nobody can act on would have
            #    satisfied the ruling and helped no one.
            out.append(f"      text withheld — len={len(line)} line_sha={line_sha(line)}")
    return out


def commit_messages(rev_range: str) -> list[tuple[str, str]]:
    """(sha, message) for every commit in `rev_range`, newest first."""
    sep = "@@PATHCOMMIT@@"
    out = subprocess.run(
        ["git", "log", f"--format=%H%x1f%B{sep}", rev_range],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    ).stdout
    rows = []
    for chunk in out.split(sep):
        chunk = chunk.strip("\n")
        if not chunk:
            continue
        sha, _, body = chunk.partition("\x1f")
        rows.append((sha.strip(), body))
    return rows


def range_is_two_dot(rev_range: str) -> bool:
    """`git log HEAD` means every commit; `git diff HEAD` means the WORKING TREE.

    THE SAME ARGUMENT NAMES TWO DIFFERENT THINGS TO THE TWO COMMANDS THIS GATE
    RUNS, and the divergence is silent. Caught while porting: run against a
    clean clone with `--range HEAD`, the message arm scanned 2142 commits and
    the file arm scanned NOTHING -- and the summary line printed
    "0 added lines scanned", which reads as a clean measurement of a real scan.

    A zero that means "I could not look" and a zero that means "nothing was
    there" are the same number. So the file arm now declares which it is.
    """
    return ".." in rev_range


def added_lines(rev_range: str) -> list[tuple[str, str]]:
    """(path:line-ish, added text) for lines this delta ADDS to tracked files.

    WHY ADDED LINES AND NOT WHOLE FILES. The sibling trailer gate scans whole
    tracked files, and can, because its forbidden population is zero. This
    one's is not: ~50 files already carry these shapes from before the ruling.
    Scanning whole files would red on a file somebody merely touched, which
    punishes the wrong commit and teaches the gate is noise. A delta scan
    charges each commit for what it ADDS.

    A deletion is never a finding: removing a forbidden path is the repair.
    """
    out = subprocess.run(
        ["git", "diff", "--unified=0", "--no-color", rev_range],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    ).stdout
    rows: list[tuple[str, str]] = []
    path = "?"
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
        elif line.startswith("+") and not line.startswith("+++"):
            rows.append((path, line[1:]))
    return rows


def scan(rows: list[tuple[str, str]]) -> list[tuple[str, str, str]]:
    """(id, what, line) for every violation found."""
    bad = []
    for ident, body in rows:
        for pattern, what in FORBIDDEN:
            m = pattern.search(body)
            if m:
                line = next((l for l in body.splitlines() if m.group(0) in l),
                            m.group(0))
                bad.append((ident, what, line.strip()))
    return bad


def _is_empty_scan_fatal(rows) -> bool:
    """The fail-closed rule, as a function so the self-test can prove it."""
    return len(rows) == 0


def is_shallow() -> bool:
    out = subprocess.run(["git", "rev-parse", "--is-shallow-repository"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace")
    return out.stdout.strip() == "true"


def self_test() -> int:
    """BOTH ARMS DRIVEN BEFORE TRUST. A planted path must FAIL; a role-worded
    message must PASS. The fixtures are the three real instances that were
    measured in this repository after the ruling — not invented shapes."""
    failures = []

    # 1. THE EMPTY SET, FIRST. A scan with nothing in it must not read as clean.
    if scan([]) != []:
        failures.append("scan([]) should find nothing to report")
    if not _is_empty_scan_fatal([]):
        failures.append("an empty scan must be FATAL, not green")

    # 2. ARM ONE — THE REAL INSTANCES. These three are verbatim fragments of
    #    commit messages that actually landed here after the ruling stamp.
    real = [
        # message arm -- the gate author's own commit, 3h26m after the ruling
        ("4787935", "AND 0 inside every .pdf in " + _SEAT + "/papers -- the control word"),
        # message arm -- 1 minute 41 seconds after the ruling
        ("5466ad9", "citations verified against " + _SEAT + "/briefs/kit-revision-0813.md"),
        # FILE arm -- 7 minutes after the ruling, and INVISIBLE to a
        # message-only census. This fixture exists because the hand census
        # missed it and the gate did not.
        # ⛔ LINE ANCHOR BLINDED 08/31 (row I(e), a sibling seat's audit): the
        # real instance carried a real line number, and this file published it
        # -- assembled parts dodge the SCANNER, not the READER, and a line
        # anchor is a pointer INTO the record's contents (this file's own
        # doctrine, above). The matched span (the path) is byte-identical, so
        # the fixture drives the same shape; only the anchor is synthetic.
        ("ee5a84a", "the council ruled this sitting (`" + _SEAT
                    + "/briefs/2026-08-19-maestro-night-bank.md:9999`)"),
        # historical, kept as the only specimen of the kit-surface shape
        ("c9d3b50", "the kit copy at ~/" + _KIT + "/bus_watch.sh"),
    ]
    for ident, text in real:
        if not scan([(ident, text)]):
            failures.append(f"real instance {ident} must be caught")
    # Count DISTINCT ROWS caught, never findings: one string can legitimately
    # match two shapes (an absolute kit path is also a path into a private repo),
    # and a findings-count assertion would fail on a correct gate.
    if len({b[0] for b in scan(real)}) != len(real):
        failures.append(f"all {len(real)} real instances, got "
                        f"{len({b[0] for b in scan(real)})}")

    # 3. ARM ONE, continued — one planted specimen per remaining shape.
    planted = [
        ("p-emp", "see " + _EMPLOYER[0] + "/notes/x.md"),
        ("p-priv", "see " + _PRIVATE_PROJ[1] + "/design/y.md"),
        # ROW IB: the two roots this gate was blind to for 14 days. These rows are the reason
        # the absence would RED next time instead of passing clean.
        ("p-priv-ib1", "see " + _PRIVATE_PROJ[2] + "/src/ledger/x.ts"),
        ("p-priv-ib2", "see " + _PRIVATE_PROJ[3] + "/docs/y.md"),
        # ⛔⛔ THE PLANT MUST NOT SHARE A CONSTANT WITH THE PATTERN. This row read
        #   `"~/.claude-" + _SEAT + "-evidence/…"` against a pattern built from that SAME `_SEAT`,
        #   so BOTH SIDES MOVED TOGETHER and the arm matched whatever the pattern happened to be.
        #   ⇒ 🔑 IT TESTED STRING CONCATENATION, NOT THE PATTERN, AND WOULD HAVE BEEN GREEN FOR
        #     EVERY FUTURE CONVENTION TOO.
        #   ⭐ The splits below are deliberately DIFFERENT from `_CFG_SEGS`' splits ("ac"+"count"
        #     vs "acc"+"ount"), so editing one cannot silently keep the other in step. The names
        #     are SYNTHETIC — no real config directory is spelled in a public tree.
        ("p-cfg", "config lives in ~/.claude-" + "ac" + "count" + "-EXAMPLE/settings.json"),
        ("p-cfg-short", "config lives in ~/.claude-" + "a" + "cct" + "-EXAMPLE/settings.json"),
        ("p-cfg-old", "config lives in ~/.claude-" + "se" + "at" + "-EXAMPLE/settings.json"),
        # The bus-citation arm needs A line number, never THAT line number --
        # the anchor below is synthetic for the same reason as ee5a84a's.
        ("p-bus", "as minuted at " + _BUS.replace(chr(92), "") + ":99999"),
        # THE FOUR SHAPES THAT WERE BLIND UNTIL 08/25. Assembled, never spelled.
        ("p-bslash", "see " + _SEAT + chr(92) + "briefs" + chr(92) + "x.md"),
        ("p-mixed", "see " + _SEAT + chr(92) + _ROOTLESS[0] + "/x.md"),
        ("p-unc", "see " + chr(92)*2 + "host" + chr(92) + _SEAT + chr(92) + "briefs"),
        ("p-drive", "see C:" + chr(92) + "Users" + chr(92) + "j" + chr(92)
                    + _SEAT + chr(92) + "briefs" + chr(92) + "x.md"),
        # CRLF was already caught; kept as a control so a future edit cannot
        # silently lose it.
        ("p-crlf", "see " + _SEAT + "/briefs/x.md" + chr(13)),
        # THE DURABLE LOCAL TIER (root born 08/25). Only the QUALIFIED forms;
        # the bare word is the declared hole and is controlled for below.
        ("l-qual", "see projects/claude/" + _LOCALWORD + "/x.md"),
        ("l-qual-bs", "see projects" + chr(92) + "claude" + chr(92)
                      + _LOCALWORD + chr(92) + "x.md"),
        ("l-repo", "the bare repo " + _LOCALWORD + ".git"),
        ("l-vol", "/Volumes/Content HD/" + "Salt" + "works/archives"),
        # 2026-10-24 (O54 S3): the NAS home. Split differently from `_NASHOME` ("v"+"olume1") so the plant never shares a constant with the pattern.
        ("l-nas", "the bare repo on /v" + "olume1/git/" + "Salt" + "works/archives"),
        ("l-nas-host", "pushed to oto" + "rongo:/v" + "olume1/git/" + "Salt" + "works/x.git"),
        ("l-nas-bs", "see " + chr(92) + "v" + "olume1" + chr(92) + "git" + chr(92) + "Salt" + "works" + chr(92) + "x.git"),
        # ⛔⛔ ROW VD (2026-09-22): the two ordinary-word private trees born at council 2026-09-18, and the social
        #   seat's run directory. Split DIFFERENTLY from `_LOCALONLY` ("hom"+"e" vs "ho"+"me") so that editing one
        #   cannot silently keep the other in step — the plant must never share a constant with the pattern.
        ("vd-home", "see projects/claude/" + "hom" + "e" + "/docs/x.md"),
        ("vd-social", "see projects/claude/" + "so" + "cial" + "/src/x.py"),
        ("vd-social-bs", "see projects" + chr(92) + "claude" + chr(92) + "so" + "cial" + chr(92) + "x.md"),
        ("vd-home-repo", "the bare repo " + "hom" + "e" + ".git"),
        ("vd-social-repo", "pushed to Saltworks/" + "so" + "cial" + ".git"),
        # 2026-09-27: content + studio (born 2026-09-26), qualified forms only. Split differently from `_LOCALONLY`
        #   ("co"+"ntent" vs "con"+"tent") so the plant never shares a constant with the pattern.
        ("cs-content", "see projects/claude/" + "co" + "ntent" + "/docs/x.md"),
        ("cs-content-bs", "see projects" + chr(92) + "claude" + chr(92) + "co" + "ntent" + chr(92) + "x.md"),
        ("cs-content-repo", "pushed to Saltworks/" + "co" + "ntent" + ".git"),
        ("cs-studio", "see projects/claude/" + "st" + "udio" + "/src/x.py"),
        ("cs-studio-bs", "see projects" + chr(92) + "claude" + chr(92) + "st" + "udio" + chr(92) + "x.md"),
        ("cs-studio-repo", "the bare repo " + "st" + "udio" + ".git"),
        # 2026-10-09: jaguar (the private-lane tree), qualified forms only. Split differently from `_LOCALONLY`.
        ("ja-jaguar", "see projects/claude/" + "ja" + "guar" + "/notes/x.md"),
        ("ja-jaguar-bs", "see projects" + chr(92) + "claude" + chr(92) + "ja" + "guar" + chr(92) + "x.md"),
        ("ja-jaguar-repo", "pushed to Saltworks/" + "ja" + "guar" + ".git"),
        # 2026-10-20: tutor (the coaching tree), qualified forms only. Split differently from `_LOCALONLY`.
        ("tu-tutor", "see projects/claude/" + "tut" + "or" + "/log/x.md"),
        ("tu-tutor-bs", "see projects" + chr(92) + "claude" + chr(92) + "tut" + "or" + chr(92) + "x.md"),
        ("tu-tutor-repo", "pushed to Saltworks/" + "tut" + "or" + ".git"),
        ("vd-run", "receipts in ~/" + "so" + "cial-run" + "/receipts.tsv"),
        # ROW XK (2026-09-24): the family, the bare tree and three real worktree shapes. Split differently from
        #   `_FAMILY` so the plant never shares a constant with the pattern.
        ("xk-bare", "see projects/claude/" + "saltbench-sys" + "tems" + "/tasks/x.md"),
        ("xk-wt", "tools from /Users/x/" + "saltbench-sys" + "tems-v3-export-2833621" + "/harness"),
        ("xk-wt2", "scorer/walk " + "saltbench-sys" + "tems-v3-gemini-abb7829" + "/harness/systems-v3"),
        ("xk-bs", "at C:" + chr(92) + "saltbench-sys" + "tems-x86r1" + chr(92) + "t.md"),
        # ⛔ A PATH THAT ENDS *AT* A ROOT (systems, 2026-10-16, the helm's item 11; saltbench #355): saltbench #354 carried this
        #   exact line unflagged, because every pattern here wants a CHILD after the root. Split differently again.
        ("end-host", "studio_export: DONE → <the run box>:~/projects/claude/" + "saltbench-sy" + "stems-v3-export-0d97b68" + " (marker)"),
        ("end-tilde", "dest ~/projects/claude/" + "saltbench-sy" + "stems-v3-export-906775a" + " · 377 files"),
        ("end-scp", "pushed to host:" + "saltbench-sy" + "stems-v3" + " tonight"),
        ("end-url", "https://github.com/jyh/" + "se" + "at" + " is the memory mirror"),
        # kent's read of saltbench #355 (2026-10-16 23:49:51): a SENTENCE-FINAL period hid the root; a RELATIVE sibling path is a location.
        ("end-period", "the export is ~/projects/claude/" + "saltbench-sy" + "stems" + ". Next sentence"),
        ("end-dotdot", "cd ../" + "saltbench-sy" + "stems-v3" + " and build"),
        # kent's delta read of saltbench #355 (2026-10-17 00:02:08): ONE directory between the anchor and the root hid it.
        ("end-one-tilde", "dest ~/bench-dry/" + "saltbench-sy" + "stems-v3-export-0d97b68" + " (marker)"),
        ("end-one-tilde2", "dest ~/projects/" + "saltbench-sy" + "stems" + " tonight"),
        ("end-one-host", "copied to host:~/bench-dry/" + "saltbench-sy" + "stems-v3" + " and built"),
        ("end-one-abs", "dest /srv/" + "saltbench-sy" + "stems" + " on the box"),
        # ROOTLESS SHAPES (row J, 08/31). Assembled, never spelled.
        ("r-rl-b", "ruled in " + _ROOTLESS[0] + "/2026-08-30-x.md"),
        ("r-rl-f", "the row in " + _ROOTLESS[1] + "/RULING-x.md"),
        ("r-rl-bs", "see " + _ROOTLESS[1] + chr(92) + "DESK.tsv"),
    ]
    for ident, text in planted:
        if not scan([(ident, text)]):
            failures.append(f"planted shape {ident} must be caught")

    # 4. ARM TWO — THE COMPLIANT FORMS MUST PASS. A gate that reds the ruled
    #    standard is worse than no gate: it teaches people to route around it.
    clean = [
        ("c-role", "as the helm minuted in its own brief, and the maestro ruled"),
        ("c-role2", "another " + _SEAT + "'s bank carries the superseded value"),
        ("c-bare", "the bus (FLEET.md) is unversioned and outside every git tree"),
        ("c-pub", "docs/QUEUE.md and SaltWorks/Silicon/TT/info.yaml both changed"),
        ("c-pubabs", "/Users/x/projects/claude/saltworks/docs/QUEUE.md is public"),
        ("c-clone", "the clone at " + _SEAT + "s/evidence/saltworks is a PUBLIC path"),
        ("c-word", "the evidence " + _SEAT + " and the silicon " + _SEAT + " agree"),
        ("c-winpub", "C:" + chr(92) + "src" + chr(92) + "saltworks" + chr(92) + "docs"),
        ("c-plural-bs", "the clone at " + _SEAT + "s" + chr(92) + "evidence"),
        # THE DECLARED HOLE, KEPT AS A CONTROL: the ordinary word must never
        # fire, or one sibling repo reds on eight pre-existing occurrences.
        ("c-usr", "installed to /usr/" + _LOCALWORD + "/bin"),
        ("c-usrlib", "on the path /usr/" + _LOCALWORD + "/lib/python3.12"),
        ("c-localprose", _LOCALWORD + "/remote divergence was the cause"),
        # ROW VD's declared hole, kept as controls: the ordinary words must never fire unqualified.
        ("vd-c-runner", "the checkout is at /" + "home" + "/runner/work/x"),
        ("vd-c-homedir", "cd to your " + "home" + " directory and run it"),
        ("vd-c-brew", "brew installs under /opt/" + "home" + "brew/bin"),
        ("vd-c-social", "the " + "social" + " cost of a false alarm"),
        ("vd-c-mid", "docs/" + "social" + "/x.md nests a PUBLIC dir"),
        # 2026-09-27: content + studio are ordinary words and must never fire unqualified.
        ("cs-c-content", "the " + "content" + " of the file"),
        ("cs-c-content-dir", "docs/" + "content" + "/x.md nests a PUBLIC dir"),
        ("cs-c-studio", "a " + "studio" + " apartment"),
        ("cs-c-studio-dir", "open src/" + "studio" + "/main.rs in Visual " + "Studio"),
        # 2026-10-09: jaguar is an ordinary word and must never fire unqualified.
        ("ja-c-jaguar", "a " + "jaguar" + " in the rainforest"),
        ("ja-c-jaguar-dir", "docs/" + "jaguar" + "/x.md nests a PUBLIC dir"),
        # 2026-10-20: tutor is an ordinary word and must never fire unqualified.
        ("tu-c-tutor", "a maths " + "tutor" + " after school"),
        ("tu-c-tutor-dir", "docs/" + "tutor" + "/x.md nests a PUBLIC dir"),
        # ROW XK: the PUBLIC benchmark repo, and the family name in prose, must never fire.
        ("xk-c-public", "see " + "saltbench" + "/harness/systems-v3/x.md"),
        ("xk-c-prose", "the " + "saltbench-sys" + "tems" + " harness runs the cells"),
        ("xk-c-near", "a dir named " + "saltbench-sys" + "temsx" + "/x is not the tree"),
        # item 11's guard: an owner/repo COORDINATE names a repo, it is not a path, and frozen amendments carry it.
        ("end-c-coord", "repo: jyh/" + "saltbench-sy" + "stems" + "          not the public repo"),
        ("end-c-clone", "cd <a clone of jyh/" + "saltbench-sy" + "stems" + ">"),
        ("end-c-reldir", "the tree dir/" + "saltbench-sy" + "stems" + " has no anchor"),
        ("end-c-dotgit", "the bare repo ~/x/" + "saltbench-sy" + "stems" + ".git" + "x is a longer name"),
        ("c-meta", "this gate forbids paths into the private record"),
        # ROOTLESS guards: a bare name stays softened by the ruling; a MID-PATH
        # component of the same ordinary word is the declared consequence of
        # the left guard; the plain English word must never fire.
        ("c-rl-bare", "the " + _ROOTLESS[0] + " directory holds the record"),
        ("c-rl-mid", "docs/" + _ROOTLESS[0] + "/x.md nests a PUBLIC dir"),
        ("c-rl-word", "a " + _ROOTLESS[1] + " of seats sailed at dawn"),
    ]
    for ident, text in clean:
        got = scan([(ident, text)])
        if got:
            failures.append(f"compliant form {ident} must PASS, got {got[0][1]}")

    # 4c. THE PRESERVED-RECORD EXEMPTION. Byte-exactness is the whole grant,
    #     so the arm that matters is the ONE-CHARACTER change.
    if len(EXEMPT) != 5:
        failures.append(f"expected 5 pins, found {len(EXEMPT)}")
    # A line that hashes to a REAL pin cannot be constructed here, so the arms
    # are driven on a SYNTHETIC pin over a line this test controls. The real
    # pins are driven against the live branch separately, and that receipt is
    # in the commit message.
    S = "se" + "at"
    site = "see " + S + "/briefs/preserved-record-fixture.md for the verdict"
    fake = [{"repo": repo_slug() or "x", "ref": "r", "file": "docs/F.md",
             "sha": line_sha(site)}]
    found = scan([("docs/F.md", site)])
    if not found:
        failures.append("the exemption fixture must be a finding before it is exempt")
    viol, exm = partition(found, fake)
    if viol or len(exm) != 1:
        failures.append(f"an exact-match site must be EXEMPTED, got {len(viol)} viol")
    # ...and ONE CHARACTER of drift must survive as a violation.
    drift = scan([("docs/F.md", site + ".")])
    viol2, exm2 = partition(drift, fake)
    if exm2 or len(viol2) != 1:
        failures.append("a one-character drift must NOT be exempted")
    # ...and the SAME line in a DIFFERENT file must not be exempted.
    other = scan([("docs/OTHER.md", site)])
    viol3, exm3 = partition(other, fake)
    if exm3 or len(viol3) != 1:
        failures.append("an exemption is per-SITE, not per-STRING")
    # ...and with no active exemptions, nothing is muted.
    viol4, exm4 = partition(found, [])
    if exm4 or len(viol4) != 1:
        failures.append("with no active exemptions nothing may be exempted")

    # 4d. THE REPO SCOPE, WHICH HAD NO ARM AT ALL. `pins_for` promises EXACT
    #     match because two of the three repos this file ships to DIFFER BY A
    #     SUFFIX -- so a substring implementation hands one repo's grant to
    #     another, which is the adjacent-object trap wearing a ruling's
    #     authority. Driven on a FIXTURE set, so the arm does not break when
    #     the real grant changes: it is testing the selector, not the data.
    scope_pins = [{"repo": "salt", "ref": "r", "file": "f", "sha": "0" * 16},
                  {"repo": "saltworks", "ref": "r", "file": "f", "sha": "1" * 16}]
    for slug, want in (("salt", 1), ("saltworks", 1), ("jas", 0),
                       ("sal", 0), ("saltwork", 0), ("saltworks2", 0), ("", 0)):
        got = len(pins_for(slug, scope_pins))
        if got != want:
            failures.append(f"pins_for({slug!r}) must select {want}, got {got}")
    # ...and the real grant must be scoped to ONE repo, or the note printed at
    # the landing ("none are scoped here") is describing a different object.
    if len({e["repo"] for e in EXEMPT}) != 1:
        failures.append("the grant spans more than one repo; the scope note lies")

    # 4e. ⛔ audit_pins() -- THE SECOND, INDEPENDENT ARM, AND IT HAD NO TEST.
    #     Its trichotomy was driven ONCE, BY HAND, and the receipt was written
    #     into a commit message. A receipt in a commit message is not a check:
    #     it cannot fail, it does not run again, and it certifies the code as
    #     it was that afternoon. In particular the FAIL-OPEN the author found by
    #     driving it (ref PRESENT + file DELETED reported as "not applicable"
    #     instead of drift) had nothing holding it down. It does now.
    #     Driven against a REAL throwaway repository, through the SAME call
    #     shape production uses -- audit_pins(pins) with no ref argument, cwd
    #     being the repo -- so nothing here is a fixture of the test's own.
    tmp = tempfile.mkdtemp(prefix="ppgate-selftest-")
    here = os.getcwd()
    try:
        repo = os.path.join(tmp, "r")
        subprocess.run(["git", "init", "-q", "-b", "trunk", repo], capture_output=True)

        def g(*a):
            return subprocess.run(["git", "-C", repo, *a], capture_output=True,
                                  text=True, encoding="utf-8", errors="replace")

        g("config", "user.email", "selftest@example.invalid")
        g("config", "user.name", "selftest")
        g("config", "commit.gpgsign", "false")
        os.makedirs(os.path.join(repo, "docs"))
        # A PLAIN line: audit_pins HASHES, it never scans, so this fixture needs
        # no forbidden shape -- and therefore cannot make this file an instance.
        keep = "a preserved observation, recorded 2026-08-25"
        doc = os.path.join(repo, "docs", "R.md")

        def write(text):
            # newline="" is not lint-appeasement: without it this arm writes
            # CRLF on the Windows lane, and an arm whose BYTES depend on the
            # platform is not driving the same fixture everywhere.
            with open(doc, "w", encoding="utf-8", newline="") as fh:
                fh.write("preface\n" + text + "\ntrailer\n")

        write(keep)
        g("add", "-A"); g("commit", "-qm", "fixture")
        g("branch", "pres/fix")
        pin = {"repo": "x", "ref": "pres/fix", "file": "docs/R.md",
               "sha": line_sha(keep)}
        os.chdir(repo)

        def buckets(pins):
            i, d, u = audit_pins(pins)[:3]
            return len(i), len(d), len(u)

        # the detector first: an intact pin must land intact, or every red below
        # is unreadable.
        if buckets([pin]) != (1, 0, 0):
            failures.append(f"an INTACT pin must audit intact, got {buckets([pin])}")
        # a pin nobody granted must not be conjured out of the tree
        if buckets([]) != (0, 0, 0):
            failures.append("an empty grant must audit to three empty buckets")
        # ONE CHARACTER of drift on the preserved line
        write(keep + ".")
        g("add", "-A"); g("commit", "-qm", "drift"); g("branch", "-f", "pres/fix", "HEAD")
        if buckets([pin]) != (0, 1, 0):
            failures.append(f"a DRIFTED line must audit drifted, got {buckets([pin])}")
        # ⛔ THE FAIL-OPEN: the ref is PRESENT and the FILE IS GONE. That is the
        #    preserved record being destroyed; reporting it "unresolvable" reads
        #    as not-applicable and is green.
        os.remove(doc)
        g("add", "-A"); g("commit", "-qm", "delete"); g("branch", "-f", "pres/fix", "HEAD")
        if buckets([pin]) != (0, 1, 0):
            failures.append("a DELETED preserved file must be DRIFT, never "
                            f"unresolvable, got {buckets([pin])}")
        # a ref this checkout does not have is UNRESOLVABLE -- and never intact
        gone = dict(pin, ref="no/such/branch")
        if buckets([gone]) != (0, 0, 1):
            failures.append(f"an ABSENT ref must be unresolvable, got {buckets([gone])}")
        # ...and the origin/<ref> fallback must actually resolve
        head = g("rev-parse", "HEAD").stdout.strip()
        g("update-ref", "refs/remotes/origin/only-remote", head)
        write(keep)
        g("add", "-A"); g("commit", "-qm", "restore")
        g("update-ref", "refs/remotes/origin/only-remote", g("rev-parse", "HEAD").stdout.strip())
        remote_only = dict(pin, ref="only-remote")
        if buckets([remote_only]) != (1, 0, 0):
            failures.append("a pin whose ref exists only as origin/<ref> must "
                            f"resolve, got {buckets([remote_only])}")
        # 4f. ⛔ WHICH OBJECT IS THE PIN ABOUT? The ruling preserved sites on a
        #     PUBLISHED branch, so the authoritative instance of `ref` is the
        #     REMOTE one. A bare local branch of the same name is a DIFFERENT
        #     OBJECT -- the adjacent-object trap, inside the function written to
        #     defend against it -- and consulting it first produces a FALSE
        #     GREEN in the exact case that matters: the published line is
        #     destroyed, a stale local checkout still has it, the gate says
        #     intact. Driven in BOTH directions, because a precedence rule that
        #     is only tested one way is half a rule.
        div = os.path.join(tmp, "div")
        for label, local_text, origin_text, want in (
                ("published intact, local stale", keep + ".", keep, "intact"),
                ("published DESTROYED, local stale", keep, keep + ".", "drifted")):
            shutil.rmtree(div, ignore_errors=True)
            subprocess.run(["git", "init", "-q", "-b", "trunk", div], capture_output=True)

            def d(*a):
                return subprocess.run(["git", "-C", div, *a], capture_output=True,
                                      text=True, encoding="utf-8", errors="replace")

            d("config", "user.email", "selftest@example.invalid")
            d("config", "user.name", "selftest")
            d("config", "commit.gpgsign", "false")
            os.makedirs(os.path.join(div, "docs"))
            dpath = os.path.join(div, "docs", "R.md")

            def dwrite(text):
                with open(dpath, "w", encoding="utf-8", newline="") as fh:
                    fh.write("preface\n" + text + "\ntrailer\n")

            dwrite(origin_text)
            d("add", "-A"); d("commit", "-qm", "published")
            d("update-ref", "refs/remotes/origin/pres/fix",
              d("rev-parse", "HEAD").stdout.strip())
            d("checkout", "-q", "-b", "pres/fix")
            dwrite(local_text)
            d("add", "-A"); d("commit", "-qm", "local divergence")
            d("checkout", "-q", "trunk")
            dpin = {"repo": "x", "ref": "pres/fix", "file": "docs/R.md",
                    "sha": line_sha(keep)}
            os.chdir(div)
            i2, d2, u2 = audit_pins([dpin])[:3]
            got = "intact" if i2 else "drifted" if d2 else "unresolvable"
            os.chdir(repo)
            if got != want:
                failures.append(f"{label}: the PUBLISHED ref governs -- want "
                                f"{want}, got {got}")
        shutil.rmtree(div, ignore_errors=True)

        # ...and when there IS no published ref, the local one answers and the
        # gate must SAY SO rather than let a local-only verdict read as a
        # statement about the published record.
        local_only = audit_pins([pin])[3]
        if len(local_only) != 1:
            failures.append("a pin resolved from a LOCAL ref only must be "
                            f"reported as such, got {len(local_only)}")
        if audit_pins([remote_only])[3]:
            failures.append("a pin resolved from origin/<ref> is NOT local-only")
    finally:
        os.chdir(here)
        shutil.rmtree(tmp, ignore_errors=True)

    # 5. THE ARM-COVERAGE DECLARATION. A range the file arm cannot scan must be
    #    reported as a gap, never silently as a zero.
    if range_is_two_dot("HEAD"):
        failures.append("'HEAD' must be recognised as NOT a two-dot range")
    if not range_is_two_dot("abc..HEAD"):
        failures.append("'abc..HEAD' must be recognised as a two-dot range")

    # 6. THIS FILE'S OWN SOURCE must not match. A detector that trips on its own
    #    documentation cannot be committed, and this fleet has shipped that.
    try:
        with open(__file__, encoding="utf-8") as fh:
            own = fh.read()
        hits = scan([("SELF", own)])
        if hits:
            failures.append(f"this file's own source trips the gate: {hits[0][1]}")
    except OSError:
        failures.append("could not read own source for the self-match check")

    # 7. THE MESSAGE RATCHET'S VERDICT, both arms on ONE fixture set. The
    #    function is pure so this drives the real decision, not a description
    #    of it. Good and bad arms must DIFFER on the same input.
    accepted = "a" * 40
    novel = "b" * 40
    new1, abs1 = msg_ratchet_verdict([accepted], {accepted})
    if new1:
        failures.append("a baselined sha must not be NEW")
    new2, abs2 = msg_ratchet_verdict([accepted, novel], {accepted})
    if new2 != [novel]:
        failures.append(f"a novel violating sha must be NEW, got {new2}")
    new3, abs3 = msg_ratchet_verdict([], {accepted})
    if new3 or abs3 != [accepted]:
        failures.append("an unreachable baseline entry is ABSENT, never a failure")
    # The missing-baseline distinction: None is not the empty set, and only
    # None-with-findings is the unarmed state.
    if not _msg_unarmed_fatal(None, 1):
        failures.append("a MISSING baseline with findings must be fatal-unarmed")
    if _msg_unarmed_fatal(set(), 1):
        failures.append("an EMPTY baseline is armed; its findings red as NEW, not as unarmed")
    if _msg_unarmed_fatal(None, 0):
        failures.append("a missing baseline over a clean history is not fatal")
    # The same distinction on the TREE side, which carried set() for both states
    # until 2026-09-21: an EMPTY-but-present baseline read as "never armed".
    if not _tree_unarmed_fatal(None, 1):
        failures.append("a MISSING tree baseline with findings must be fatal-unarmed")
    if _tree_unarmed_fatal(set(), 1):
        failures.append("an EMPTY tree baseline is armed; its findings red as NEW, not as unarmed")
    if _tree_unarmed_fatal(None, 0):
        failures.append("a missing tree baseline over a clean tree is not fatal")
    # ⛔ AND THE ARM THAT ACTUALLY COVERS THE CHANGE. The three above exercise the pure
    #    predicate, which takes the baseline as an ARGUMENT -- so reverting load_baseline to
    #    `return set()` leaves them ALL GREEN and silently restores the defect. Driven: a mutant
    #    that did exactly that passed the suite rc 0 before this arm existed.
    #    ⇒ A PREDICATE ARM TESTS THE PREDICATE; ONLY A LOADER ARM TESTS THE LOADER.
    _saved_baseline = BASELINE
    try:
        globals()["BASELINE"] = os.path.join(tempfile.mkdtemp(), "no-such-baseline.tsv")
        if load_baseline() is not None:
            failures.append("load_baseline must return None when the baseline file is MISSING, "
                            "never set() -- None and empty are different verdicts")
    finally:
        globals()["BASELINE"] = _saved_baseline

    # 8. EVERY FAIL PATH NAMES ITS FINDINGS (row I(c)). The formatter is shared
    #    by construction — armed and unarmed paths all print finding_lines() —
    #    so the arm asserts the FINDING STRING the reader will see, not an exit
    #    code: identity, shape, and excerpt must each survive into the report.
    named = finding_lines([("cafe" * 10, "some shape", "the offending excerpt")])
    if not any("cafecafe" in l for l in named):
        failures.append("finding_lines must carry the finding's identity")
    if not any("some shape" in l for l in named):
        failures.append("finding_lines must carry the finding's shape")
    # ⛔ THE EXCERPT IS WITHHELD — council 2026-09-17 ⑲, desk PX: "the scrub gates
    #    print a location + digest, never the matched text". These runs are PUBLIC
    #    CI logs; the echo had already fired 25 times across 4 public repos, most
    #    recently the day this landed. The LABEL line still carries identity and
    #    shape, which is what a reader needs to act.
    if any("offending excerpt" in l for l in named):
        failures.append("finding_lines must NOT echo the matched text (council ⑲)")
    # ⛔ AND A DIGEST THAT IS CONSTANT WOULD PASS THE ARM ABOVE WHILE BEING USELESS.
    #    Both arms must DIFFER: the same text must digest the same, different text
    #    must digest differently, or the field discriminates nothing.
    if not any("line_sha=" in l for l in named):
        failures.append("finding_lines must print a digest of the withheld text")
    # ⭐ AND THE DIGEST MUST BE THE PIN KEY, not merely some hash: an operator
    #    reads it straight into a baseline row. If these two ever diverge the
    #    report becomes un-actionable while still looking redacted and correct.
    if f"line_sha={line_sha('the offending excerpt')}" not in "\n".join(named):
        failures.append("the printed digest must BE line_sha(), the pin key")
    dig_a = finding_lines([("i", "w", "the offending excerpt")])[-1]
    dig_b = finding_lines([("i", "w", "a DIFFERENT offending line")])[-1]
    dig_a2 = finding_lines([("i", "w", "the offending excerpt")])[-1]
    if dig_a == dig_b:
        failures.append("two different excerpts must not produce the same digest")
    if dig_a != dig_a2:
        failures.append("the same excerpt must produce the same digest (stable)")
    if "len=" not in dig_a:
        failures.append("the digest line must carry the withheld text's length")
    if len(finding_lines([("x", "w", "")])) != 1:
        failures.append("an empty excerpt prints identity+shape alone, never a blank")

    # 9. THE HISTORY RATCHET, DRIVEN ON A REAL THROWAWAY REPOSITORY -- and the
    #    two arms that matter are DIFFERENTIAL: they assert that the two-dot
    #    audit form is BLIND to something this arm catches. An arm that only
    #    showed --history finding things would not show it was needed.
    #
    #    ⛔ THE CONTROL COMES FIRST AND IS RE-RUN AFTER EVERY MUTATION. A probe
    #    that dies between a mutate and a restore poisons every later arm with
    #    its own corruption, and the only thing that catches that is a control
    #    on the unmutated state (measured, this seat, 2026-09-09).
    tmp2 = tempfile.mkdtemp(prefix="pphist-selftest-")
    here2 = os.getcwd()
    try:
        hrepo = os.path.join(tmp2, "h")
        subprocess.run(["git", "init", "-q", "-b", "trunk", hrepo], capture_output=True)

        def h(*a):
            return subprocess.run(["git", "-C", hrepo, *a], capture_output=True,
                                  text=True, encoding="utf-8", errors="replace")

        h("config", "user.email", "selftest@example.invalid")
        h("config", "user.name", "selftest")
        h("config", "commit.gpgsign", "false")

        # Every fixture path is ASSEMBLED, never spelled -- this file must not
        # become an instance of what it detects (the doctrine at the top).
        BAD_ROOT = "cited at " + _SEAT + "/briefs/root-never-touched.md"
        BAD_TRANS = "cited at " + _SEAT + "/briefs/added-then-repaired.md"
        BAD_BRANCH = "cited at " + _SEAT + "/briefs/on-a-branch.md"
        BAD_EVIL = "cited at " + _SEAT + "/briefs/invented-by-the-merge.md"
        CLEAN = "cited as the helm's own brief, which is the ruled standard"

        def wf(name, text):
            with open(os.path.join(hrepo, name), "w", encoding="utf-8", newline="") as fh:
                fh.write(text + "\n")

        # root: a forbidden line that is NEVER TOUCHED AGAIN (blindness class b)
        wf("ROOT.md", BAD_ROOT)
        wf("W.md", CLEAN)
        h("add", "-A"); h("commit", "-qm", "root")
        root = h("rev-parse", "HEAD").stdout.strip()
        # c2 ADDS a forbidden line; c3 REPAIRS it (blindness class a)
        wf("W.md", BAD_TRANS)
        h("add", "-A"); h("commit", "-qm", "adds")
        c2 = h("rev-parse", "HEAD").stdout.strip()
        wf("W.md", CLEAN)
        h("add", "-A"); h("commit", "-qm", "repairs")
        c3 = h("rev-parse", "HEAD").stdout.strip()

        os.chdir(hrepo)

        # --- CONTROL, BEFORE ANY CLAIM: the scanner works in this repo at all.
        if not scan([("ctl", BAD_ROOT)]):
            failures.append("history selftest: the scanner does not catch its own fixture")

        # --- ARM (a) THE DIFFERENTIAL. The two-dot form over root..c3 must MISS
        #     the added-then-repaired line, and --history must CATCH it, charged
        #     to the commit that added it and not to the one that repaired it.
        twodot = {ln for _, ln in added_lines(f"{root}..{c3}")}
        if any(BAD_TRANS in ln for ln in twodot):
            failures.append("the two-dot arm was expected to be BLIND to an "
                            "added-then-repaired line; this fixture no longer "
                            "demonstrates the defect --history exists for")
        hf = history_findings()
        charged = {(sha, f) for sha, f, _, _ in hf}
        if (c2, "W.md") not in charged:
            failures.append(f"--history must charge the ADDING commit {c2[:8]} for W.md")
        if (c3, "W.md") in charged:
            failures.append("--history must not charge the REPAIRING commit")

        # --- ARM (b) THE ROOT COMMIT. The two-dot form cannot see a file that is
        #     byte-identical at both endpoints; the whole root commit is that.
        if any(BAD_ROOT in ln for ln in twodot):
            failures.append("the two-dot arm was expected to be BLIND to the root "
                            "commit's own untouched content")
        if (root, "ROOT.md") not in charged:
            failures.append("--history must charge the ROOT commit for its own content")

        # --- ARM (c) A MERGE MUST NOT BE CHARGED TWICE. The branch commit owns
        #     the line; the merge that carries it forward introduces nothing.
        h("checkout", "-q", "-b", "side", root)
        wf("S.md", BAD_BRANCH)
        h("add", "-A"); h("commit", "-qm", "branch adds")
        side = h("rev-parse", "HEAD").stdout.strip()
        h("checkout", "-q", "trunk")
        h("merge", "-q", "--no-ff", "-m", "merge side", "side")
        merge = h("rev-parse", "HEAD").stdout.strip()
        hf = history_findings()
        charged = {(sha, f) for sha, f, _, _ in hf}
        if (side, "S.md") not in charged:
            failures.append("--history must charge the BRANCH commit that added the line")
        if (merge, "S.md") in charged:
            failures.append("--history must NOT charge a merge for a line a parent "
                            "already carries -- that double-counts the debt")

        # --- ARM (d) AN EVIL MERGE **IS** CHARGED. Content in the merge and in
        #     NO parent is the merge's own, and the set rule must find it. This
        #     is why the rule is an intersection and not 'skip merges'.
        h("checkout", "-q", "-b", "side2", root)
        wf("E.md", CLEAN)
        h("add", "-A"); h("commit", "-qm", "side2")
        h("checkout", "-q", "trunk")
        h("merge", "-q", "--no-ff", "--no-commit", "side2")
        wf("E.md", BAD_EVIL)
        h("add", "-A"); h("commit", "-qm", "evil merge")
        evil = h("rev-parse", "HEAD").stdout.strip()
        hf = history_findings()
        charged = {(sha, f) for sha, f, _, _ in hf}
        if (evil, "E.md") not in charged:
            failures.append("--history must charge an EVIL MERGE for content no "
                            "parent carries")

        # --- ARM (e) THE RATCHET VERDICT ITSELF, on the real findings, using the
        #     same missing-vs-empty predicate the message arm is held to.
        allf = history_findings()
        if not _msg_unarmed_fatal(None, len(allf)):
            failures.append("a MISSING history baseline with findings must be fatal-unarmed")
        if _msg_unarmed_fatal(set(), len(allf)):
            failures.append("an EMPTY history baseline is ARMED; its findings red as NEW")
        if _msg_unarmed_fatal(None, 0):
            failures.append("a missing history baseline over a clean history is not fatal")
        keys = {history_key(sha, f, ln) for sha, f, _, ln in allf}
        if [x for x in allf if history_key(x[0], x[1], x[3]) not in keys]:
            failures.append("a baseline holding every finding must leave NOTHING new")
        one = sorted(keys)[0]
        if not [x for x in allf if history_key(x[0], x[1], x[3]) not in (keys - {one})]:
            failures.append("dropping one baseline entry must make exactly that finding NEW")

        # --- ARM (f) THE KEY MUST SEPARATE ALL THREE OF (sha, file, line).
        #     ⛔⛔ ASSERTED AGAINST LITERAL DISTINCTNESS, NOT BY RE-DERIVING THE
        #     KEY. The first version of this arm built its expectation with
        #     history_key() and then compared it with history_key(), so a
        #     break-probe that dropped the FILE from the key -- and a second that
        #     dropped the LINE -- both left the self-test GREEN. A function used
        #     on BOTH sides of a comparison cannot be tested by that comparison;
        #     it is the derivation-gate shape, and it survived one repair of this
        #     very arm before the probe caught it a second time.
        ka = history_key("s1", "a.md", "one line")
        if history_key("s1", "b.md", "one line") == ka:
            failures.append("the history key must separate two FILES -- a finding in "
                            "another file would be absolved by this baseline entry")
        if history_key("s1", "a.md", "another line") == ka:
            failures.append("the history key must separate two LINES -- one accepted "
                            "line would absolve every other line in the same file")
        if history_key("s2", "a.md", "one line") == ka:
            failures.append("the history key must separate two COMMITS -- accepting a "
                            "line in one commit would absolve it in every commit")
        if len(ka) != 3 or ka[0] != "s1" or ka[1] != "a.md":
            failures.append(f"the history key must carry (sha, file, line-digest); got {ka}")
        # --- ARM (g) THE MODE ITSELF, END TO END, ON A REAL BASELINE FILE.
        #     ⛔ ADDED BECAUSE A PROBE THAT DISABLED THE UNARMED-FATAL BRANCH
        #     INSIDE history_mode LEFT THE SELF-TEST GREEN. Arms (a)-(f) test the
        #     walk, the key and the predicate; none of them could run the VERDICT,
        #     so the verdict was the one part of this arm with no test at all.
        bfile = os.path.join(tmp2, "hist-baseline.tsv")

        def drive(*a):
            """Run the mode and keep BOTH halves of its answer. ⛔ The exit code
            alone is not the answer: UNARMED and REGRESSED both return 1, so a
            code-only assertion cannot tell them apart -- measured, by a probe
            that disabled the unarmed branch and stayed GREEN because the ratchet
            branch returned the same 1 with a different diagnosis. What a
            refusing gate SAYS is the part a reader acts on."""
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = history_mode(*a)
            return rc, buf.getvalue()

        unarmed, unarmed_said = drive(False, bfile)       # no baseline, findings exist
        drive(True, bfile)                                # record them
        armed, _ = drive(False, bfile)                    # now accepted
        wf("N.md", BAD_ROOT)
        h("add", "-A"); h("commit", "-qm", "a NEW violating commit")
        regressed, regressed_said = drive(False, bfile)   # new debt must red
        drive(True, bfile)
        reaccepted, _ = drive(False, bfile)
        if unarmed != 1:
            failures.append("history_mode with NO baseline and findings must FAIL unarmed")
        if "NO BASELINE" not in unarmed_said:
            failures.append("the UNARMED refusal must say the baseline is MISSING — it "
                            "asks for a deliberate write, where the ratchet asks for a "
                            "repair, and only the wording tells the reader which")
        if "HISTORY RATCHET" not in regressed_said:
            failures.append("the REGRESSION refusal must name the ratchet, not read as "
                            "an unarmed gate")
        if armed != 0:
            failures.append("history_mode must PASS once the baseline accepts every finding")
        if regressed != 1:
            failures.append("history_mode must FAIL on a NEW violating commit — this is "
                            "the ratchet, and without it the arm records but never gates")
        if reaccepted != 0:
            failures.append("history_mode must PASS again after the new debt is recorded")
        hist_arms = 7
    finally:
        os.chdir(here2)
        shutil.rmtree(tmp2, ignore_errors=True)

    # 12. --write-baseline MUST PRESERVE WHAT A READER WROTE (the helm's item 12, 2026-10-16 23:48:04). Until this arm,
    #     every write REGENERATED its file from the scan: `--history --write-baseline` on this repo dropped d30ef38's
    #     Captain's-word entry and row XK's text while every gate stayed green. The arm drives the three REAL write modes
    #     over a scratch repo against ANNOTATED baselines: every `#` line survives, the history and message lists are
    #     APPEND-ONLY (the old file is a byte prefix of the new one, a row the scan no longer sees is kept), and the tree
    #     list keeps its comments and live rows in place, drops a paid row BY NAME, and appends the new one.
    tmp12 = tempfile.mkdtemp()
    here12 = os.getcwd()
    saved12 = {k: globals()[k] for k in ("BASELINE", "HISTORY_BASELINE", "MSG_BASELINE")}
    try:
        r12 = os.path.join(tmp12, "r")
        os.makedirs(r12)
        os.chdir(r12)
        g12 = ["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", "init", "-q"], check=True)
        plant12 = ["see projects/claude/" + "saltbench-sys" + "tems" + "/tasks/a.md",
                   "see projects/claude/" + "saltbench-sys" + "tems" + "/tasks/b.md"]
        for i, text in enumerate(plant12):
            with open(f"f{i}.md", "w", encoding="utf-8", newline="") as fh:
                fh.write(text + "\n")
            subprocess.run(["git", "add", f"f{i}.md"], check=True)
            subprocess.run(g12 + ["commit", "-q", "-m", f"c{i} " + text], check=True)
        tf12 = tree_findings()
        hf12 = history_findings()
        mf12 = scan(commit_messages("HEAD"))
        if len({(f, line_sha(l)) for f, _, l in tf12}) < 2 or len({history_key(a, f, l) for a, f, _, l in hf12}) < 2 \
                or len({a for a, _, _ in mf12}) < 2:
            failures.append("write-baseline arm: the scratch repo must carry TWO findings in each population "
                            f"(tree {len(tf12)}, history {len(hf12)}, messages {len(mf12)}) or the arm tests nothing")
        else:
            t0 = sorted(tf12)[0]
            h0 = sorted(hf12)[0]
            m0 = sorted(mf12)[0]
            cases12 = {
                "tree": ("BASELINE", tree_mode,
                         f"{t0[0]}\t{line_sha(t0[2])}\t{t0[1]}\tKEPT-THIRD-FIELD\n",
                         "gone.md\t0000000000000000\ta paid row\n"),
                "history": ("HISTORY_BASELINE", history_mode,
                            f"{h0[0]}\t{h0[1]}\t{line_sha(h0[3])}\t{h0[2]}\n",
                            "0" * 40 + "\tgone.md\t0000000000000000\ta row the scan no longer sees\n"),
                "messages": ("MSG_BASELINE", messages_mode,
                             f"{m0[0]}\t{m0[1]}\n", "1" * 40 + "\ta row the scan no longer sees\n"),
            }
            for kind, (var, mode, live, stale) in cases12.items():
                bpath = os.path.join(tmp12, kind + ".tsv")
                before = ("# HEADER a reader wrote\n" + live
                          + "# ON THE CAPTAIN'S WORD -- an annotation between rows\n#   and its second line\n"
                          + stale)
                with open(bpath, "w", encoding="utf-8", newline="") as fh:
                    fh.write(before)
                globals()[var] = bpath
                buf12 = io.StringIO()
                with contextlib.redirect_stdout(buf12):
                    rc12 = mode(True)
                after = open(bpath, encoding="utf-8").read()
                out12 = buf12.getvalue()
                if rc12 != 0:
                    failures.append(f"--{kind} --write-baseline must succeed (rc {rc12}): {out12.strip()[-160:]}")
                    continue
                for l in before.splitlines():
                    if l.startswith("#") and l not in after.splitlines():
                        failures.append(f"--{kind} --write-baseline DROPPED an annotation line: {l[:60]!r}")
                if live not in after:
                    failures.append(f"--{kind} --write-baseline must keep an existing live row VERBATIM")
                rows12 = [l for l in after.splitlines() if l.strip() and not l.startswith("#")]
                if len(rows12) < (2 if kind == "tree" else 3):
                    failures.append(f"--{kind} --write-baseline must APPEND the newly found row ({len(rows12)} rows)")
                if kind == "tree":
                    if stale in after:
                        failures.append("--tree --write-baseline must DROP a paid row (it shrinks after a repair)")
                    if "gone.md" not in out12:
                        failures.append("--tree --write-baseline must NAME each row it drops")
                elif not after.startswith(before):
                    failures.append(f"--{kind} --write-baseline must be APPEND-ONLY: the old file must be a byte "
                                    "prefix of the new one (this list does not shrink)")
    finally:
        os.chdir(here12)
        globals().update(saved12)
        shutil.rmtree(tmp12, ignore_errors=True)

    # 13. A CWD ON ANOTHER DRIVE (systems, 2026-10-17, measured on jas #503's Windows lane): arm 12's scratch repo sits under
    #     the temp dir, which is C: on a Windows runner while the checkout is D:, and os.path.relpath raises ValueError
    #     across drives. Driven here on any platform by making relpath raise: tree_rows must still return rows.
    _relpath13 = os.path.relpath

    def _cross_drive13(*a, **k):
        raise ValueError("path is on mount 'D:', start on mount 'C:'")
    os.path.relpath = _cross_drive13
    try:
        tree_rows()
    except ValueError:
        failures.append("tree_rows must survive a cwd on another drive (os.path.relpath raises across Windows drives)")
    finally:
        os.path.relpath = _relpath13

    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    if failures:
        return 1
    print(f"check_private_paths SELF-TEST [gate {self_id()}]: OK "
          f"(empty scan fatal proven FIRST; "
          f"{len(real)} real post-ruling instances caught; {len(planted)} planted "
          f"shapes caught; {len(clean)} compliant forms passed; own source clean; "
          f"message-ratchet verdict driven on both arms; pin audit driven on a "
          f"real scratch repo — trichotomy, published-ref precedence in BOTH "
          f"directions, local-only disclosure; every FAIL path NAMES findings; "
          f"{hist_arms} history-ratchet arms driven on a real scratch repo — "
          f"TWO of them DIFFERENTIAL against the two-dot form's measured "
          f"blindness, merge double-charging refused, evil merge charged)")
    return 0


# ---------------------------------------------------------------------------
# THE TREE RATCHET — added 2026-08-29 by the helm on the council's row m.
#
# WHY A SECOND ARM. The delta gate fired on FIVE consecutive pushes for one file
# (08/29 00:19-01:16 UTC) and nobody repaired it; the sixth push touched other
# files, its delta was clean, and the run went GREEN with the violation still
# in the tree. A delta gate charges the commit that ADDS a path; it cannot
# charge the tree for KEEPING one. That is the stale-known-hole shape: a fired
# gate that is not acted on is laundered by the next green.
#
# WHY NOT A WHOLE-TREE GATE. The tree carried 67 findings in 27 files on the
# day this was written, most of them line-anchored bus citations in 08/13-08/16
# ledgers that are RECORDS and were never in the ruling's scope to rewrite. A
# gate that reds on all of them would be routed around inside a day.
#
# SO: A RATCHET. `private_paths_baseline.tsv` lists the ACCEPTED residue as
# (file, line-sha16). `--tree` scans every tracked text file and REDS on any
# finding NOT in the baseline -- new residue, or residue that moved (a moved
# line hashes the same but its file changed; an edited line hashes anew).
# Baseline entries no longer present are reported as debt paid, never as a
# failure. The baseline shrinks by `--write-baseline` after a real repair; it
# grows only by the same explicit act, which is a reviewed diff, not a silent
# pass. The gate's own source is excluded (it assembles the shapes from parts
# and is self-tested for that separately).
# ---------------------------------------------------------------------------
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "private_paths_baseline.tsv")


def tree_rows(exclude_self: bool = True) -> list[tuple[str, str]]:
    """(path, line) for every line of every tracked text file."""
    out = subprocess.run(["git", "ls-files", "-z"], capture_output=True,
                         check=True).stdout.decode("utf-8", "replace")
    rows: list[tuple[str, str]] = []
    try:
        own = os.path.relpath(os.path.abspath(__file__), os.getcwd())
    except ValueError:
        # Windows: the cwd is on another drive (a self-test scratch repo under C:\\ beside a checkout on D:\\), so this
        #   file cannot be in the scanned tree and there is nothing to exclude (systems, 2026-10-17, measured on jas #503).
        own = None
    for path in out.split("\0"):
        if not path or (exclude_self and path == own):
            continue
        try:
            with open(path, "rb") as fh:
                blob = fh.read()
        except (IsADirectoryError, FileNotFoundError):
            continue
        if b"\0" in blob[:8192]:
            continue  # binary
        for line in blob.decode("utf-8", "replace").splitlines():
            rows.append((path, line))
    return rows


def load_baseline():
    """set of accepted (path, line-sha) pairs, or None when no baseline file exists.

    None and empty are DIFFERENT verdicts, exactly as in load_msg_baseline and
    load_history_baseline: a MISSING file plus findings means the ratchet was
    never armed here (arm it deliberately); an EMPTY one plus findings falls
    through to the verdict, where the finding reds as NEW.
    """
    try:
        with open(BASELINE, encoding="utf-8") as fh:
            return {tuple(l.rstrip("\n").split("\t")[:2])
                    for l in fh if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return None


def _tree_unarmed_fatal(baseline, finding_count: int) -> bool:
    """The tree twin of _msg_unarmed_fatal. None is not the empty set.

    Until this existed, load_baseline() returned set() for BOTH a missing file
    and an armed-and-clean one, so `if not base and found:` printed "--tree has
    NO BASELINE" over a baseline that was PRESENT, ARMED and deliberately EMPTY
    -- and prescribed `--tree --write-baseline`, which would have accepted the
    very findings the gate had just caught. The message was wrong and the
    remedy it printed was the one act that must not be taken.
    """
    return baseline is None and finding_count > 0


def merge_write_baseline(path: str, header: str, key_of, rows: list, shrink: bool) -> tuple:
    """Write a baseline WITHOUT erasing what a reader wrote in it (the helm's item 12, 2026-10-16).

    `rows` is [(key, line)] for every finding the scan sees; `key_of(line)` reads the same key back from an existing
    row. Every `#` line and blank line is kept IN PLACE, and every existing row is kept VERBATIM (extra fields too).
    shrink=False (history, messages: "this list does not shrink"): nothing is dropped, so the old file is a byte prefix
    of the new one. shrink=True (tree: "shrink it after a repair"): an existing row whose key the scan no longer sees
    is dropped, and returned so the caller NAMES it. New keys are appended in sorted order. A missing file gets
    `header`. Returns (kept, added, dropped_lines).
    ⛔ Until 2026-10-16 every write REGENERATED its file from the scan, so `--history --write-baseline` on saltbench
       dropped a Captain's-word entry and a desk row's text while every gate stayed green.
    """
    want = dict(rows)
    out, seen, dropped = [], set(), []
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
            if shrink and k not in want:
                dropped.append(body)
                continue
            out.append(line)
            seen.add(k)
    else:
        out.append(header)
    added = 0
    for k in sorted(want):
        if k not in seen:
            out.append(want[k] + "\n")
            seen.add(k)
            added += 1
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write("".join(out))
    return len(seen) - added, added, dropped


def tree_findings() -> list[tuple[str, str, str]]:
    return scan(tree_rows())


def tree_mode(write: bool) -> int:
    found = tree_findings()
    keys = {(f, line_sha(line)) for f, _, line in found}
    if write:
        # newline="" so a write on Windows does not emit CRLF into a byte-compared file
        # (jas's encoding-hygiene gate caught this when the ratchet was ported there: a file that
        # ships byte-identical to three repos must satisfy the STRICTEST repo's gates, not the
        # source's -- a port inherits the destination's rules, measured 08/29).
        kept, added, dropped = merge_write_baseline(
            BASELINE,
            "# private_paths_baseline.tsv -- ACCEPTED residue for the tree ratchet "
            "(check_private_paths.py --tree).\n# file<TAB>line-sha16<TAB>what. "
            "Shrink it after a repair with --tree --write-baseline; a growth is a "
            "reviewed diff.\n",
            lambda l: tuple(l.split("\t")[:2]),
            [((f, line_sha(line)), f"{f}\t{line_sha(line)}\t{what}") for f, what, line in sorted(found)],
            shrink=True)
        print(f"check_private_paths --write-baseline: {len(found)} accepted residue "
              f"line(s) in {len({f for f,_,_ in found})} file(s) in {os.path.basename(BASELINE)} "
              f"({kept} kept in place, {added} appended, {len(dropped)} paid row(s) dropped; every # line kept)")
        for d in dropped:
            print(f"  dropped (paid): {d}")
        return 0
    base = load_baseline()
    if _tree_unarmed_fatal(base, len(found)):
        print(f"FAIL [gate {self_id()}]: --tree has NO BASELINE and the tree carries "
              f"{len(found)} finding(s), NAMED below. Write the baseline deliberately "
              f"with --tree --write-baseline (a reviewed act, not a fix).\n")
        print("\n".join(finding_lines(found)))
        return 1
    if base is None:      # missing AND clean: not unarmed-fatal, and the set ops below need a set
        base = set()
    new = [f for f in found if (f[0], line_sha(f[2])) not in base]
    paid = base - keys
    if new:
        print(f"FAIL [gate {self_id()}] TREE RATCHET: {len(new)} private-record path(s) "
              f"in the tree that the baseline does not accept.\n")
        print("A delta gate fired on these (or would have) and the tree still carries")
        print("them. Rewrite as ROLE wording or a bare filename; do not add to the")
        print("baseline unless the council preserved the site.\n")
        print("\n".join(finding_lines(new)))
        return 1
    print(f"check_private_paths --tree [gate {self_id()}]: OK ({len(found)} accepted residue "
          f"line(s) in {len({f for f,_,_ in found})} file(s), all in the baseline; "
          f"{len(paid)} baseline entr{'y' if len(paid)==1 else 'ies'} no longer present"
          + (" -- debt paid; shrink the baseline with --tree --write-baseline" if paid else "")
          + "). 0 NEW residue.")
    return 0


# ---------------------------------------------------------------------------
# THE MESSAGE RATCHET — added 2026-08-30 by the helm on the council's row u.
#
# WHY A THIRD ARM. The delta gate charges the PUSH that carries a violating
# message; it cannot charge history for KEEPING one. Measured on the flagship
# repo: a merge push landed four branch commits whose messages cite the
# private record, the delta gate fired ON THAT RUN — and every later push was
# green, because the four had fallen into the next scan's BASE. Same
# laundering the tree ratchet closed for FILES, in the arm that had no
# ratchet. And a message is WORSE than a file here: a tracked file can be
# repaired, a pushed message cannot be edited without a force-push, which the
# council ruled out (08/30: ACCEPT + record, NO history rewrite).
#
# SO: A RATCHET, keyed on the one immutable identity a message has — its
# commit sha. `private_paths_message_baseline.tsv` lists the ACCEPTED
# historical commits. `--messages` scans EVERY message reachable from HEAD and
# REDS on any violating commit NOT in the baseline. Baseline entries absent
# from the scanned history are reported, never failed: a branch rooted before
# them legitimately lacks them, and after a rewrite membership—not
# existence—is the only claim the sha can carry.
#
# ⛔ THE BASELINE STORES sha + shape ONLY, NEVER THE OFFENDING LINE: a quoted
# excerpt would put the private path INTO the tree, where the tree ratchet
# (correctly) reds on it. The explanation of a rule is a carrier of the rule.
# ---------------------------------------------------------------------------
MSG_BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "private_paths_message_baseline.tsv")


def load_msg_baseline():
    """set of accepted shas, or None when no baseline file exists.

    None and empty are DIFFERENT verdicts: a missing file plus findings means
    the ratchet was never armed here (fatal, arm it deliberately); an empty
    file plus findings means the repo was measured clean and something NEW
    arrived (fatal, and the finding is the point)."""
    try:
        with open(MSG_BASELINE, encoding="utf-8") as fh:
            return {l.split("\t")[0].strip() for l in fh
                    if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return None


def msg_ratchet_verdict(found_shas, baseline):
    """(new, absent) — pure, so the self-test can drive both arms without git."""
    new = [s for s in found_shas if s not in baseline]
    absent = sorted(baseline - set(found_shas))
    return new, absent


def _msg_unarmed_fatal(baseline, finding_count: int) -> bool:
    """None is not the empty set: a MISSING baseline plus findings means the
    ratchet was never armed here (arm it deliberately); an EMPTY one plus
    findings falls through to the verdict, where the finding reds as NEW."""
    return baseline is None and finding_count > 0


def messages_mode(write: bool) -> int:
    if is_shallow():
        print("FAIL: this is a SHALLOW clone. A full-history ratchet on a "
              "truncated history scans the truncation, not the history.\n"
              "      CI must check out with `fetch-depth: 0` for this job.")
        return 1
    try:
        rows = commit_messages("HEAD")
    except subprocess.CalledProcessError as e:
        print(f"FAIL: could not read history from HEAD: {e}")
        return 1
    if _is_empty_scan_fatal(rows):
        print("FAIL: scanned ZERO commits from HEAD. An empty scan is not a "
              "clean scan — this gate refuses to report success on it.")
        return 1
    found = scan(rows)
    per_sha: dict = {}
    for sha, what, line in found:
        per_sha.setdefault(sha, (what, line))
    if write:
        # newline="" for the same reason as the tree baseline: a file shipped
        # byte-identical to three repos must satisfy the STRICTEST repo's
        # encoding gate (jas), not the source's.
        kept, added, _ = merge_write_baseline(
            MSG_BASELINE,
            "# private_paths_message_baseline.tsv -- ACCEPTED historical commits whose "
            "MESSAGES carry a private-record path (check_private_paths.py --messages).\n"
            "# sha<TAB>what. NEVER the line itself: an excerpt would put the path into "
            "the tree, where the tree ratchet reds on it.\n"
            "# A pushed message cannot be repaired without a force-push (ruled out "
            "08/30), so this list does not shrink; a growth is a reviewed diff that "
            "should be nearly impossible to justify.\n",
            lambda l: l.split("\t")[0].strip(),
            [(sha, f"{sha}\t{per_sha[sha][0]}") for sha in sorted(per_sha)],
            shrink=False)
        print(f"check_private_paths --messages --write-baseline: {len(per_sha)} accepted "
              f"commit(s) in {os.path.basename(MSG_BASELINE)} (APPEND-ONLY: {kept} kept, "
              f"{added} appended; every # line kept)")
        return 0
    base = load_msg_baseline()
    if _msg_unarmed_fatal(base, len(per_sha)):
        print(f"FAIL [gate {self_id()}]: --messages has NO BASELINE and history carries "
              f"{len(per_sha)} violating message(s), NAMED below. Arm it deliberately "
              f"with --messages --write-baseline (a reviewed act, not a fix).\n")
        print("\n".join(finding_lines(
            [(sha, per_sha[sha][0], per_sha[sha][1]) for sha in sorted(per_sha)])))
        return 1
    new, absent = msg_ratchet_verdict(list(per_sha), base or set())
    if new:
        print(f"FAIL [gate {self_id()}] MESSAGE RATCHET: {len(new)} commit message(s) "
              f"citing the private record that the baseline does not accept.\n")
        print("The delta gate charges a push once; this arm makes sure a fired-and-")
        print("unrepaired message cannot launder into the next scan's base. A pushed")
        print("message cannot be edited without a force-push — which is why the ONLY")
        print("acceptable fix is catching it BEFORE the push, and why growing the")
        print("baseline needs a council word, not a green build.\n")
        print("\n".join(finding_lines(
            [(sha, per_sha[sha][0], per_sha[sha][1]) for sha in new])))
        return 1
    print(f"check_private_paths --messages [gate {self_id()}]: OK ({len(rows)} messages "
          f"scanned from HEAD; {len(per_sha)} accepted historical commit(s), all in the "
          f"baseline; {len(absent)} baseline entr{'y' if len(absent)==1 else 'ies'} not in "
          f"this history (a branch may predate them — membership, never existence). "
          f"0 NEW violating messages.")
    return 0


# ═══════════════════════════════════════════════════════════════════════════
# ⭐⭐⭐ THE HISTORY ARM — WHAT EACH COMMIT *INTRODUCED*, WHICH NO OTHER ARM READS
#
# PORTED FROM x86lean 2026-09-10 ON THE HELM'S RULING (FLEET.md 48491666), after
# a leak path was DRIVEN that every existing arm passes:
#
#   two commits pushed together; commit 1 ADDS a private path, commit 2 REMOVES it
#     --range BASE..HEAD   rc 0   -- the NET DIFFERENCE has no such file
#     --tree               rc 0   -- the TREE has no such file
#     --history            FAIL   -- names the intermediate commit and the blob
#
# ⇒ THE BLOB IS PUSHED TO A PUBLIC REMOTE AND EVERY GATE IS GREEN. The path lives
#   only in an intermediate commit, which is the population this arm reads and the
#   one nothing else does. A clone receives it.
#
# ⛔ THE FLAG WAS NOT MERELY UNRUN HERE, IT WAS ABSENT: `argparse` rejected it, so
#   this repository's intermediate commits had never been read at all. The helm
#   measured it across the flagships -- salt, saltbench and saltworks all at zero.
#
# ⚠️ A BASELINE HERE IS ACCEPTED HISTORICAL DEBT AND MUST BE **READ, NOT COUNTED**
#   (ruling item 2). A baseline armed over an unread count converts a real leak
#   into permanent accepted residue, which is strictly worse than no arm at all.
#   A tree repair NEVER shrinks it: only a history rewrite does, and that is a
#   council act.
# ═══════════════════════════════════════════════════════════════════════════
HISTORY_BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "private_paths_history_baseline.tsv")


def empty_tree_sha() -> str:
    """Git's empty tree, ASKED FOR rather than hard-coded: the well-known
    constant is the SHA-1 value and would silently be wrong in a SHA-256
    repository -- a hard-coded hash is a bet on an object format."""
    return subprocess.run(["git", "hash-object", "-t", "tree", os.devnull],
                          capture_output=True, text=True, encoding="utf-8", errors="replace",
                          check=True).stdout.strip()


def _parse_added(diff_text: str) -> list[tuple[str, str]]:
    """(path, added text) for every `+` line of a unified diff."""
    rows: list[tuple[str, str]] = []
    path = "?"
    for line in diff_text.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
        elif line.startswith("+") and not line.startswith("+++"):
            rows.append((path, line[1:]))
    return rows


def _added_rows_between(base: str, sha: str) -> list[tuple[str, str]]:
    out = subprocess.run(["git", "diff", "--unified=0", "--no-color", base, sha],
                         capture_output=True, text=True, encoding="utf-8", errors="replace",
                         check=True).stdout
    return _parse_added(out)


def commit_introduced(sha: str, parents: list[str], empty: str) -> list[tuple[str, str]]:
    """Rows this ONE commit introduces to the history.

    Root commit: its whole content -- the case the two-dot audit form drops.
    Ordinary commit: what it adds to its parent.
    ⛔ MERGE: the INTERSECTION of the per-parent added sets, which is exactly
    the content present in the merge and in NO parent. A merge that merely
    carries a branch's line onto the trunk introduces nothing of its own and
    must not be charged for it -- charging it would count one line twice and
    inflate the debt. An 'evil merge' that invents a line IS charged, because
    no parent carries it. The rule is stated as a set operation rather than as
    'skip merges' so that the second case cannot be lost.
    """
    if not parents:
        return _added_rows_between(empty, sha)
    if len(parents) == 1:
        return _added_rows_between(parents[0], sha)
    sets = [set(_added_rows_between(p, sha)) for p in parents]
    return sorted(set.intersection(*sets))


def history_findings() -> list[tuple[str, str, str, str]]:
    """(sha, file, what, line) for every commit reachable from HEAD."""
    empty = empty_tree_sha()
    out = subprocess.run(["git", "log", "--format=%H %P", "HEAD"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace",
                         check=True).stdout
    found: list[tuple[str, str, str, str]] = []
    for entry in out.splitlines():
        parts = entry.split()
        if not parts:
            continue
        sha, parents = parts[0], parts[1:]
        for f, what, line in scan(commit_introduced(sha, parents, empty)):
            found.append((sha, f, what, line))
    return found


def load_history_baseline(path: str | None = None):
    """set of (sha, file, line-sha16), or None when no baseline file exists.

    ⛔ THE PATH IS AN ARGUMENT SO THIS ARM HAS A CALLABLE SURFACE. A break-probe
    that disabled the unarmed-fatal branch inside `history_mode` left the
    self-test GREEN, because every arm tested the PREDICATE and none of them
    could run the MODE -- the mode's only entry point wrote to a fixed path in
    this directory, which a test cannot touch. A gate whose verdict cannot be
    invoked borrows its neighbours' green.

    None is not the empty set, for the same reason the message ratchet says so:
    an EMPTY baseline is an armed statement that nothing is accepted, and a
    MISSING one is no statement at all.
    """
    try:
        with open(path or HISTORY_BASELINE, encoding="utf-8") as fh:
            return {tuple(l.rstrip("\n").split("\t")[:3])
                    for l in fh if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return None


def history_key(sha: str, f: str, line: str) -> tuple[str, str, str]:
    """The ratchet's identity for one historical finding.

    ⛔ EXTRACTED SO THE SELF-TEST DRIVES THE PRODUCTION KEY AND NOT A COPY OF
    IT. Measured 2026-09-09: the first version of arm (f) recomputed this tuple
    inside the self-test, so a break-probe that dropped the FILE from the key in
    `history_mode` left the self-test GREEN. An arm that re-derives the rule it
    is checking asserts nothing -- it is a tautology wearing a test's clothes,
    and the probe that found it was the only thing between here and shipping it.
    """
    return (sha, f, line_sha(line))


def _history_lines(found) -> list[str]:
    """Render for the shared formatter: history findings are keyed by COMMIT,
    so the identity a reader needs is the sha AND the file, never either alone."""
    return finding_lines([(f"{sha[:8]} {f}", what, line) for sha, f, what, line in found])


def history_mode(write: bool, path: str | None = None) -> int:
    target = path or HISTORY_BASELINE
    found = history_findings()
    keys = {history_key(sha, f, line) for sha, f, _, line in found}
    ncommits = len({sha for sha, _, _, _ in found})
    if write:
        kept, added, _ = merge_write_baseline(
            target,
            "# private_paths_history_baseline.tsv -- ACCEPTED HISTORICAL DEBT: content a\n"
            "# commit INTRODUCED, which every clone receives whatever the tree now says.\n"
            "# sha<TAB>file<TAB>line-sha16<TAB>what.\n"
            "# A TREE REPAIR NEVER SHRINKS THIS FILE. Only a history rewrite does, and\n"
            "# that is a council act -- so a shrink here is a diff somebody must have ruled.\n",
            lambda l: tuple(l.split("\t")[:3]),
            [(history_key(sha, f, line), f"{sha}\t{f}\t{line_sha(line)}\t{what}")
             for sha, f, what, line in sorted(found)],
            shrink=False)
        print(f"check_private_paths --history --write-baseline: {len(found)} accepted "
              f"historical finding(s) across {ncommits} commit(s) in "
              f"{os.path.basename(target)} (APPEND-ONLY: {kept} kept, {added} appended; every # line kept)")
        return 0
    base = load_history_baseline(target)
    if _msg_unarmed_fatal(base, len(found)):
        print(f"FAIL [gate {self_id()}]: --history has NO BASELINE and the history "
              f"carries {len(found)} finding(s) across {ncommits} commit(s), NAMED below.\n"
              f"Write it deliberately with --history --write-baseline (a reviewed act:\n"
              f"it records debt that CANNOT be repaired in the tree).\n")
        print("\n".join(_history_lines(found)))
        return 1
    if base is None:
        base = set()
    new = [x for x in found if history_key(x[0], x[1], x[3]) not in base]
    absent = sorted(base - keys)
    if new:
        print(f"FAIL [gate {self_id()}] HISTORY RATCHET: {len(new)} private-record "
              f"path(s) introduced by a commit the baseline does not accept.\n")
        print("⛔ A TREE REPAIR DOES NOT ANSWER THIS ARM. The blob is in the history")
        print("every clone receives. Either the commit is not yet pushed and should be")
        print("amended, or the debt is accepted by a ruling and recorded here.\n")
        print("\n".join(_history_lines(new)))
        return 1
    print(f"check_private_paths --history [gate {self_id()}]: OK ({len(found)} accepted "
          f"historical finding(s) across {ncommits} commit(s), all in the baseline; "
          f"{len(absent)} baseline entr{'y' if len(absent)==1 else 'ies'} not in this "
          f"history (a branch may predate them -- membership, never existence)). "
          f"0 NEW historical findings.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="council 5b firewall gate")
    ap.add_argument("--range", default=None,
                    help="git revision range to scan (messages + added lines)")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--tree", action="store_true",
                    help="ratchet: whole-tree residue vs the committed baseline")
    ap.add_argument("--messages", action="store_true",
                    help="ratchet: every message reachable from HEAD vs the committed baseline")
    ap.add_argument("--history", action="store_true",
                    help="ratchet: what each commit INTRODUCED (per-commit, not a net diff) "
                         "vs the committed baseline -- the arm --range cannot be")
    ap.add_argument("--write-baseline", action="store_true",
                    help="with --tree/--messages: (re)write that accepted-residue baseline")
    args = ap.parse_args()

    if sum([bool(args.tree), bool(args.messages), bool(args.history)]) > 1:
        print("FAIL: --tree and --messages are separate ratchets with separate "
              "baselines; run them as separate steps so a red names its arm.")
        return 1

    if args.tree:
        return tree_mode(args.write_baseline)

    if args.messages:
        return messages_mode(args.write_baseline)

    if args.history:
        if is_shallow():
            print("FAIL: this is a SHALLOW clone. --history walks every commit "
                  "reachable from HEAD and a truncated walk reports success.\n"
                  "      CI must check out with `fetch-depth: 0` for this job.")
            return 1
        return history_mode(args.write_baseline)

    if args.self_test:
        return self_test()

    if args.range is None:
        print("FAIL: --range is required. This gate scans a DELTA by design; "
              "see the module docstring for why a full-history scan is red.")
        return 1

    if is_shallow():
        print("FAIL: this is a SHALLOW clone. A delta gate on a one-commit "
              "checkout scans one commit and reports success.\n"
              "      CI must check out with `fetch-depth: 0` for this job.")
        return 1

    file_arm = range_is_two_dot(args.range)
    try:
        msgs = commit_messages(args.range)
        lines = added_lines(args.range) if file_arm else []
    except subprocess.CalledProcessError as e:
        print(f"FAIL: could not read '{args.range}': {e}")
        return 1

    # FAIL CLOSED: nothing scanned is not the same as nothing wrong. A push that
    # genuinely adds no commit does not reach this gate at all.
    if _is_empty_scan_fatal(msgs):
        print(f"FAIL: scanned ZERO commits for '{args.range}'. An empty scan is "
              f"not a clean scan — this gate refuses to report success on it.")
        return 1

    exempt = active_exemptions()
    bad, exempted = partition(scan(msgs) + scan(lines), exempt)

    # THE PIN AUDIT — the arm a delta scan cannot have. Run before the verdict,
    # because a drifted pin is a failure even on a push that touches nothing.
    intact, drifted, unresolvable, local_only = audit_pins(exempt)
    if drifted:
        print(f"FAIL [gate {self_id()}]: {len(drifted)} PRESERVED-RECORD PIN(S) "
              f"HAVE DRIFTED.\n")
        print("The 2026-08-25 ruling preserved these sites EXACTLY. A pin that no")
        print("longer matches means the preserved record changed -- which the")
        print("exemption does not cover and was never intended to hide.\n")
        for e in drifted:
            print(f'  {e["file"]}  @{e["ref"]}  pin {e["sha"]} no longer matches')
        print("\nEither restore the line byte-for-byte, or take a new ruling.")
        return 1

    if bad:
        print(f"FAIL [gate {self_id()}]: {len(bad)} private-record path(s) "
              f"entering a PUBLIC repo.\n")
        print("Council 2026-08-25 ruled the firewall line at PATHS: paths into")
        print("the private record are forbidden on public repos. Bare filenames")
        print("are softened; role-wording is the standard. Rewrite the reference")
        print("as a ROLE ('the helm's brief') or a bare filename, not a path.\n")
        print("\n".join(finding_lines(bad)))
        print("\nIF YOU ARE DEMONSTRATING A FORBIDDEN FORM rather than citing one:")
        print("assemble it from parts or describe it in words. A literal example")
        print("is still an instance -- this gate tripped ITSELF three times that")
        print("way on its first run, and the paragraph explaining how to avoid it")
        print("sits in this script, which is the one file nobody opens while")
        print("fixing a commit the tool just refused. (compiler seat, 08/25.)")
        print("\nA commit message already pushed cannot be edited without a")
        print("force-push; fix it BEFORE the push, which is why this runs here.")
        return 1

    if exempted:
        print(f"NOTE [gate {self_id()}]: {len(exempted)} finding(s) EXEMPTED BY "
              f"RULING (2026-08-25) -- preserved-record sites, pinned byte-exact.")
        print("      THIS IS NOT A CLEAN RESULT. These lines DO cite the private")
        print("      record; they are preserved deliberately and are green only")
        print("      while they match their pins exactly.")
        for e in exempted:
            print(f"        {e[0]}  {e[1]}")
    if exempt:
        print(f"  PIN AUDIT: {len(intact)} intact, {len(drifted)} drifted, "
              f"{len(unresolvable)} unresolvable"
              + (" (ref not in this checkout -- NOT counted as intact)"
                 if unresolvable else "")
              + (f"; {len(local_only)} resolved from a LOCAL ref only -- a "
                 f"verdict about this checkout, not the published record"
                 if local_only else ""))
    else:
        print(f"  PIN AUDIT: not applicable in '{repo_slug() or 'unknown repo'}'"
              f" -- {len(EXEMPT)} pin(s) exist and none are scoped here."
              f" Stated rather than silently skipped.")

    if file_arm:
        arm2 = f"{len(lines)} added lines scanned"
    else:
        arm2 = ("FILE ARM NOT RUN -- '" + args.range + "' is not a two-dot "
                "range, so `git diff` would compare the working tree, not the "
                "delta. This is a DECLARED GAP, not a clean result")
    print(f"check_private_paths [gate {self_id()}]: OK ({len(msgs)} commit messages scanned and "
          f"{arm2}, for '{args.range}'; " + ("0 paths into the private record" if not exempted else f"0 UNEXEMPTED paths, {len(exempted)} EXEMPTED BY RULING -- see the NOTE above; this line is NOT a clean bill") + "). "
          f"Not scanned, by ruling: {'; '.join(PRESERVED)}.\n"
          f"  WATCHING {len(FORBIDDEN)} shapes: "
          + "; ".join(w for _, w in FORBIDDEN) + ".\n"
          f"  ROOTS ARE A HAND-COPIED SNAPSHOT of a fleet map that lives OUTSIDE"
          f" these repos and MOVES. ROOT-SET DIGEST {ROOTS_DIGEST} -- DERIVED from the list, so"
          f" two gated repos printing the same digest are PROVABLY reconciled and the date below"
          f" is prose that decides nothing (row MK). Last reconciled {ROOTS_RECONCILED} by {ROOTS_OWNER};"
          f" NEXT RE-MEASURE DUE {ROOTS_REMEASURE_DUE}. A private root born after the"
          f" reconcile date is NOT watched until this list is edited, and this line is"
          f" the only thing that will say so -- it went unactioned for 14 days once.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
