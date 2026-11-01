# O95 PROGRAM 3 — the MetaPRL arm's counts (mojave, 2026-11-01 02:3x PST)

Inputs vir 98d9329 (program3-inputs.md K1–K4; E10 read as p := frame_sender(b), not disputed). Predictions
PREDICTIONS-program3.md (T1–T5), extractors fixed in count.py at that sha. Theory `theories/vir/vir3.ml` (extends vir2; F2 unchanged).
Stored proof `vir3.prla`. Model (B), unchanged.

## K2/K3 as written in CTT (vir3.ml)
- `wirebuf ≡ list{top}` (program 2's buffer type) · `whole_slice{b} ≡ (b, 0)` (Lean's wholeSlice) ·
  `validframe ≡ { b: wirebuf | vlen(whole_slice b) ≥ 24 ∧ read_u32(whole_slice b, 0) = vir_magic ∈ int }` — a SET type, as A.2 · 
  `frame_sender{b} ≡ read_u32(whole_slice b, 4)`, `frame_topic{b} ≡ read_u32(whole_slice b, 8)`.
- `isrouted{o} ≡ assert(decide{o; btrue; bfalse})`, the CTT form of Lean's match to True/False. CanAccess = assert(can_access).
- Goal: `∀b: validframe. ∀st: top. isrouted(F2(whole_slice b, st)) ⇒ assert(can_access(frame_sender b, frame_topic b))`,
  under the I1 typing hypotheses of programs 1–2 (has_tokens now quantified over the state) **plus one new one: take's typing**
  `∀p: top. ∀n: int. ∀s: top. take{p; n; q. vreturn{(s, q)}} ∈ top + top`. take (J1) is declared and undefined, so the
  STATEMENT's well-formedness (isrouted needs F2's output in a union) cannot be proved without it. Lean types take natively.
  A hypothesis, not a rule: C4 does not count it (the programs 1–2 convention). Named here as an affordance difference.

## K3: PROVED
`route_acl_safe` complete, **21 rule boxes, 1,908 primitive steps**. Batch verdict from the archive alone
(`verdict.sh ROOT "" vir3` after the build regenerated vir3.cmoz): `route_acl_safe complete 21`, as verdict3.expected.
Mutant (conclusion `can_access(frame_topic b, frame_topic b)`): `incomplete 2`, RED; restored, green. Programs 1 and 2 re-read: OK.

## The chain (steps/c2-router3.mp, runs-c2-router3.txt with CHILDREN lines)
∀-intro b · unfold validframe/wirebuf in b's type · **set elimination** (b: list{top}; the predicate becomes a squashed hypothesis —
the CTT boundary, one step, no token) · ∀-intro st · ⇒-intro · unfold isrouted/F2/vguard/vdrop/read_u32/whole_slice in the
hypothesis, and frame_sender/topic/read_u32/whole_slice in the goal (both reach the same `wire_u32` form, so NO arithmetic) ·
splitITE on the length guard (the drop branch closes: decide on inr → assert bfalse) · splitITE on the band guard (same) ·
two band eliminations · the goal is a hypothesis. Then 7 refines, one per well-formedness child, each closing it.
A case split proves K3 directly (T5): yes.

## Counts (vir's harness, `count.py --arm metaprl --program 3`, at vir f19133d)
| id | value | note |
|---|---|---|
| C1 | **0** | no cast-class token |
| C2genWf | **7** | 3 from the STATEMENT (validframe Type · top Type · isrouted{F2…} Type) + 4 from the proof (2 splitITE bool-typing, 2 band-elim typing) |
| C2genEq · C2genCond | 0 · 0 | |
| C2gen | **7** | displayed beside it: wf 8 |
| C3 | 5 | amend-3 form unfolds: read_u32 · vguard · vdrop on the main chain; let_lin · advance only in the isrouted-Type closer |
| C3strict | **0** | no aux_ rule |
| C4 | **0** | no prim anywhere |
| C5chain | 178 | refine lines of c2-router3.mp, closers included (Lean 32) |
| C6 | 16 driver sessions to first green | ⚠️ the harness's C6 rows (20 · 43) read `runs-\d+.txt`, which is PROGRAM 1's files: a scope defect for programs 2–3. 10 runs-p3 files kept; 6 reruns overwrote their file, so refines to first green are not recoverable exactly (≥ 140 in the kept files) |

## Against T1–T5 (my reading; vir scores)
- T1: MetaPRL C1 = 0 — holds on this arm.
- T2: C2genWf 7 > Lean P3.C2cond 0 — **holds**. Of the 7, the 3 statement-wf children are §5.1's "Gate 2" class; the other 4 are
  boolean typing of the guards the case split reads.
- T3: C3strict 0 — holds on this arm (C3 under amend-3 is 5).
- T4: C4 0 — holds.
- T5: C5chain 178; the case split proves K3 directly.

## The control (amend-9's CTT half, steps/ctl-flat3.mp, runs-ctl-flat3.txt)
The same chain with `thinT 3` right after the set elimination (the squashed validity predicate removed): the proof completes
(root `*`). ⇒ **in CTT too, ValidFrame carries no load**: the router's own guards re-check length and magic. The boundary is paid
as one set elimination and three statement-wf obligations, never as a coercion.

## Defects / traps met (each measured)
- A session's `.cmoz` is also a BUILD output: deleting it without rebuilding makes `mp` fail "Failed to find the specified format of
  vir3". `reset3.sh` = delete the session-written .cmoz (newer than .build-stamp), then build.
- A session's `.cmoz` loads under the next session, so an "exploration" re-run starts on the previous tree (runs-p3-03 did). Reset before every run.

## D5 (vir's AFFORDANCE-PARITY, recorded only) — MEASURED: no count moves
Scratch module `vir1b.ml` (not scored): program 1's I4 restated with `b0 ∈ list{top} × int` (programs 2–3's type; program 1 used
`top × int`). Program 1's stored script (steps/20.mp), path changed only, proves it: **5 rule boxes, as program 1; 651 primitive
steps against 516** (+135: autoT discharges `b0 ∈ top × int` from the list type). The C2 chain replay (steps/d5-c2-router.mp):
**CHILDREN lines byte-identical** to runs-c2-router.txt, displayed labels 9 = 9. C1, C3, C4, C5chain are script properties and the
script did not change. ⇒ the type difference costs primitive steps only, inside a closer. `verdict.sh ROOT "" vir1b` green.

## D3 re-measured (11-01 02:4x PST): the defect was MY DRIVER's, not metaprl's
`cd` into a module whose archive fails to load RAISES; the shell prints the exception, remounts the previous module (pwd stays
there, consistent) and runs the next phrase, as an interactive shell does. `export ()` then writes the CURRENT module — the previous
one ("Exporting vir"). That is what overwrote vir.prla in runs-p2-07 (step 18: `cd "/vir/vir2"` failed on D1).
**mpdrive read that failed cd as [ok]**: its error needles (Failure · error · Exception · …) do not match `Invalid Argument` or
`wrong magic number`, so its post-D3 guard ("refuse export after an error") would NOT have caught D3 itself.
FIX: a step is ERR unless its output prints a value (`v : type`). Audit over every runs-*.txt: ok-with-value 823 · ERR-without 27 ·
ok-without-value 10 = exactly the missed failures (9 in runs-p2-07, 1 in the probe). Driven both ways on the D3 shape (corrupt
vir1b.prla, cd, export): new driver ERR + REFUSED, archive untouched; old driver ok + exported, vir.prla MODIFIED (restored from git).
The scored program-3 chain classifies identically under the new driver.
