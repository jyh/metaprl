# O95 AMENDMENT B′ — the MetaPRL arm's counts (mojave, 2026-11-01 15:0x PST)

The Captain's style rulings (council 2026-11-01 §A), a declared amendment under the preregistration;
the predictions are untouched and vir re-scores. B′ is the four theory commits after 81e0317b0 on `mojave/vir-arm`
(df9524fb0 · 25c260367 · 9bfa8a4a2 · 03fe1ed8c); B is that branch at 81e0317b0.

## What changed (B → B′)
- **Carriers, never `top`.** `wirebuf ≡ list{int}` · `vslice ≡ wirebuf × int` · `state`, `verr` declared ·
  `vresult ≡ (state × vslice) + verr`. The slice laws of I1 hold by definition (vlen, advance, read_u32 are defined, as in B).
- **Prims (the I5 "axioms of the VIR" column): 10.** `state ∈ U`, `verr ∈ U`, `wire_u32`, `can_access`, `has_tokens`,
  `dec_tokens`, `ERR_TRUNCATED_FRAME`, `ERR_UNAUTHORIZED_OR_RATE_LIMITED` (vir.ml) · `take`, `ERR_BAD_PAYLOAD` (vir2.ml).
  Each states only the operator's typing, in `intro`. C4 (the arm's own extra axioms) is unchanged: 0.
- **wf rules, all proved, in `intro`: 37** — vir 27 (incl. the carriers' Type/univ facts, the slice's pair/fst/snd, the wire's
  length) · vir2 4 · vir3 6. Four of them were added DURING the proofs, where a chain met a bare constructor or projection
  (vslice_pair_wf, vslice_fst_wf, vslice_snd_wf, wirebuf_length_wf).
- **Theorems carry no typing premises.** router_fuse / router2_fuse: conditions `b0 ∈ vslice`, `st ∈ state`.
  route_acl_safe `{| intro [] |} 'st`: `[wf] b ∈ validframe`, `[wf] st ∈ state`, the routed premise ⊢ the assert.

## The three theorems (status_all, from the archives, fresh -batch replay)

| program | theorem | B rule boxes | B primitive steps | B′ rule boxes | B′ primitive steps |
|---|---|---|---|---|---|
| 1 | router_fuse (I4) | 5 | 516 | 1 | 290 |
| 2 | router2_fuse (J5) | 12 | 6,036 | 12 | 3,321 |
| 3 | route_acl_safe (K3) | 21 | 1,908 | 19 | 430 |

⚠️ **READ THE STEP COLUMN WITH THIS:** B′'s theorems discharge every typing subgoal through the wf rules, whose own
primitive steps live in those rules' proofs, not in the theorem's. The drop is largely WORK MOVED into shared lemmas
(reused across all three programs), not work removed. The chains themselves are B's, step for step:
- program 1: B's `20.mp` chain verbatim; only its tail changes (`assumT 1..4` → `assumT 1..2`, two carriers).
- program 2: B's `p2-09.mp` chain and its two arithmetic steps verbatim; every typing tail is `assumT 1; assumT 2; autoT`.
- program 3: an opening (the routed premise to the conclusion, `'b` generalized, `st ∈ state` as hypothesis 4 so the
  hypothesis numbers equal B's), then B's main path verbatim; B's seven bespoke wf refines are each `autoT`.

Mutant (program 3, conclusion `can_access(frame_topic b, frame_topic b)`): `incomplete 2`, RED; restored, `complete 19`.
Open as in B: `guard_merge`, `slice_fuse` (the unconditional given forms; their conditional forms are proved and used).

## Files
steps `bp-vir.mp` · `bp-vir2.mp` · `bp-vir3.mp` (the stored scripts; each ends in `export`) · runs `runs-bp-vir*.txt`
(`=== CHILDREN` lines, as before) · the transcription check `transcribe.py`, `steps/tc.mp`, `runs-tc.txt`, `verdicttc.expected`.

## The A.2 transcription check (theory virtc, 10/10)
Each definition as the object/inputs write it, translated by a declared table, `<-->` the hand-written term, proved by
unfolding that definition alone. 10/10 complete. Mutants: a read offset 4 → 8 in F's text stays OPEN; `24` → `12 + 12`
in F2's text CLOSES. LIMITS: equality up to MetaPRL's reduction, not characters; bodies only (parameter lists are
written once by hand in the translator).

## A limit found on the way
`check_all` (the grounded check) reports every rule of module `vir` as depending on "an incomplete /vir/<itself>" — a
self-reference that appears even for `verr_type`. Not a missing proof (status_all reads each complete), and B's branch
shows the same on rules with nothing in intro, so it is not a B′ circularity. DIAGNOSED: the refiner fetches a delayed
rule's proof by `extract [module; rule]`, resolved as a path from the root, and `/vir` resolves to the THEORY directory
(`cd "/vir/beta_lin"` → `Theory.get_theory: theory beta_lin not found`; `cd "/vir2"` reaches the module). A metaprl
defect for any module named like its theory; queued as a pinned fix. The measure here is status_all per rule, as in B.
