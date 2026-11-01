# O95 PROGRAM 2 — the MetaPRL arm's counts (mojave, 2026-11-01 01:0x)

Inputs vir 5d6f739a (program2-inputs.md J1–J5; I1, I5, I7, amend-1..6 carried). Predictions PREDICTIONS-program2.md (Q1–Q5).
Theory `theories/vir/vir2.ml` (vir-metaprl 139797629, local). Stored proof **`vir2.prlb`** (binary; see D1). Model (B), unchanged.

## J5: PROVED
`router2_fuse : (b0 ∈ list{top} × int) → (∀x k. wire_u32 ∈ int) → (∀x y. can_access ∈ Bool) → (∀x. has_tokens ∈ Bool)
 → vir_U2{b0; st} <--> vir_F2{b0; st}` — complete, 12 rule boxes, 6,036 primitive steps.
Batch verdict from the archive (`verdict.sh ROOT "" vir2`, fresh build, no session archive): `router2_fuse complete 12`, as verdict2.expected.
Program 1's verdict re-read after every program 2 session: 12 rules OK.
The condition changed from program 1: `b0 ∈ list{top} × int` (was top × int), because the bound uses the buffer's length.

## The chain (I7), one rule per step (steps/c2-router2.mp, runs-c2-router2.txt with CHILDREN lines)
unfold U2/F2 and the J2 bodies · aux_advance_sink_guard · beta_lin · aux_advance_sink_guard · **unfold_advance** (the s1 advance:
the bad-payload guard's condition mentions s1, so no VIR-level rule can move or fuse it) · unfold_read_u32 (all) · aux_guard_swap ·
guard_merge_c ×2 · beta_lin (F2 side) · unfold_advance (rest) · const_fold/assoc (ITT reduceC) · unfold vlen · reduceC ·
two arithmetic BRIDGES: `sqSubstT` (offset: b0.2 + (12 + (w − 12)) ~ b0.2 + w; bound: (|b0.1| − (b0.2 + 12)) + 12 ~ |b0.1| − b0.2),
each `sqsimple_sq <<int>>` then `omegaT`. Neither slice_fuse nor slice_fuse_c is on this path.

## Counts
| id | program 2 | program 1 | how |
|---|---|---|---|
| C1 | **0** | 0 | no cast-class token in any script |
| C2wf (gen) | **3** | 3 | lemma proofs on the path (splitBoolT): guard_merge_c 1, aux_guard_swap 2 |
| C2eq (gen) | **6** | 0 | the two bridges: sqSubstT 1 + sqsimple_sq 2, twice |
| C2cond (gen) | **9** | 10 | chain: swap 2 · merge 1 + 1 · reduceC's associativity conditions 5. (Program 1's lemma slice_fuse_c added 3; not on this path) |
| C2 gen sum | **18** | 13 | |
| discharge-visible, beside | wf 4 · assertion 6 | wf 2 | omegaT's typing leaves (closer level, not in the sum, by program 1's rule) |
| C3 | **4** (strict **2**) | 3 (strict 2) | aux_advance_sink_guard · aux_guard_swap · unfold_read_u32 · **unfold_advance** (new form, amend-3) |
| C4 | **0** | 0 | no `prim` in vir2.ml; every path rule proved |
| C5 | 12 tactics · 1,236 tokens | 11 · 487 | refine lines of steps/p2-09.mp (= the stored proof) |
| C6 | 8 driver sessions · 61 refines · to first green (p2-08) | 20 · 43 | runs-p2-01..08 (p2-06/07 broke on D2 and D3) |

## Against Q1–Q5 (my reading; vir scores)
- Q1 (MetaPRL C1 = 0): **holds** on this arm.
- Q2 (C2cond rises on both; MetaPRL gen-cond > 10): **FALSIFIED on C2gen-cond (9 ≤ 10)**; holds on the displayed reading
  (9 + 6 = 15). The cost moved from conditions to EQUALITY obligations (C2eq 0 → 6). The C2 sum rises, 13 → 18.
- Q3 (≥ 1 aux beyond program 1's set): **holds under amend-3** (the advance unfold is new: C3 3 → 4); **falsified on C3strict** (2 → 2).
  No context-dependent rewrite was needed: in model (B) offsets are unbounded ints, so `24 ≤ off` is never used by the equation (M-F3 again).
- Q4 (F1 recurs): **holds, measured** — aux_guard_swap at the guard pair with the reads in place:
  `Rewrite condition has free variable where it is not allowed 'topic` (runs-q4-router2.txt). The bound condition is
  never the trigger (no rewrite in this chain is conditional on `off`).
- Q5: shortcut not attempted (I7); C5/C6 above.

## Defects found on the way (MetaPRL / the driver), each measured
- **D1 — a module whose summary id is ≥ 2^30 cannot load its text archive.** `Filter_cache_fun.hash` seeds with 0x6ace12d4 (bit 30 set);
  only the grammar constants flip that bit, so an id lands ≥ 2^30 for some modules. The archive writes `Number <id>`; reading it,
  `Lm_num.num_of_string` makes any value ≥ 2^30 a big number (15-bit digits), and `Filter_summary.dest_id` rejects it:
  `Invalid Argument: Filter_summary.dest_id: not an int`. vir2's id is 1,511,842,520. Of the 234 committed .prla in metaprl, 211 carry an id, all with |id| < 2^30 (68 negative, written on 32-bit); 23 carry none. (First published as "all 143": that census's regex could not match a minus sign.)
  Workaround: the binary archive (.prlb). FIX: metaprl #88 (dest_id reads an OCaml int; test/filter_prla_id red on the old code, green with the fix).
- **D2 — the mp shell parses one LINE as one phrase and fails past ~1,024 characters**; a phrase cannot continue on the next line.
  mpdrive now refuses a command over 1,000 characters (split the refine instead).
- **D3 — `export ()` after a failed step overwrote program 1's committed vir.prla** (restored from git b26a2bd84; verdict green after). **[CORRECTED 11-01 02:4x PST: the failed step was a `cd` into vir2 (D1); the shell stayed in vir and export wrote vir, as designed. The defect was mpdrive reading that cd as ok — fixed in tools 10191be; see COUNTS-metaprl-program3.md §D3.]**
  mpdrive now refuses `export`/`save` once any step of the session has erred.
