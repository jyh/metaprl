(*
 * Primitive axiomatization of implication.
 *)

include Czf_itt_set
include Czf_itt_union

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "or"{'A; 'B}
declare "inl"{'x}
declare "inr"{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_or : "or"{'A; 'B} <--> Itt_union!union{'A; 'B}
rewrite unfold_inl : inl{'x} <--> Itt_union!inl{'x}
rewrite unfold_inr : inr{'x} <--> Itt_union!inr{'x}
rewrite unfold_decide : decide{'x; y. 'a['y]; z. 'b['z]} <--> Itt_union!decide{'x; y. 'a['y]; z. 'b['z]}

rewrite reduce_decide_inl : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
rewrite reduce_decide_inr : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

val fold_or : conv
val fold_inr : conv
val fold_inl : conv
val fold_decide : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- A \/ B
 * by or_intro_left
 * H >- A
 * H >- B wf
 *)
axiom or_intro_left 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

axiom or_intro_right 'H :
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >- T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >- T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >- T[inr y]
 *)
axiom or_elim 'H 'J 'y :
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'A; 'J[inl{'y}] >- 'T[inl{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'B; 'J[inr{'y}] >- 'T[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom or_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."or"{'A; 'B}} }

axiom or_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."or"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
axiom or_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "or"{'A['x]; 'B['x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
