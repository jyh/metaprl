(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_and
include Czf_itt_sep

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "implies"{'A; 'B}
declare "iff"{'A; 'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_implies : "implies"{'A; 'B} <--> "fun"{'A; 'B}
rewrite unfold_iff : "iff"{'A; 'B} <--> "and"{."implies"{'A; 'B}; ."implies"{'B; 'A}}

val fold_implies : conv
val fold_iff : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom implies_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."implies"{'A; 'B}} }

(*
 * Well formedness.
 *)
axiom implies_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."implies"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A => B
 * by implies_intro
 * H >- A wf
 * H, A >- B
 *)
axiom implies_intro 'H 'a :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H; a: 'A >- 'B } -->
   sequent ['ext] { 'H >- "implies"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A => B, J[x] >- T[x]
 * by implies_elim i
 * H, x: A => B, J[x] >- A
 * H, x: A => B, J[x], y: B -> T[x]
 *)
axiom implies_elim 'H 'J 'x 'y :
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'A } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x]; y: 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
axiom implies_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x ."implies"{'A['x]; 'B['x]}} }

(*
 * Typehood.
 *)
axiom iff_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."iff"{'A; 'B}} }

(*
 * Well formedness.
 *)
axiom iff_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."iff"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A => B
 * by iff_intro
 * H >- A wf
 * H, A >- B
 *)
axiom iff_intro 'H :
   sequent ['ext] { 'H >- "implies"{'A; 'B} } -->
   sequent ['ext] { 'H >- "implies"{'B; 'A} } -->
   sequent ['ext] { 'H >- "iff"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A => B, J[x] >- T[x]
 * by iff_elim i
 * H, x: A => B, J[x] >- A
 * H, x: A => B, J[x], y: B -> T[x]
 *)
axiom iff_elim 'H 'J 'x 'y 'z :
   sequent ['ext] { 'H; y: "implies"{'A; 'B}; z: "implies"{'B; 'A}; 'J["pair"{'y; 'z}] >- 'T["pair"{'y; 'z}] } -->
   sequent ['ext] { 'H; x: "iff"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
axiom iff_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x ."iff"{'A['x]; 'B['x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
