(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "and"{'A; 'B}
declare pair{'a; 'b}
declare spread{'z; x, y. 'b['x; 'y]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_and : "and"{'A; 'B} <--> 'A * 'B
rewrite unfold_pair : pair{'a; 'b} <--> Itt_dprod!pair{'a; 'b}
rewrite unfold_spread : spread{'z; x, y. 'b['x; 'y]} <-->
   Itt_dprod!spread{'z; x, y. 'b['x; 'y]}

val fold_and : conv
val fold_pair : conv
val fold_spread : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom and_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."and"{'A; 'B}} }

(*
 * Well formedness.
 *)
axiom and_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."and"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A /\ B
 * by or_intro
 * H >- A
 * H >- B
 *)
axiom and_intro 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- "and"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A /\ B, J[x] >- T[x]
 * by and_elim i
 * H, x: A /\ B, y: A; z:B; J[<y, z>] >- T[<y, z>]
 *)
axiom and_elim 'H 'J 'x 'y 'z :
   sequent ['ext] { 'H;
                    y: 'A;
                    z: 'B;
                    'J[pair{'y; 'z}]
                    >- 'T[pair{'y; 'z}]
   } -->
   sequent ['ext] { 'H; x: "and"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
axiom and_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "and"{'A['x]; 'B['x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
