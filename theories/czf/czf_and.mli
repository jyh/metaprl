(*
 * Primitiva axiomatization of implication.
 *)

include Czf_wf;;

declare and{'A; 'B};;
declare pair{'A; 'B};;

(*
 * Intro.
 *
 * H >> A /\ B
 * by and_intro
 * H >> A
 * H >> B
 *)
axiom and_intro :
   sequent { 'H >> 'A } -->
   sequent { 'H >> 'B } -->
   sequent { 'H >> 'A /\ 'B };;

(*
 * Elimination.
 *
 * H, x: A /\ B, J[x] >> T[x]
 * by or_elim i
 * H, y: A; z: B; J[<y, z>] >> T[y, z]
 *)
axiom and_elim 'H 'J 'y 'z :
   sequent { 'H; y: 'A; z: 'B; 'J['y, 'z] >> 'T['y, 'z] } -->
   sequent { 'H; x: 'A /\ 'B; 'J['x] >> 'T['x] };;

(*
 * Well formedness.
 *)
axiom and_wf :
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> wf{'A /\ 'B} };;

(*
 * Implication is restricted.
 *)
axiom and_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H >> restricted{'B} } -->
   sequent { 'H >> restricted{'A /\ 'B} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
