(*
 * Primitiva axiomatization of implication.
 *)

include Czf_wf;;
include Czf_false;;

declare implies{'A; 'B};;
define not_abs : not{'A} <--> 'A => false;;

(*
 * Intro.
 *
 * H >> A => B
 * by implicationIntro
 * H, x: A >> B
 * H >> W wf
 *)
axiom implies_intro 'x :
   sequent { 'H; x: 'A >> 'B } -->
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> 'A => 'B };;

(*
 * Elimination.
 *
 * H, x: A => B, J >> T
 * by implies_elim i
 * H, x: A => B, J >> A
 * H, x: A => B, J, y: B >> T
 *)
axiom implies_elim 'H 'J 'y :
   sequent { 'H; x: 'A => 'B; 'J >> 'A } -->
   sequent { 'H; x: 'A => 'B; 'J; y: 'B >> 'T } -->
   sequent { 'H; x: 'A => 'B; 'J >> 'T };;

(*
 * Well formedness.
 *)
axiom implies_wf :
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> wf{'A => 'B} };;

(*
 * Implication is restricted.
 *)
axiom implies_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H >> restricted{'B} } -->
   sequent { 'H >> restricted{'A => 'B} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
