(*
 * Primitiva axiomatization of implication.
 *)

include Czf_wf;;

declare or{'A; 'B};;
declare inl{'A};;
declare inr{'A};;

(*
 * Intro.
 *
 * H >> A \/ B
 * by or_intro_left
 * H >> A
 * H >> B wf
 *)
axiom or_intro_left 'x :
   sequent { 'H >> 'A } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> 'A \/ 'B };;

axiom or_intro_right 'x :
   sequent { 'H >> 'B } -->
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> 'A \/ 'B };;

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >> T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >> T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >> T[inr y]
 *)
axiom or_elim 'H 'J 'y :
   sequent { 'H; x: 'A \/ 'B; y: 'A; 'J[inl{'y}] >> 'T[inl{'y}] } -->
   sequent { 'H; x: 'A \/ 'B; y: 'B; 'J[inr{'y}] >> 'T[inr{'y}] } -->
   sequent { 'H; x: 'A \/ 'B; 'J['x] >> 'T['x] };;

(*
 * Well formedness.
 *)
axiom or_wf :
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> wf{'A \/ 'B} };;

(*
 * Implication is restricted.
 *)
axiom or_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H >> restricted{'B} } -->
   sequent { 'H >> restricted{'A \/ 'B} };;
