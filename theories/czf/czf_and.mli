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
 * $Log$
 * Revision 1.1  1997/04/28 15:51:58  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
