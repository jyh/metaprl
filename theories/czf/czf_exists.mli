(*
 * Universal quantification.
 *)

include Czf_wf;;
include Czf_set;;
include Czf_implies;;
include Czf_member;;

declare "exists"{x. 'P};;
define bounded_exists_abs : "exists"{'y; x. 'P['x]} <--> "exists"{x. member{'x; 'y} => 'P['x]};;

(*
 * Bounded intro form.
 *
 * H >> exists x: A. B[x]
 * by bounded_exists_intro a
 * H >> B[a]
 * H >> member{a; A}
 * functionality subgoal?
 *)
axiom bounded_exists_intro 'a :
   sequent { 'H >> 'B['a] } -->
   sequent { 'H >> member{'a; 'A} } -->
   sequent { 'H >> exists x: 'A. 'B['x] };;

(*
 * Bounded elim form.
 *
 * H, y: (exists x: A. B[x]), J >> T
 * by bounded_exists_elim a
 * H, y: (exists x: A. B[x]), a: A, z: B[a], J >> T
 *)
axiom bounded_exists_elim 'H 'J 'a 'z :
   sequent { 'H; y: (exists x: 'A. 'B['y]); a: 'A; b: 'B['a]; 'J['a, 'b] >> 'T['a, 'b] } -->
   sequent { 'H; y: (exists x: 'A. 'B['y]); 'J['y] >> 'T['y] };;

(*
 * Unbounded intro form.
 *
 * H >> exists x. B[x]
 * by exists_intro z
 * H >> B[z]
 * H >> member{z, set}
 *)
axiom exists_intro 'z :
   sequent { 'H >> 'B['z] } -->
   sequent { 'H >> member{'z; set} } -->
   sequent { 'H >> "exists"{x. 'B['x]} };;

(*
 * Elim form.
 *
 * H, y: (exists x. B[x]), J >> T
 * by exists_elim z w
 * H, y: (exists x. B[x]), z: set, b: 'B['z], J>> T
 *)
axiom all_elim 'H 'J 'z 'b :
   sequent { 'H; y: "exists"{x. 'B['x]}; z: set; b: 'B['z]; 'J[z, b] >> 'T['z, 'b] } -->
   sequent { 'H; y: "exists"{x. 'B['x]}; 'J['y] >> 'T['y] };;

(*
 * Wellformedness.
 *)
axiom bounded_exists_wf :
   sequent { 'H >> wf{'A} } --> (* should be a different judgment? *)
   sequent { 'H; x: set >> wf{'B['x]} } -->
   sequent { 'H >> wf{exists x: 'A. 'B['x] } };;

axiom exists_wf :
   sequent { 'H; x: set >> wf{'B['x]} } -->
   sequent { 'H >> wf{"exists"{x. 'B['x]}} };;

(*
 * Bounded formula is restricted.
 *)
axiom bounded_exists_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H; x: set; y: restricted{x} >> restricted{'B['x]} } -->
   sequent { 'H >> restricted{exists x: 'A. 'B['x]} };;

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:51:59  jyh
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
