(*
 * Logical false.
 *)

include Czf_wf;;

declare false;;

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
axiom false_elim 'H :
   sequent { 'H; x: false; 'J['x] >> 'T['x] };;

(*
 * False is well-formed.
 *)
axiom false_wf :
   sequent { 'H >> wf{false} };;

(*
 * False is a restricted formula.
 *)
axiom false_res :
   sequent { 'H >> restricted{false} };;

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:00  jyh
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
