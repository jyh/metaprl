(*
 * Logical true.
 *)

include Czf_wf

declare "true"

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
axiom true_intro 'H : sequent { 'H >- "true" }

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
axiom true_wf 'H :
   sequent { 'H >- wf{."true"} }

(*
 * True is a restricted formula.
 *)
axiom true_res 'H :
   sequent { 'H >- restricted{."true"} }

(*
 * $Log$
 * Revision 1.2  1998/06/15 22:33:02  jyh
 * Added CZF.
 *
 * Revision 1.1  1997/04/28 15:52:03  jyh
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
