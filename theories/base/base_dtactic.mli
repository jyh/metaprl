(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

open Term
open Refine
open Tactic_type

(*
 * This are the types.
 *)
type d_data

resource (term * (int -> tactic), int -> tactic, d_data) d_resource

(*
 * $Log$
 * Revision 1.2  1998/05/07 16:02:59  jyh
 * Adding interactive proofs.
 *
 * Revision 1.1  1997/04/28 15:51:55  jyh
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
 * Revision 1.2  1996/10/23 15:18:02  jyh
 * First working version of dT tactic.
 *
 * Revision 1.1  1996/09/25 22:52:09  jyh
 * Initial "tactical" commit.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
