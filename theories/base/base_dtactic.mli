(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.Refine
open Tacticals

(*
 * This are the types.
 *)
type d_data

resource (term * (int -> tactic), int -> tactic, d_data) d_resource

(*
 * The inherited d tactic.
 *)
val dT : int -> tactic

(*
 * $Log$
 * Revision 1.5  1998/07/03 21:04:11  nogin
 * Specified the full "path" to the Refine module:
 * open Refiner.Refiner.Refine
 *
 * Revision 1.4  1998/07/02 18:36:47  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/05/28 13:47:14  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
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
