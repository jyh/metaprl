(*
 * Additional tacticals.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:40  jyh
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
 * Revision 1.1  1996/10/23 15:18:15  jyh
 * First working version of dT tactic.
 *
 *)

open Term
open Refine
open Var
open Sequent
open Tacticals

(*
 * Optional vars.
 *)
let get_opt_var_arg v p =
   try get_var_arg 0 p with
      Not_found -> maybe_new_var v (declared_vars p)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
