(*
 * Additional tacticals.
 *)

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.Refine
open Var
open Sequent
open Tacticals

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Options%t" eflush

(*
 * Optional vars.
 *)
let get_opt_var_arg v p =
   try dest_var (get_term_arg p "var") with
      Not_found ->
         maybe_new_var v (declared_vars p)

(*
 *
 * $Log$
 * Revision 1.4  1998/06/09 20:52:52  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.3  1998/05/28 13:48:32  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/24 02:43:59  jyh
 * Added more extensive debugging capabilities.
 *
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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
