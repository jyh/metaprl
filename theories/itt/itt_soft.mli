(*
 * This is just some utilitiesfor soft abstractions.
 *
 *)

include Tactic_type

include Itt_equal

open Refiner.Refiner
open Refiner.Refiner.Term
open Resource

open Tactic_type
open Base_dtactic
open Itt_equal

val add_soft_abs :
       (term * (int -> tactic), int -> tactic, d_data) rsrc ->
       (term * tactic, tactic, eqcd_data) rsrc ->
       term ->
       tactic_argument Refine.rw ->
       (term * (int -> tactic), int -> tactic, d_data) rsrc *
       (term * tactic, tactic, eqcd_data) rsrc

(*
 * $Log$
 * Revision 1.4  1998/06/01 13:56:17  jyh
 * Proving twice one is two.
 *
 * Revision 1.3  1998/05/28 13:48:05  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/22 22:45:12  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/04/28 15:52:26  jyh
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
 * Revision 1.1  1996/10/23 15:18:12  jyh
 * First working version of dT tactic.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
