(*
 * This is just some utilitiesfor soft abstractions.
 *
 *)

open Term
open Resource
open Refine

include Tactic_type

include Itt_equal

val add_soft_abs :
       (term * (int -> tactic), int -> tactic, d_data) rsrc ->
       (term * tactic, tactic, eqcd_data) rsrc ->
       term ->
       tactic_argument Refiner.rw ->
       (term * (int -> tactic), int -> tactic, d_data) rsrc *
       (term * tactic, tactic, eqcd_data) rsrc

(*
 * $Log$
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
