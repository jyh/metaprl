(*
 * This is just some utilitiesfor soft abstractions.
 *
 *)

include Tacticals
include Conversionals
include Base_dtactic
include Itt_equal

open Refiner.Refiner
open Refiner.Refiner.Term
open Resource

open Tacticals
open Base_dtactic
open Itt_equal

val add_soft_abs :
       (term * (int -> tactic), int -> tactic, d_data) rsrc ->
       (term * tactic, tactic, eqcd_data) rsrc ->
       term ->
       Rewrite_type.conv ->
       (term * (int -> tactic), int -> tactic, d_data) rsrc *
       (term * tactic, tactic, eqcd_data) rsrc

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
