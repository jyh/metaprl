(*
 * The D tactic performs a case selection on the conclusion opname.
 *)

include Base_auto_tactic

open Refiner.Refiner.Term
open Refiner.Refiner.Refine
open Tacticals

open Base_auto_tactic

(*
 * This are the types.
 *)
type d_data

resource (term * (int -> tactic), int -> tactic, d_data) d_resource

(*
 * Get a resource for the toploop.
 *)
val get_resource : string -> d_resource

(*
 * The inherited d tactic.
 *)
val d_prec : auto_prec

topval dT : int -> tactic

(*
 * Run dT 0 so many times.
 *)
topval dForT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
