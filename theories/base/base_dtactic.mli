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
 * The inherited d tactic.
 *)
val d_prec : auto_prec

val dT : int -> tactic

(*
 * Run dT 0 so many times.
 *)
val dForT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
