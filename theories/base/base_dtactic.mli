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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
