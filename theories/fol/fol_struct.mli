(*
 * Structural rules.
 *)

include Base_theory

open Refiner.Refiner.TermType
open Tactic_type.Tacticals

val nthHypT : int -> tactic
val thinT : int -> tactic
val assertT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
