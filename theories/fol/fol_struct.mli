(*
 * Structural rules.
 *)

include Base_theory

open Refiner.Refiner.TermType
open Tactic_type.Tacticals

topval nthHypT : int -> tactic
topval thinT : int -> tactic
topval assertT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
