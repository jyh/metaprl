(*
 * These are some extra derived rules to make proofs easier.
 *)

include Itt_fun
include Itt_prod
include Itt_struct
include Itt_logic

open Refiner.Refiner.TermType
open Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

val applyT : term -> int -> tactic
val anyApplyT : term list -> int -> tactic
val autoApplyT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
