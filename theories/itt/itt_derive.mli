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

topval applyT : term -> int -> tactic
topval anyApplyT : term list -> int -> tactic
topval autoApplyT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
