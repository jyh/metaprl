(*
 * Add the rewrite to the decompose tactic.
 *)

include Rewrite_type
include Base_dtactic

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

open Tacticals

(*
 * Tactics.
 *)
val rewrite_term : term
val d_rewriteT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
