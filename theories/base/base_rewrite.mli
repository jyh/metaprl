(*
 * Add the rewrite to the decompose tactic.
 *)

include Rewrite_type
include Base_dtactic

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

open Tactic_type

(*
 * Tactics.
 *)
val rewrite_term : term
val d_rewriteT : int -> tactic

(*
 * $Log$
 * Revision 1.3  1998/06/22 19:46:04  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.2  1998/06/12 13:47:16  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.1  1998/06/01 19:53:58  jyh
 * Working addition proof.  Removing polymorphism from refiner(?)
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
