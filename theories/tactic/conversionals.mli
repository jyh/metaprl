(*
 * These are the basic rewriting operations.
 *)

include Tacticals

open Refiner.Refiner.Term

open Tactic_type
open Tacticals
open Rewrite_type

(************************************************************************
 * INHERITANCE                                                          *
 ************************************************************************)

(*
 * Environment.
 *)
val env_term : env -> term
val env_goal : env -> term

(*
 * All rewrites are wrapped by the rewrite function.
 * The argument is the hyp number, or concl to apply to.
 *)
val rw : conv -> int -> tactic

val prefix_andthenC : conv -> conv -> conv
val prefix_orelseC : conv -> conv -> conv
val addrC : int list -> conv -> conv
val idC : conv

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * Try a conversion.
 *)
val tryC : conv -> conv

(*
 * Subterm application.
 *)
val someSubC : conv -> conv
val allSubC : conv -> conv

(*
 * First term, leftmost, outermost.
 *)
val higherC : conv -> conv

(*
 * First term, leftmost, innermost.
 *)
val lowerC : conv -> conv

(*
 * Sweep the rewrite up from the leaves to the root.
 *)
val sweepUpC : conv -> conv

(*
 * Sweep down from the root to the leaves.
 *)
val sweepDnC : conv -> conv

(*
 * $Log$
 * Revision 1.1  1998/06/03 22:19:53  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
