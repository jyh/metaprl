(*
 * These are the basic rewriting operations.
 *)

include Tacticals

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Tacticals
open Rewrite_type

(************************************************************************
 * INHERITANCE                                                          *
 ************************************************************************)

type env = Rewrite_type.env
type conv = Rewrite_type.conv

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
val rwh : conv -> int -> tactic

val prefix_andthenC : conv -> conv -> conv
val prefix_orelseC : conv -> conv -> conv
val addrC : int list -> conv -> conv
val idC : conv
val foldC : term -> conv -> conv
val makeFoldC : term -> conv -> conv
val cutC : term -> conv
val funC : (env -> conv) -> conv

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * Fail with a message.
 *)
val failC : string -> conv
val failWithC : (string * refine_error) -> conv

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
 * Use the first conversion that works.
 *)
val firstC : conv list -> conv

(*
 * Repeat the conversion until nothing more happens.
 *)
val repeatC : conv -> conv
val repeatForC : int -> conv -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
