(*
 * These are the basic rewriting operations.
 *)

include Nltop

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
topval rw : conv -> int -> tactic
topval rwh : conv -> int -> tactic

topval prefix_andthenC : conv -> conv -> conv
topval prefix_orelseC : conv -> conv -> conv
topval addrC : int list -> conv -> conv
topval idC : conv
topval foldC : term -> conv -> conv
topval makeFoldC : term -> conv -> conv
topval cutC : term -> conv
val funC : (env -> conv) -> conv

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * Fail with a message.
 *)
topval failC : string -> conv
val failWithC : (string * refine_error) -> conv

(*
 * Try a conversion.
 *)
topval tryC : conv -> conv

(*
 * Subterm application.
 *)
topval someSubC : conv -> conv
topval allSubC : conv -> conv

(*
 * First term, leftmost, outermost.
 *)
topval higherC : conv -> conv

(*
 * First term, leftmost, innermost.
 *)
topval lowerC : conv -> conv

(*
 * Sweep the rewrite up from the leaves to the root.
 *)
topval sweepUpC : conv -> conv

(*
 * Sweep down from the root to the leaves.
 *)
topval sweepDnC : conv -> conv

(*
 * Use the first conversion that works.
 *)
topval firstC : conv list -> conv

(*
 * Repeat the conversion until nothing more happens.
 *)
topval repeatC : conv -> conv
topval repeatForC : int -> conv -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
