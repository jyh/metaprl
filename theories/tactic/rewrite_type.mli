(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *)

open Refiner.Refiner.Refine

open Tactic_type

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type t
type env

type conv = env -> t

(************************************************************************
 * OPERATIONS                                                           *
 ************************************************************************)

(*
 * Operations on the environment mirror operations from Sequent.
 *)
val env_term : env -> term
val env_goal : env -> term

(*
 * Apply a rewrite.
 *)
val rw : conv -> int -> tactic

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
val rewrite_of_rewrite : prim_rewrite -> conv

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
val rewrite_of_cond_rewrite : prim_cond_rewrite -> string array * term list -> conv

(*
 * Sequencing.
 *)
val prefix_andthenC : conv -> conv -> conv
val prefix_orelseC : conv -> conv -> conv

(*
 * Identity.
 *)
val idC : conv

(*
 * Apply a conversion at an address.
 *)
val addrC : int list -> conv -> conv

(*
 * $Log$
 * Revision 1.1  1998/06/03 22:19:56  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
