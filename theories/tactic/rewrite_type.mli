(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *)

include Perv

open Refiner.Refiner.Refine

open Sequent
open Tacticals

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type env
type conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Justification for rewrites.
 *)
declare rewrite_just

(*
 * The basic rewrite axiom.
 * BUG: jyh: I don't know why we need the extra param here.
 *)
axiom rewriteAxiom 'x : "rewrite"{'x; 'x}

(*
 * Sequent version of rewrite proposition.
 *)
axiom rewriteSequentAxiom 'H : sequent ['ext] { 'H >- "rewrite"{'x; 'x} }

(*
 * Sequent replacement.
 *)
axiom rewriteHypCut 'H 'J 'T1 :
   sequent ['ext] { 'H; x: 'T1; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H; x: 'T2; 'J['x] >- 'C['x] }

axiom rewriteConclCut 'H 'T1 :
   sequent ['ext] { 'H >- 'T1 } -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H >- 'T2 }

axiom rewriteContextCut 'H 'J (lambda{v. 'T['v]}) :
   "sequent"{'ext; ."context"[H:v]{'T["concl"{'C; ."concl"}]}} -->
   "sequent"{'ext; ."context"[H:v]{."concl"{."rewrite"{.'T[rewrite_just]; ."context"[J:v]{rewrite_just}}; concl}}} -->
   "sequent"{'ext; ."context"[H:v]{."context"[J:v]{."concl"{'C; ."concl"}}}}

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
 * Pull out the argument.
 *)
val funC : (env -> conv) -> conv

(*
 * Apply a conversion at an address.
 *)
val addrC : int list -> conv -> conv

(*
 * Two versions of cut.
 * foldC t conv: cuts in the new term t, and uses conv to
 *    solve the resulting goal.
 * cutC t: just cuts in the new goal
 *)
val foldC : term -> conv -> conv
val cutC : term -> conv

(*
 * Create a fold operation automatically.
 *)
val makeFoldC : term -> conv -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
