(*
 * These are the basic rewriting operations.
 *)

include Tacticals

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

open Tactic_type
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
val failWithC : refine_error -> conv

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
 * $Log$
 * Revision 1.5  1998/06/23 22:12:40  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.4  1998/06/22 19:46:41  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.3  1998/06/15 22:33:44  jyh
 * Added CZF.
 *
 * Revision 1.2  1998/06/12 18:36:49  jyh
 * Working factorial proof.
 *
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
