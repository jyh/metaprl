(*
 * These are the basic rewriting operations.
 *
 * We execute the operations outside the refiner.
 * After the refinement is done, we construct the
 * rewrite tree.
 *)

include Tacticals

open Debug
open Printf

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine

open Tactic_type

open Tacticals

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Tacticals%t" eflush

let debug_conv =
   create_debug (**)
      { debug_name = "conv";
        debug_description = "display conversion operation";
        debug_value = false
      }

(************************************************************************
 * INHERITANCE                                                          *
 ************************************************************************)

type env = Rewrite_type.env
type conv = Rewrite_type.conv

let env_term = Rewrite_type.env_term
let env_goal = Rewrite_type.env_goal

let rw = Rewrite_type.rw
let prefix_andthenC = Rewrite_type.prefix_andthenC
let prefix_orelseC = Rewrite_type.prefix_orelseC
let addrC = Rewrite_type.addrC
let idC = Rewrite_type.idC

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * Failure.
 *)
let failC err env =
   raise (RefineError ("failC", StringError err))

let failWithC err env =
   raise (RefineError err)

(*
 * Trial.
 *)
let tryC rw =
   rw orelseC idC

(*
 * First subterm that works.
 *)
let someSubC conv env =
   let t = env_term env in
   let count = subterm_count t in
   let rec subC i =
      if i = count then
         failWithC ("subC", StringError "all subterms failed")
      else
         (addrC [i] conv) orelseC (subC (i + 1))
   in
      subC 0 env

(*
 * Apply to all subterms.
 *)
let allSubC conv env =
   let t = env_term env in
   let count = subterm_count t in
   let rec subC i =
      if i = count then
         idC
      else
         (addrC [i] conv) andthenC (subC (i + 1))
   in
      subC 0 env

(*
 * Apply to leftmost-outermost term.
 * We use our own sub, so that we can track the addresses.
 *)
let rec higherC rw env =
   (rw orelseC (someSubC (higherC rw))) env

(*
 * Apply to leftmost-innermost term.
 *)
let rec lowerC rw e =
   ((someSubC (lowerC rw)) orelseC rw) e

(*
 * Apply to all terms possible from innermost to outermost.
 *)
let rec sweepUpC rw =
   (allSubC (sweepUpC rw)) andthenC (tryC rw)

let rec sweepDnC rw =
   (tryC rw) andthenC (allSubC (sweepDnC rw))

(*
 * Use the first conversion that works.
 *)
let rec firstC = function
   conv :: t ->
      conv orelseC firstC t
 | [] ->
      failWithC ("firstC", StringError "all conversions failed")

(*
 * Repeat the conversion until nothing more happens.
 *)
let repeatC conv env =
   let rec repeat t env =
      let t' = env_term env in
         (if alpha_equal t t' then
             idC
          else
             conv andthenC tryC (repeat t')) env
   in
   let t = env_term env in
      (conv andthenC (repeat t)) env

let rec repeatForC i conv env =
   (if i = 0 then
       idC
    else
       conv andthenC (repeatForC (i - 1) conv)) env

(*
 * $Log$
 * Revision 1.3  1998/06/12 18:36:47  jyh
 * Working factorial proof.
 *
 * Revision 1.2  1998/06/12 13:47:45  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.1  1998/06/03 22:19:52  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
