(*
 * These are the basic rewriting operations.
 *
 * We execute the operations outside the refiner.
 * After the refinement is done, we construct the
 * rewrite tree.
 *)

include Tacticals

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

open Tactic_type
open Tacticals

(************************************************************************
 * INHERITANCE                                                          *
 ************************************************************************)

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
 * Trial.
 *)
let tryC rw =
   rw orelseC idC

(*
 * First subterm that works.
 *)
let someSubC conv env =
   let t = env_goal env in
   let count = subterm_count t in
   let rec subC i =
      if i = count then
         (fun p -> raise (RefineError (StringStringError ("subC", "all subterms failed"))))
      else
         (addrC [i] conv) orelseC (subC (i + 1))
   in
      subC 0 env

(*
 * Apply to all subterms.
 *)
let allSubC conv env =
   let t = env_goal env in
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
 *)
let higherC rw =
   rw orelseC (someSubC rw)

(*
 * Apply to leftmost-innermost term.
 *)
let lowerC rw =
   (someSubC rw) orelseC rw

(*
 * Apply to all terms possible from innermost to outermost.
 *)
let rec sweepUpC rw =
   (allSubC (sweepUpC rw)) andthenC (tryC rw)

let rec sweepDnC rw =
   (tryC rw) andthenC (allSubC (sweepDnC rw))

(*
 * $Log$
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
