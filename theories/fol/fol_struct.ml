(*
 * Structural rules.
 *)

include Base_theory

open Refiner.Refiner.RefineError
open Base_auto_tactic
open Mp_resource
open Tacticals

(*
 * Hypothesis.
 *)
prim hypothesis 'H 'J 'x : :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'T } = 'x

(*
 * Thinning.
 *)
prim thin 'H 'J :
   ('t : sequent ['ext] { 'H; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'C['x] } = 't

(*
 * Cut rule.
 *)
prim cut 'H 'T 'x :
   ('a : sequent ['ext] { 'H >- 'T }) -->
   ('b['x] : sequent ['ext] { 'H; x: 'T >- 'C }) -->
   sequent ['ext] { 'H >- 'C } =
   'b['a]

(*
 * Tactics.
 *)
let nthHypT i p =
   let v, _ = Sequent.nth_hyp p i in
   let j, k = Sequent.hyp_indices p i in
      hypothesis j k v p

let thinT i p =
   let x, _ = Sequent.nth_hyp p i in
      if Sequent.is_free_seq_var i x p then
         raise (RefineError ("thinT", StringStringError ("free variable: ", x)))
      else
         let i, j = Sequent.hyp_indices p i in
            thin i j p

let assertT t p =
   let v = Var.maybe_new_vars1 p "v" in
      cut (Sequent.hyp_count_addr p) t v p

(*
 * Add to trivialT tactic.
 *)
let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "nthHypT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT nthHypT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
