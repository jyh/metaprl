(*
 * Structural rules.
 *)

extends Base_theory

open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic

(*
 * Hypothesis.
 *)
prim hypothesis 'H 'J :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'T } = 'x

(*
 * Thinning.
 *)
prim thin 'H 'J :
   ('t : sequent ['ext] { 'H; 'J >- 'C }) -->
   sequent ['ext] { 'H; x: 'T; 'J >- 'C } = 't

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
   let j, k = Sequent.hyp_indices p i in
      hypothesis j k p

let thinT i p =
   let i, j = Sequent.hyp_indices p i in
      thin i j p

let nthAssumT i p =
   let assum = Sequent.nth_assum p i in
      Top_tacticals.thinMatchT thinT assum p

let assertT t p =
   let v = Var.maybe_new_vars1 p "v" in
      cut (Sequent.hyp_count_addr p) t v p

(*
 * Add to trivialT tactic.
 *)
let resource auto += {
   auto_name = "Fol_struct.nthHypT+nthAssumT";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT nthHypT orelseT onSomeAssumT nthAssumT;
   auto_type = AutoTrivial;
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
