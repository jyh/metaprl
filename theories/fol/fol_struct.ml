(*
 * Structural rules.
 *)

extends Base_theory

open Tactic_type
open Tactic_type.Tacticals

open Auto_tactic

(*
 * Hypothesis.
 *)
prim hypothesis 'H :
   sequent ['ext] { <H>; x: 'T; <J['x]> >- 'T } = 'x

(*
 * Thinning.
 *)
prim thin 'H :
   ('t : sequent ['ext] { <H>; <J> >- 'C }) -->
   sequent ['ext] { <H>; x: 'T; <J> >- 'C } = 't

(*
 * Cut rule.
 *)
prim cut 'T :
   ('a : sequent ['ext] { <H> >- 'T }) -->
   ('b['x] : sequent ['ext] { <H>; x: 'T >- 'C }) -->
   sequent ['ext] { <H> >- 'C } =
   'b['a]

(*
 * Tactics.
 *)
let nthHypT = hypothesis
let thinT = thin

let nthAssumT = argfunT (fun i p ->
   let assum = Sequent.nth_assum p i in
      Top_tacticals.thinMatchT thinT assum)

let assertT = cut

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
