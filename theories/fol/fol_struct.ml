(*
 * Structural rules.
 *)

extends Base_theory

open Basic_tactics

(*
 * Hypothesis.
 *)
prim hypothesis 'H :
   sequent { <H>; x: 'T; <J['x]> >- 'T } = 'x

(*
 * Thinning.
 *)
prim thin_many 'H 'J :
   ('t : sequent { <H>; <K> >- 'C }) -->
   sequent { <H>; <J>; < K<|H|> > >- 'C<|H;K|> } = 't

interactive thin 'H :
   sequent { <H>; <J> >- 'C } -->
   sequent { <H>; 'A; <J> >- 'C }

(*
 * Cut rule.
 *)
prim cut 'T :
   ('a : sequent { <H> >- 'T }) -->
   ('b['x] : sequent { <H>; x: 'T >- 'C }) -->
   sequent { <H> >- 'C } =
   'b['a]

(*
 * Tactics.
 *)
let nthHypT = hypothesis
let thinT = thin

let nthAssumT = argfunT (fun i p ->
   let assum = Sequent.nth_assum p i in
      Top_tacticals.thinMatchT thin_many assum)

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
