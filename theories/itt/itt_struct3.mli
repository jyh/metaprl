extends Itt_squash
extends Itt_ext_equal
extends Itt_struct2
extends Itt_subtype
extends Itt_pointwise

open Refiner.Refiner.RefineError

open Tactic_type.Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* This rule is valid both in pointwise and pairwise functionality, but the proof of this rule is
 * difirent for these functionalities
 *)
(*
 * WEAK BUG
rule substUsingEpimorphism 'H 'B bind{y. 'f['y]} bind{x. 'g['x]}  : (* g does not depend on J *)
   [wf] sequent { <H>; x: 'A; <J['x]>; y: 'B >- 'f['y] in 'A } -->
   [wf] sequent { <H>; x: 'A; <J['x]> >-  'g['x] in 'B } -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'f['g['x]] ~ 'x } -->
   [main] sequent { <H>; y: 'B; <J['f['y]]> >- 'C['f['y]] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

rule hypReplacementStrong 'H 'B :
   [assertion] sequent { <H>; x: 'A; <J['x]>; y: 'B >- 'y in 'A } -->
   [assertion] sequent { <H>; x: 'A; <J['x]> >-  'x in 'B } -->
   [main] sequent { <H>; x: 'B; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

rule hypReplacementExt 'H 'B  :
   [equality] sequent { <H>; x: 'A; <J['x]> >- ext_equal{'A;'B} } -->
   [main]  sequent { <H>; x: 'B; <J['x]> >- 'T['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] }
*)

topval changeHypT : term -> int -> tactic

topval replaceHypT : term -> int -> tactic
