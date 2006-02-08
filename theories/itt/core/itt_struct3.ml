extends Itt_squash
extends Itt_ext_equal
extends Itt_struct2
extends Itt_subtype
extends Itt_pairwise2

open Basic_tactics

open Itt_struct
open Itt_ext_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* This rule is valid both in pointwise and pairwise functionality, but the proof of this rule is
 * difirent for these functionalities
 *)

interactive substUsingEpimorphism 'H 'B bind{y. 'f['y]} bind{x. 'g['x]}  : (* g does not depend on J *)
   [wf] sequent { <H>; x: 'A; <J['x]> >-  'g['x] in 'B } -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'f['g['x]] ~ 'x } -->
   [main] sequent { <H>; y: 'B; <J['f['y]]> >- 'C['f['y]] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

interactive hypReplacementStrong 'H 'B :
   [assertion] sequent { <H>; x: 'A; <J['x]>; y: 'B >- 'y in 'A } -->
   [assertion] sequent { <H>; x: 'A; <J['x]> >-  'x in 'B } -->
   [main] sequent { <H>; x: 'B; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'C['x] }

interactive hypReplacementExt 'H 'B  :
   [equality] sequent { <H>; x: 'A; <J['x]> >- ext_equal{'A;'B} } -->
   [main]  sequent { <H>; x: 'B; <J['x]> >- 'T['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] }

let changeHypT t i =
   hypReplacementStrong i t

let replaceHypT t i = funT (fun p ->
   try
      let univ = get_univ_arg p in
        hypReplacement i t univ
   with RefineError _ ->
        hypReplacementExt i t)

let replaceWithHypT j i = funT (fun p ->
   let s, t = dest_ext_equal (Sequent.nth_hyp p j) in
	hypReplacementExt i t)

let replaceWithRevHypT j i = funT (fun p ->
   let s, t = dest_ext_equal (Sequent.nth_hyp p j) in
	hypReplacementExt i s)
