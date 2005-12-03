(*!
 * @module[Itt_pairwise]
 * @parents
 *)

extends Itt_subtype
extends Itt_pairwise

open Basic_tactics

(*! @docoff *)

interactive supertype 'H 'B:
   [wf] sequent  { <H>; x:'A; <J['x]> >- 'A subtype 'B} -->
   sequent  { <H>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; x:'A; <J['x]> >- 'T['x]}

let supertypeT b i =
   supertype i b

interactive supertypeHyp 'H 'K:
   sequent  { <H>; 'A subtype 'B; <K>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; 'A subtype 'B; <K>; x:'A; <J['x]> >- 'T['x]}

