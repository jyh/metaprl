(*!
 * @begin[doc]
 * @module[Itt_pairwise]
 * @parents
 * @end[doc]
 *)

extends Itt_equal
extends Itt_squiggle
extends Itt_struct2
extends Itt_subtype

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type

open Itt_squiggle
open Itt_struct
open Itt_struct2
(*! @docoff *)

interactive supertype 'H 'B:  (* Can't prove it because of the BUG #3.14 *)
   sequent  { <H>; x:'A; <J['x]> >- 'A subtype 'B} -->
   sequent  { <H>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; x:'A; <J['x]> >- 'T['x]}

interactive supertypeHyp 'H 'K:
   sequent  { <H>; 'A subtype 'B; <K>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; 'A subtype 'B; <K>; x:'A; <J['x]> >- 'T['x]}

