(*!
 * @begin[doc]
 * @module[Itt_pairwise]
 * @parents
 * @end[doc]
 *)

extends Itt_equal
extends Itt_squiggle
extends Itt_struct2

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type

open Itt_squiggle
open Itt_struct
open Itt_struct2
(*! @docoff *)


(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * The following two rules are valid only for pairwise functionality.
 * They are invalid in pointwise functionality and contradict, for example, to @hrefrule[quotientElimination2] rule.
 * @end[doc]
 *)

prim let_rule 'H ('x='s in 'S):
  [assertion] sequent { <H>; <J> >- 's in 'S } -->
   [main]    ('t['x; 'u]:  sequent { <H>; x: 'S;  <J>; u:'s ~ 'x  >- 'T } )-->
   sequent { <H>; <J>  >- 'T}
      = 't['s; it]

let rec onAllHypFrom n tac =  (* applies tac on all hyp betweeb n ending -1 excluded *)
    funT (fun p ->
       if n= -1 || n=Sequent.hyp_count p then idT else
       let next = if n>0 then n+1 else n-1 in
          tac next thenT onAllHypFrom next tac
         )

let letAtT i x_is_s_in_S =
   let i = if i < 0 then i + 1 else i in
      let_rule i x_is_s_in_S thenMT (rwh (hypC (-1)) 0 thenT onAllHypFrom i (rwh (hypC (-1))) thenT thinT (-1))


(*! @docoff *)
