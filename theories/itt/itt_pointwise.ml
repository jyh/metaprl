doc <:doc<
   @begin[doc]
   @module[Itt_pointwise]
   @parents
   @end[doc]
>>

extends Itt_equal
doc <:doc< @docoff >>

open Lm_debug

(*
 * Show that the file is loading.
 *)
let _ = show_loading "Loading Itt_pointwise%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   The following two rules are valid only for pointwise functionality.
   They both contradict to @hrefrule[Let] rule.
   @end[doc]
>>

prim hypSubstPointwise 'H 'J_1 bind{t.'t1['t]}  bind{y. 'A['y]} :
   [equality] sequent { <H>; t:'T; <J_1['t]>;  x: 'A['t]; <J_2['x;'t]> >- 't = 't1<|H;J_1|>['t] in 'T } -->
   [main] ('c['t;'x] : sequent { <H>; t:'T; <J_1['t]>;  x: 'A['t1<|H;J_1|>['t]]; <J_2['x;'t]> >- 'C['x;'t] }) -->
   sequent { <H>; t:'T; <J_1['t]>;  x: 'A['t]; <J_2['x;'t]> >- 'C['x;'t] } =
   'c['t;'x]

prim contextSubstPointwise 'H 'J_1 'J 't1  :
   [equality] sequent { <H>; t:'T; <J_1['t]>;  <J['t]>; <J_2['t]> >- 't = 't1 in 'T } -->
   [main] ('c['t] : sequent { <H>; t:'T; <J_1['t]>;  <J['t1]>; <J_2['t]> >- 'C['t] }) -->
   sequent { <H>; t:'T; <J_1['t]>;  <J['t]>; <J_2['t]> >- 'C['t] } =
   'c['t]

doc <:doc< @docoff >>
