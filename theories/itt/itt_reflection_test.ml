extends Itt_theory
extends Base_reflection

open Base_reflection

open Basic_tactics

define unfold_is_bterm: is_bterm{'bterm} <--> if_bterm{'bterm;btrue}

let resource reduce +=
   (<<is_bterm{ sequent[bterm]{ <H> >- 't} }>>, (unfold_is_bterm thenC reduce_ifbterm))


interactive wellformed_bterm_example 'J :
   sequent {'H >-
    "assert"{is_bterm{ sequent [bterm] { <J>; x:term; <K> >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} }}} }

