extends Itt_theory
extends Base_reflection

open Base_reflection

open Basic_tactics

define unfold_is_bterm: is_bterm{'bterm} <--> Base_reflection!if_bterm{'bterm;"true"}

let resource reduce +=
   (<<is_bterm{ sequent[bterm]{ <H> >- 't} }>>, (unfold_is_bterm thenC reduce_ifbterm))

interactive wellformed_bterm_example 'J :
   sequent {'H >-
    is_bterm{ sequent [bterm] { <J>; x:term; <K> >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} }} }

declare list_of_xlist{'l}

prim_rw reduce_xlist_cons :
   list_of_xlist{ (Perv!cons{'hd; 'tl})} <--> ('hd :: list_of_xlist{'tl})

prim_rw reduce_xlist_nil :
   list_of_xlist{ (Perv!nil) } <--> nil

define unfold_dest_bterm:
   dest_bterm{'t} <--> list_of_xlist{ (Base_reflection!dest_bterm{'t})}

let rec reduce_xlist t =
   if is_xnil_term (one_subterm t) then
      reduce_xlist_nil
   else reduce_xlist_cons thenC addrC [1] (termC reduce_xlist)

let reduce_dest_bterm =
   unfold_dest_bterm thenC addrC [0] Base_reflection.reduce_dest_bterm thenC termC reduce_xlist

let resource reduce +=
   ( << dest_bterm{ sequent [bterm] { <H> >- 't } } >>, reduce_dest_bterm )

interactive_rw test_dest_bterm :
   dest_bterm{ sequent [bterm] { x:term >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} }} <-->
   (sequent [bterm] { x: term >- univ[@,i:l] } :: sequent [bterm] { x: term; y:term >- union[@]{'x;'y}} :: nil)
