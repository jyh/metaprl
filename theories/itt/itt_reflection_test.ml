extends Itt_theory
extends Itt_reflection
extends Base_reflection

open Basic_tactics
open Base_reflection
open Itt_reflection

interactive wellformed_bterm_example 'J :
   sequent { <H> >-
    is_bterm{ bterm{| <J>; x:term; <K> >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} |} } }

interactive isbterm_wf1 'J :
   sequent { <H> >-
    is_bterm{ bterm{| <J>; x:term; <K> >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} |} } Type }



interactive_rw test_subterms :
   Itt_reflection!subterms{ bterm{| x:term >- prod[@]{univ[@,i:l];y.union[@]{'x;'y}} |} } <-->
   ((bterm{| x: term >- univ[@,i:l] |}) :: (bterm{| x: term; y:term >- union[@]{'x;'y} |}) :: nil)


interactive isbterm_example :
   sequent { <H> >- is_bterm{ bterm{| >- 'A |} } } -->
   sequent { <H> >- is_bterm{ bterm{| >- 'B |} } } -->
   sequent { <H> >- is_bterm{ bterm{| >- prod[@]{'A; 'B} |} } }
