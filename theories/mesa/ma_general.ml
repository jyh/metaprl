extends Nuprl_general

open Dtactic
(*
define nuprl_pairwise : "pairwise"[]{x, y.'P['x;'y];'L} <-->
    list_ind{ 'L;  "true";  hd, tl, g.  all_list{'tl; x. 'P['hd;'x]} and 'g}
*)

interactive nuprl_pairwise_nil {| intro[] |}  :
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['x;'y]; nil} }

interactive nuprl_pairwise_cons  {| intro[] |}  :
   sequent  { <Gamma> >- all_list{'tl; x. 'P['hd;'x]} }  -->
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['x;'y]; 'tl } }  -->
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['x;'y]; 'hd::'tl } }

interactive nuprl_pairwise_map  {| intro[] |}  :
   [wf] sequent  { <Gamma> >- 'l in "list"{top} }  -->
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['f 'x;'f 'y]; 'l } }  -->
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['x;'y]; map{'f;'l}} }

interactive nuprl_pairwise_if  {| intro[] (*???*)|}  :
   [wf] sequent  { <Gamma> >- 'b in bool }  -->
   sequent  { <Gamma>; "assert"{'b} >- "pairwise"[]{"x", "y".'P['x;'y]; 'l_1} }  -->
   sequent  { <Gamma>; "assert"{bnot{'b}} >- "pairwise"[]{"x", "y".'P['x;'y]; 'l_2} }  -->
   sequent  { <Gamma> >- "pairwise"[]{"x", "y".'P['x;'y]; if 'b then 'l_1 else 'l_2} }


