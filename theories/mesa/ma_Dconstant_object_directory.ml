extends Nuprl_Dconstant_object_directory

open Dtactic

interactive nuprl_Dconstant_wf {|intro[] |}   :
   [wf] sequent  { <Gamma> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"c" in '"T" }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"i" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"} in pw_compat_list[level:l] }
