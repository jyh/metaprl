extends Nuprl_once_object_directory


open Dtactic

interactive nuprl_once__compatible  {|intro[]  |} :
   [wf] sequent  { <Gamma> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"i" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "once"[]{'"loc";'"a";'"i"} in pw_compat_list[level:l] }

