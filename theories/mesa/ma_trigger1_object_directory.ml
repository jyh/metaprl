extends Nuprl_trigger1_object_directory

open Dtactic

interactive nuprl_trigger1__compatible {|intro[] |}   :
   [wf] sequent  { <Gamma> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"P" in "fun"[]{'"A";""."fun"[]{'"T";""."bool"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"i" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- '"A" }  -->
   sequent  { <Gamma> >- '"T" }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"x";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}}}} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Knd"[]{};"locl"[]{'"a"};'"k"}} }  -->
   sequent  { <Gamma> >- "trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"} in pw_compat_list[level:l] }

