extends Nuprl_send__once_object_directory

open Dtactic

interactive nuprl_send_once__compatible   {|intro[] |} :
   [wf] sequent  { <Gamma> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "fun"[]{'"A";"".'"T"} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}};'"x"}} }  -->
   sequent  { <Gamma> >- '"A" }  -->
   sequent  { <Gamma> >- '"T" }  -->
   sequent  { <Gamma> >- "send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"} in pw_compat_list[level:l] }


