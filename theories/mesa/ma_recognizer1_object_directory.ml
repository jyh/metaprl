extends Nuprl_recognizer1_object_directory

open Dtactic

interactive nuprl_recognizer1__compatible {|intro []|}  :
   [wf] sequent  { <Gamma> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"P" in "fun"[]{'"A";""."fun"[]{'"T";""."bool"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"i" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"r" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- '"A" }  -->
   sequent  { <Gamma> >- '"T" }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"r"}} }  -->
   sequent  { <Gamma> >- "recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"} in pw_compat_list[level:l] }


