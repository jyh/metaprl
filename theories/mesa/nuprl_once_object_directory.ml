extends Ma_Dconstant_object_directory

open Dtactic


define unfold_once : "once"[]{'"loc";'"a";'"i"} <-->
      "ifthenelse"[]{"eq_id"[]{'"loc";'"i"};"cons"[]{"ma-single-pre-init1"[]{"mkid"[]{"token"["done":t]{};"number"[0:n]{}};"bool"[]{};"bfalse"[]{};'"a";"unit"[]{};"x", "v"."not"[]{"assert"[]{'"x"}}};"cons"[]{"ma-single-frame"[]{"cons"[]{"locl"[]{'"a"};"nil"[]{}};"bool"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}}};"cons"[]{"ma-single-effect0"[]{"mkid"[]{"token"["done":t]{};"number"[0:n]{}};"bool"[]{};"locl"[]{'"a"};"unit"[]{};"lambda"[]{"x"."lambda"[]{"v"."btrue"[]{}}}};"nil"[]{}}}};"nil"[]{}}


interactive nuprl_once__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"once"[]{'"loc";'"a";'"i"}} }

interactive nuprl_once_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("once"[]{'"loc";'"a";'"i"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_once__feasible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"once"[]{'"loc";'"a";'"i"}}}} }

interactive nuprl_once__realizes   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"once"[]{'"loc";'"a";'"i"}}};"es"."and"[]{"existse-at"[]{'"es";'"i";"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}}};"alle-at"[]{'"es";'"i";"e"."alle-at"[]{'"es";'"i";"e'"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}}}}}}} }


(**** display forms ****)


dform nuprl_once_df : except_mode[src] :: "once"[]{'"loc";'"a";'"i"} =
   `"once(" slot{'"loc"} `";" slot{'"a"} `";" slot{'"i"} `")"


