extends Ma_event__system__applications

open Dtactic


define unfold_Dconstant : "Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"} <-->
      "ifthenelse"[]{"eq_id"[]{'"loc";'"i"};"cons"[]{"ma-single-init"[]{'"x";'"T";'"c"};"cons"[]{"ma-single-frame"[]{"nil"[]{};'"T";'"x"};"nil"[]{}}};"nil"[]{}}


interactive nuprl_Dconstant__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"}} }

interactive nuprl_Dconstant_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_Dconstant__feasible   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"}}}} }

interactive nuprl_Dconstant__realizes   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"}}};"es"."alle-at"[]{'"es";'"i";"e"."equal"[]{'"T";"es-when"[]{'"es";'"x";'"e"};'"c"}}} }


(**** display forms ****)


dform nuprl_Dconstant_df : except_mode[src] :: "Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"} =
   `"Dconstant(" slot{'"loc"} `";" slot{'"T"} `";" slot{'"c"} `";" slot{'"x"} `";"
    slot{'"i"} `")"


