extends Ma_recognizer1_object_directory

open Dtactic


define unfold_trigger1 : "trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"} <-->
      "cons"[]{"ma-join-list"[]{"recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}};'"x"}};"cons"[]{"ifthenelse"[]{"eq_id"[]{'"loc";'"i"};"ma-single-pre1"[]{"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}};"bool"[]{};'"a";"unit"[]{};"x", "v"."assert"[]{'"x"}};"ma-empty"[]{}};"nil"[]{}}}


interactive nuprl_trigger1__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}}}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Knd"[]{};"locl"[]{'"a"};'"k"}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"}} }

interactive nuprl_trigger1_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}}}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Knd"[]{};"locl"[]{'"a"};'"k"}} }  -->
   sequent { <H> >- ("trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_trigger1__feasible   :
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}}}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Knd"[]{};"locl"[]{'"a"};'"k"}} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"}}}} }

interactive nuprl_trigger1__realizes   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";"mkid"[]{"token"["trigger":t]{};"number"[0:n]{}}}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Knd"[]{};"locl"[]{'"a"};'"k"}} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"}}};"es"."and"[]{"and"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"};"alle-at"[]{'"es";'"i";"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}};"alle-at"[]{'"es";'"i";"e'"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"exists"[]{"es-E"[]{'"es"};"e"."and"[]{"es-locl"[]{'"es";'"e";'"e'"};"and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"assert"[]{(('"P" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}};"alle-at"[]{'"es";'"i";"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"implies"[]{"assert"[]{(('"P" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})};"existse-at"[]{'"es";'"i";"e'"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}}}}}}}} }


(**** display forms ****)


dform nuprl_trigger1_df : except_mode[src] :: "trigger1"[]{'"loc";'"T";'"A";'"P";'"i";'"k";'"a";'"x"} =
   `"trigger1(" slot{'"loc"} `";" slot{'"T"} `";" slot{'"A"} `";" slot{'"P"} `";"
    slot{'"i"} `";" slot{'"k"} `";" slot{'"a"} `";" slot{'"x"} `")"


