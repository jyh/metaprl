extends Ma_send__once_object_directory

open Dtactic


define unfold_recognizer1 : "recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"} <-->
      "ifthenelse"[]{"eq_id"[]{'"loc";'"i"};"cons"[]{"ma-single-init"[]{'"r";"bool"[]{};"bfalse"[]{}};"cons"[]{"ma-single-frame"[]{"cons"[]{'"k";"nil"[]{}};"bool"[]{};'"r"};"cons"[]{"ma-single-effect1"[]{'"r";"bool"[]{};'"x";'"A";'"k";'"T";"lambda"[]{"r"."lambda"[]{"x"."lambda"[]{"v"."bor"[]{(('"P" '"x") '"v");'"r"}}}}};"nil"[]{}}}};"nil"[]{}}


interactive nuprl_recognizer1__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"r" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"r"}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"}} }

interactive nuprl_recognizer1_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"r" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"r"}} }  -->
   sequent { <H> >- ("recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_recognizer1__feasible   :
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"r" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"r"}} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"}}}} }

interactive nuprl_recognizer1__realizes   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"r" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"r"}} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"}}};"es"."and"[]{"and"[]{"alle-at"[]{'"es";'"i";"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}};"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"}};"and"[]{"alle-at"[]{'"es";'"i";"e"."implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};"equal"[]{"bool"[]{};"es-when"[]{'"es";'"r";'"e"};"bfalse"[]{}}}};"alle-at"[]{'"es";'"i";"e'"."iff"[]{"assert"[]{"es-after"[]{'"es";'"r";'"e'"}};"exists"[]{"es-E"[]{'"es"};"e"."and"[]{"or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}};"and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"assert"[]{(('"P" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}}}} }


(**** display forms ****)


dform nuprl_recognizer1_df : except_mode[src] :: "recognizer1"[]{'"loc";'"T";'"A";'"P";'"k";'"i";'"r";'"x"} =
   `"recognizer1(" slot{'"loc"} `";" slot{'"T"} `";" slot{'"A"} `";" slot{'"P"}
    `";" slot{'"k"} `";" slot{'"i"} `";" slot{'"r"} `";" slot{'"x"} `")"


