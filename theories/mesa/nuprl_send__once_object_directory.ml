extends Ma_once_object_directory

open Dtactic


define unfold_send__once : "send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"} <-->
      "cons"[]{"ma-join-list"[]{"once"[]{'"loc";'"a";"lsrc"[]{'"l"}}};"cons"[]{"ifthenelse"[]{"eq_id"[]{'"loc";"lsrc"[]{'"l"}};"ma-single-sends1"[]{'"A";"unit"[]{};'"T";'"x";"locl"[]{'"a"};'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{('"f" '"a");"nil"[]{}}}}};"ma-empty"[]{}};"nil"[]{}}}


interactive nuprl_send__once__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}};'"x"}} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"}} }

interactive nuprl_send__once_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}};'"x"}} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- ("send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_send__once__feasible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}};'"x"}} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"}}}} }

interactive nuprl_send__once__realizes   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};"mkid"[]{"token"["done":t]{};"number"[0:n]{}};'"x"}} }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"}}};"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";"lsrc"[]{'"l"};'"x"};'"A"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}};"exists"[]{"es-E"[]{'"es"};"e"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"and"[]{"equal"[]{'"T";"es-val"[]{'"es";'"e"};('"f" "es-when"[]{'"es";'"x";"es-sender"[]{'"es";'"e"}})};"and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";"es-sender"[]{'"es";'"e"}};"locl"[]{'"a"}};"all"[]{"es-E"[]{'"es"};"e'"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";"es-sender"[]{'"es";'"e'"}};"locl"[]{'"a"}};"equal"[]{"es-E"[]{'"es"};'"e'";'"e"}}}}}}}}}} }


(**** display forms ****)


dform nuprl_send__once_df : except_mode[src] :: "send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"} =
   `"send-once(" slot{'"loc"} `";" slot{'"T"} `";" slot{'"A"} `";" slot{'"a"} `";"
    slot{'"f"} `";" slot{'"tg"} `";" slot{'"l"} `";" slot{'"x"} `")"


