extends Ma_trigger1_object_directory

open Dtactic


define unfold_ring__leader1 : "ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"} <-->
      "ifthenelse"[]{('"R" '"loc");"cons"[]{"ma-join-list"[]{"send-once"[]{'"loc";"int"[]{};"int"[]{};"mkid"[]{"token"["send-me":t]{};"number"[0:n]{}};"lambda"[]{"x".'"x"};"mkid"[]{"token"["vote":t]{};"number"[0:n]{}};('"out" '"loc");"mkid"[]{"token"["me":t]{};"number"[0:n]{}}}};"cons"[]{"ma-join-list"[]{"trigger1"[]{'"loc";"int"[]{};"int"[]{};"lambda"[]{"x"."lambda"[]{"y"."beq_int"[]{'"x";'"y"}}};'"loc";"rcv"[]{('"in" '"loc");"mkid"[]{"token"["vote":t]{};"number"[0:n]{}}};"mkid"[]{"token"["leader":t]{};"number"[0:n]{}};"mkid"[]{"token"["me":t]{};"number"[0:n]{}}}};"cons"[]{"ma-join-list"[]{"Dconstant"[]{'"loc";"int"[]{};('"uid" '"loc");"mkid"[]{"token"["me":t]{};"number"[0:n]{}};'"loc"}};"cons"[]{"ma-single-sends1"[]{"int"[]{};"int"[]{};"int"[]{};"mkid"[]{"token"["me":t]{};"number"[0:n]{}};"rcv"[]{('"in" '"loc");"mkid"[]{"token"["vote":t]{};"number"[0:n]{}}};('"out" '"loc");"mkid"[]{"token"["vote":t]{};"number"[0:n]{}};"lambda"[]{"a"."lambda"[]{"b"."ifthenelse"[]{"lt_bool"[]{'"a";'"b"};"cons"[]{'"b";"nil"[]{}};"nil"[]{}}}}};"cons"[]{"ma-single-sframe"[]{"cons"[]{"rcv"[]{('"in" '"loc");"mkid"[]{"token"["vote":t]{};"number"[0:n]{}}};"cons"[]{"locl"[]{"mkid"[]{"token"["send-me":t]{};"number"[0:n]{}}};"nil"[]{}}};('"out" '"loc");"mkid"[]{"token"["vote":t]{};"number"[0:n]{}}};"nil"[]{}}}}}};"nil"[]{}}


interactive nuprl_ring__leader1__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"R"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"}} }

interactive nuprl_ring__leader1_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"R"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- ("ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_ring__leader1__feasible   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"R"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"}}}} }

interactive nuprl_ring__leader1__realizes   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"R"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"}}};"es"."exists"[]{"rset"[]{'"R"};"ldr"."and"[]{"existse-at"[]{'"es";'"ldr";"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{"mkid"[]{"token"["leader":t]{};"number"[0:n]{}}}}};"all"[]{"rset"[]{'"R"};"i"."alle-at"[]{'"es";'"i";"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{"mkid"[]{"token"["leader":t]{};"number"[0:n]{}}}};"equal"[]{"rset"[]{'"R"};'"i";'"ldr"}}}}}}} }


(**** display forms ****)


dform nuprl_ring__leader1_df : except_mode[src] :: "ring-leader1"[]{'"loc";'"R";'"uid";'"out";'"in"} =
   `"ring-leader1(" slot{'"loc"} `";" slot{'"R"} `";" slot{'"uid"} `";"
    slot{'"out"} `";" slot{'"in"} `")"


