extends Ma_decidable__equality

open Dtactic


define unfold_event_system_typename : "event_system_typename"[]{} <-->
      "int_seg"[]{"number"[0:n]{};"number"[6:n]{}}


interactive nuprl_event_system_typename_wf {| intro[] |}   :
   sequent { <H> >- ("event_system_typename"[]{} in "univ"[level:l]{}) }

interactive nuprl_event_system_typename_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"event_system_typename"[]{}} }

define unfold_strongwellfounded : "strongwellfounded"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "exists"[]{"fun"[]{'"T";""."nat"[]{}};"f"."all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{'"R"['"x";'"y"];"lt"[]{('"f" '"x");('"f" '"y")}}}}}


interactive nuprl_strongwellfounded_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("strongwellfounded"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_strongwf__implies  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "well_founded"[level:l]{'"T";"x", "y".'"R"['"x";'"y"]} }

define unfold_rel_plus : "rel_plus"[]{'"T";'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."exists"[]{"nat_plus"[]{};"n"."infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"x";'"y"}}}}


interactive nuprl_rel_plus_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_plus"[]{'"T";'"R"} in "fun"[]{'"T";""."fun"[]{'"T";""."univ"[level:l]{}}}) }

interactive nuprl_rel_plus_trans   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "trans"[]{'"T";"x", "y"."infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"}} }

interactive nuprl_rel_plus_strongwellfounded   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "strongwellfounded"[]{'"T";"x", "y"."infix_ap"[]{'"R";'"x";'"y"}} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"T";"x", "y"."infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"}} }

interactive nuprl_rel_plus_implies   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "or"[]{"infix_ap"[]{'"R";'"x";'"y"};"exists"[]{'"T";"z"."and"[]{"infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"z"};"infix_ap"[]{'"R";'"z";'"y"}}}} }

interactive nuprl_rel_exp_iff   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"x";'"y"};"or"[]{"exists"[]{'"T";"z"."cand"[]{"lt"[]{"number"[0:n]{};'"n"};"and"[]{"infix_ap"[]{"rel_exp"[]{'"T";'"R";"sub"[]{'"n";"number"[1:n]{}}};'"x";'"z"};"infix_ap"[]{'"R";'"z";'"y"}}}};"and"[]{"equal"[]{"int"[]{};'"n";"number"[0:n]{}};"equal"[]{'"T";'"x";'"y"}}}} }

interactive nuprl_rel_star_iff   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"};"or"[]{"exists"[]{'"T";"z"."and"[]{"infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"z"};"infix_ap"[]{'"R";'"z";'"y"}}};"equal"[]{'"T";'"x";'"y"}}} }

interactive nuprl_rel__star__iff__rel__plus__or   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"};"or"[]{"infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"};"equal"[]{'"T";'"x";'"y"}}} }

interactive nuprl_rel__rel__plus   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{'"R";'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"} }

interactive nuprl_rel__star__rel__plus  '"y"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{'"R";'"y";'"z"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"z"} }

interactive nuprl_rel__plus__rel__star   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }

interactive nuprl_rel_plus_iff   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_plus"[]{'"T";'"R"};'"x";'"z"};"exists"[]{'"T";"y"."and"[]{"infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"};"infix_ap"[]{'"R";'"y";'"z"}}}} }

interactive nuprl_rel_plus_monotone   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R1";'"R2"} }  -->
   sequent { <H> >- "rel_implies"[]{'"T";"rel_plus"[]{'"T";'"R1"};"rel_plus"[]{'"T";'"R2"}} }

define unfold_first : "first"[]{'"pred?";'"e"} <-->
      "bnot"[]{"is_inl"[]{('"pred?" '"e")}}


interactive nuprl_first_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- ("first"[]{'"pred?";'"e"} in "bool"[]{}) }

define unfold_pred : "pred"[]{'"pred?";'"e"} <-->
      "outl"[]{('"pred?" '"e")}


interactive nuprl_pred_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}} }  -->
   sequent { <H> >- ("pred"[]{'"pred?";'"e"} in '"E") }

define unfold_ecase1 : "ecase1"[]{'"e";'"info";"i".'"f"['"i"];"l", "e'".'"g"['"l";'"e'"]} <-->
      "decide"[]{('"info" '"e");"p".'"f"["fst"[]{'"p"}];"q".'"g"["fst"[]{"fst"[]{'"q"}};"snd"[]{"fst"[]{'"q"}}]}


interactive nuprl_ecase1_wf {| intro[] |}  '"X2" '"X1" '"E" '"T" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x".'"f"['"x"]} '"info" '"e"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"f"['"x"] in '"T" }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": '"E" >- '"g"['"x";'"x1"] in '"T" }  -->
   sequent { <H> >- ("ecase1"[]{'"e";'"info";"i".'"f"['"i"];"l", "e'".'"g"['"l";'"e'"]} in '"T") }

define unfold_loc : "loc"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i".'"i";"l", "e'"."ldst"[]{'"l"}}


interactive nuprl_loc_wf {| intro[] |}  '"X2" '"X1" '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- ("loc"[]{'"info";'"e"} in "Id"[]{}) }

define unfold_rcv__ : "rcv?"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."bfalse"[]{};"l", "e'"."btrue"[]{}}


interactive nuprl_rcv___wf {| intro[] |}  '"X2" '"X1" '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- ("rcv?"[]{'"info";'"e"} in "bool"[]{}) }

define unfold_sender : "sender"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."it"[]{};"l", "e'".'"e'"}


interactive nuprl_sender_wf {| intro[] |}  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"e"}} }  -->
   sequent { <H> >- ("sender"[]{'"info";'"e"} in '"E") }

define unfold_link : "link"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."it"[]{};"l", "e'".'"l"}


interactive nuprl_link_wf {| intro[] |}  '"X2" '"X1" '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"e"}} }  -->
   sequent { <H> >- ("link"[]{'"info";'"e"} in "IdLnk"[]{}) }

define unfold_pred__ : "pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"} <-->
      "or"[]{"cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}};"cand"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"equal"[]{'"E";'"e";"sender"[]{'"info";'"e'"}}}}


interactive nuprl_pred___wf {| intro[] |}  '"X2" '"X1"  :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"e'" in '"E" }  -->
   sequent { <H> >- ("pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"} in "univ"[level:l]{}) }

define unfold_cless : "cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} <-->
      (("rel_plus"[]{'"E";"lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}} '"e") '"e'")


interactive nuprl_cless_wf {| intro[] |}  '"X2" '"X1"  :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"e'" in '"E" }  -->
   sequent { <H> >- ("cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} in "univ"[level:l]{}) }

interactive nuprl_cless__eq__loc  '"X2" '"X1" '"info"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}} }  -->
   sequent { <H>; "e": '"E" ; "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}}  >- "equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}} }  -->
   sequent { <H>; "e": '"E" ; "e'": '"E" ; "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} ; "equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")}  >- "equal"[]{'"E";'"e";'"e'"} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"e'" in '"E" }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} }  -->
   sequent { <H> >- "cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_plus"[]{'"E";"lambda"[]{"x"."lambda"[]{"y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}}}};'"e";'"e'"} }

define unfold_sends__bound : "sends-bound"[]{'"p";'"e";'"l"} <-->
      "fst"[]{(('"p" '"e") '"l")}


interactive nuprl_sends__bound_wf {| intro[] |}  '"X2" '"X1" '"pred?" '"info"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("sends-bound"[]{'"p";'"e";'"l"} in '"E") }

interactive nuprl_sends__bound__property  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";"sends-bound"[]{'"p";'"e";'"l"}};"cless"[]{'"E";'"pred?";'"info";'"e''";"sends-bound"[]{'"p";'"e";'"l"}}};"equal"[]{"Id"[]{};"loc"[]{'"info";"sends-bound"[]{'"p";'"e";'"l"}};"ldst"[]{'"l"}}}}}}}} }

interactive nuprl_strong__sends__bound__property  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   [wf] sequent { <H> >- '"r" in '"E" }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}} }  -->
   sequent { <H>; "e": '"E" ; "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}}  >- "equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}} }  -->
   sequent { <H>; "e": '"E" ; "e'": '"E" ; "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} ; "equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")}  >- "equal"[]{'"E";'"e";'"e'"} }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"r"}} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"E";"lambda"[]{"x"."lambda"[]{"y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}}}};'"r";"sends-bound"[]{'"p";"sender"[]{'"info";'"r"};"link"[]{'"info";'"r"}}} }

define unfold_eventlist : "eventlist"[]{'"pred?";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"eventlist"."lambda"[]{"e"."ifthenelse"[]{"first"[]{'"pred?";'"e"};"cons"[]{'"e";"nil"[]{}};"append"[]{('"eventlist" "pred"[]{'"pred?";'"e"});"cons"[]{'"e";"nil"[]{}}}}}}) '"e")


interactive nuprl_eventlist_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"x", "y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}} }  -->
   sequent { <H> >- ("eventlist"[]{'"pred?";'"e"} in "list"[]{'"E"}) }

interactive nuprl_member_eventlist   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"x", "y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"e'" in '"E" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"e'";"eventlist"[]{'"pred?";'"e"};'"E"};"infix_ap"[]{"rel_star"[]{'"E";"lambda"[]{"x"."lambda"[]{"y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}}}};'"e'";'"e"}} }

interactive nuprl_l_before_eventlist  '"X2" '"X1" '"x"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"r1" in '"E" }  -->
   [wf] sequent { <H> >- '"r2" in '"E" }  -->
   [wf] sequent { <H> >- '"x" in '"E" }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"x", "y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}} }  -->
   sequent { <H> >- "l_before"[]{'"r2";'"r1";"eventlist"[]{'"pred?";'"x"};'"E"} }  -->
   sequent { <H> >- "cless"[]{'"E";'"pred?";'"info";'"r2";'"r1"} }

define unfold_rcv__from__on : "rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"} <-->
      "band"[]{"rcv?"[]{'"info";'"r"};"band"[]{(("eqof"[]{'"dE"} '"e") "sender"[]{'"info";'"r"});(("eqof"[]{'"dL"} '"l") "link"[]{'"info";'"r"})}}


interactive nuprl_rcv__from__on_wf {| intro[] |}  '"E" '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"r" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"} in "bool"[]{}) }

interactive nuprl_assert__rcv__from__on  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"r" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"}};"cand"[]{"assert"[]{"rcv?"[]{'"info";'"r"}};"and"[]{"equal"[]{'"E";"sender"[]{'"info";'"r"};'"e"};"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"r"};'"l"}}}} }

define unfold_receives : "receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"} <-->
      "filter"[]{"lambda"[]{"r"."rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"}};"eventlist"[]{'"pred?";"sends-bound"[]{'"p";'"e";'"l"}}}


interactive nuprl_receives_wf {| intro[] |}  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"x", "y"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"y"}}};"equal"[]{'"E";'"x";"pred"[]{'"pred?";'"y"}}}} }  -->
   sequent { <H> >- ("receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"} in "list"[]{"set"[]{'"E";"r"."assert"[]{"rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"}}}}) }

interactive nuprl_member_receives  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}} }  -->
   sequent { <H>; "e": '"E" ; "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}}  >- "equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}} }  -->
   sequent { <H>; "e": '"E" ; "e'": '"E" ; "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} ; "equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")}  >- "equal"[]{'"E";'"e";'"e'"} }  -->
   [wf] sequent { <H> >- '"r" in '"E" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"r";"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"};'"E"};"cand"[]{"assert"[]{"rcv?"[]{'"info";'"r"}};"and"[]{"equal"[]{'"E";"sender"[]{'"info";'"r"};'"e"};"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"r"};'"l"}}}} }

define unfold_index : "index"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"r"} <-->
      "mu"[]{"lambda"[]{"i".(("eqof"[]{'"dE"} '"r") "select"[]{'"i";"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";"sender"[]{'"info";'"r"};"link"[]{'"info";'"r"}}})}}


interactive nuprl_index_wf {| intro[] |}  '"E" '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}} }  -->
   sequent { <H>; "e": '"E" ; "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}}  >- "equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}} }  -->
   sequent { <H>; "e": '"E" ; "e'": '"E" ; "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} ; "equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")}  >- "equal"[]{'"E";'"e";'"e'"} }  -->
   [wf] sequent { <H> >- '"r" in '"E" }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"r"}} }  -->
   sequent { <H> >- ("index"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"r"} in "int_seg"[]{"number"[0:n]{};"length"[]{"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";"sender"[]{'"info";'"r"};"link"[]{'"info";'"r"}}}}) }

interactive nuprl_index__property1  '"X2" '"X1"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"X1" } }  -->
   [wf] sequent { <H> >- "type"{'"X2" } }  -->
   [wf] sequent { <H> >- '"dE" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"dL" in "deq"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   [wf] sequent { <H> >- '"p" in "all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}} }  -->
   sequent { <H> >- "strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}} }  -->
   sequent { <H>; "e": '"E" ; "not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}}  >- "equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}} }  -->
   sequent { <H>; "e": '"E" ; "e'": '"E" ; "equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}} ; "equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")}  >- "equal"[]{'"E";'"e";'"e'"} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"length"[]{"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"}}} }  -->
   sequent { <H> >- "exists"[]{'"E";"e'"."cand"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"and"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e'"};'"l"};"and"[]{"equal"[]{'"E";"sender"[]{'"info";'"e'"};'"e"};"equal"[]{"int"[]{};"index"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e'"};'"n"}}}}} }

define unfold_EOrderAxioms : "EOrderAxioms"[level:l]{'"E";'"pred?";'"info"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")};"equal"[]{'"E";'"e";'"e'"}}}}};"and"[]{"strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"equal"[]{"Id"[]{};"loc"[]{'"info";"sender"[]{'"info";'"e"}};"lsrc"[]{"link"[]{'"info";'"e"}}}}};"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"implies"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e"};"link"[]{'"info";'"e'"}};"implies"[]{"cless"[]{'"E";'"pred?";'"info";"sender"[]{'"info";'"e"};"sender"[]{'"info";'"e'"}};"cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}}}}}}}}}}


interactive nuprl_EOrderAxioms_wf {| intro[] |}  '"X2" '"X1"  :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H> >- '"X1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"X1"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};"".'"X2"}} }  -->
   sequent { <H> >- ("EOrderAxioms"[level:l]{'"E";'"pred?";'"info"} in "univ"[level':l]{}) }

define unfold_EOrder : "EOrder"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."top"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."top"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."top"[]{}}}}}}


interactive nuprl_EOrder_wf {| intro[] |}   :
   sequent { <H> >- ("EOrder"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_EOrder_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"EOrder"[level:l]{}} }

define unfold_EState : "EState"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."top"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."top"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."top"[]{}}}}}}}}}}


interactive nuprl_EState_wf {| intro[] |}   :
   sequent { <H> >- ("EState"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_EState_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"EState"[level:l]{}} }

interactive nuprl_EState__subtype__EOrder   :
   sequent { <H> >- "subtype"[]{"EState"[level:l]{};"EOrder"[level:l]{}} }

define unfold_EKind : "EKind"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"top"[]{};"unused"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."top"[]{}}}}}}}}}}}


interactive nuprl_EKind_wf {| intro[] |}   :
   sequent { <H> >- ("EKind"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_EKind_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"EKind"[level:l]{}} }

define unfold_kind : "kind"[]{'"info";'"e"} <-->
      "decide"[]{('"info" '"e");"p"."locl"[]{"snd"[]{'"p"}};"q"."rcv"[]{"fst"[]{"fst"[]{'"q"}};"snd"[]{'"q"}}}


interactive nuprl_kind_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- ("kind"[]{'"info";'"e"} in "Knd"[]{}) }

define unfold_rtag : "rtag"[]{'"info";'"e"} <-->
      "decide"[]{('"info" '"e");"p"."it"[]{};"q"."snd"[]{'"q"}}


interactive nuprl_rtag_wf {| intro[] |}  '"A" '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};"".'"A"};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"e"}} }  -->
   sequent { <H> >- ("rtag"[]{'"info";'"e"} in "Id"[]{}) }

define unfold_EVal : "EVal"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."prod"[]{"fun"[]{"Knd"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"V"."prod"[]{"fun"[]{'"E";"e".(('"V" "kind"[]{'"info";'"e"}) "loc"[]{'"info";'"e"})};"val"."top"[]{}}}}}}}}}}}}


interactive nuprl_EVal_wf {| intro[] |}   :
   sequent { <H> >- ("EVal"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_EVal_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"EVal"[level:l]{}} }

define unfold_rmsg : "rmsg"[]{'"info";'"val";'"e"} <-->
      "msg"[]{"link"[]{'"info";'"e"};"rtag"[]{'"info";'"e"};('"val" '"e")}


interactive nuprl_rmsg_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": "Knd"[]{};"x1": "Id"[]{} >- "type"{'"V" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H>;"e": '"E" >- '"val" '"e" in (('"V" "kind"[]{'"info";'"e"}) "loc"[]{'"info";'"e"}) }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "assert"[]{"rcv?"[]{'"info";'"e"}} }  -->
   sequent { <H> >- ("rmsg"[]{'"info";'"val";'"e"} in "Msg"[]{"lambda"[]{"l"."lambda"[]{"tg".(('"V" "rcv"[]{'"l";'"tg"}) "ldst"[]{'"l"})}}}) }

define unfold_sends : "sends"[]{'"dE";'"dL";'"pred?";'"info";'"val";'"p";'"e";'"l"} <-->
      "map"[]{"lambda"[]{"r"."rmsg"[]{'"info";'"val";'"r"}};"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"}}


define unfold_SESAxioms : "SESAxioms"[level:l]{'"E";'"T";'"pred?";'"info";'"when";'"after"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}};"cand"[]{"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")};"equal"[]{'"E";'"e";'"e'"}}}}};"and"[]{"strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"equal"[]{"Id"[]{};"loc"[]{'"info";"sender"[]{'"info";'"e"}};"lsrc"[]{"link"[]{'"info";'"e"}}}}};"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"implies"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e"};"link"[]{'"info";'"e'"}};"implies"[]{"cless"[]{'"E";'"pred?";'"info";"sender"[]{'"info";'"e"};"sender"[]{'"info";'"e'"}};"cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}}}}}}}}};"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}}}}


interactive nuprl_SESAxioms_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"T" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"when" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"after" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   sequent { <H> >- ("SESAxioms"[level:l]{'"E";'"T";'"pred?";'"info";'"when";'"after"} in "univ"[level':l]{}) }

define unfold_eventtype : "eventtype"[]{'"k";'"loc";'"V";'"M";'"e"} <-->
      "kindcase"[]{('"k" '"e");"a".(('"V" ('"loc" '"e")) '"a");"l", "t".(('"M" '"l") '"t")}


interactive nuprl_eventtype_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"V" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"loc" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"k" '"x" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- ("eventtype"[]{'"k";'"loc";'"V";'"M";'"e"} in "univ"[level:l]{}) }

interactive nuprl_eventtype_wf_type {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- "type"{'"V" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"loc" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"k" '"x" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"e" in '"E" }  -->
   sequent { <H> >- "type"{"eventtype"[]{'"k";'"loc";'"V";'"M";'"e"}} }

define unfold_ESAxioms : "ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e");('"loc" '"e'")};"or"[]{(('"causl" '"e") '"e'");"or"[]{"equal"[]{'"E";'"e";'"e'"};(('"causl" '"e'") '"e")}}}}};"and"[]{"all"[]{'"E";"e"."iff"[]{"assert"[]{('"first" '"e")};"all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e'");('"loc" '"e")};"not"[]{(('"causl" '"e'") '"e")}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{('"first" '"e")}};"and"[]{"and"[]{"equal"[]{"Id"[]{};('"loc" ('"pred" '"e"));('"loc" '"e")};(('"causl" ('"pred" '"e")) '"e")};"all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e'");('"loc" '"e")};"not"[]{"and"[]{(('"causl" ('"pred" '"e")) '"e'");(('"causl" '"e'") '"e")}}}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{('"first" '"e")}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" ('"loc" '"e")) '"x");(('"when" '"x") '"e");(('"after" '"x") ('"pred" '"e"))}}}};"and"[]{"trans"[]{'"E";"e", "e'".(('"causl" '"e") '"e'")};"and"[]{"strongwellfounded"[]{'"E";"e", "e'".(('"causl" '"e") '"e'")};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"equal"[]{"Msg"[]{'"M"};"select"[]{('"index" '"e");(('"sends" "lnk"[]{('"kind" '"e")}) ('"sender" '"e"))};"msg"[]{"lnk"[]{('"kind" '"e")};"tagof"[]{('"kind" '"e")};('"val" '"e")}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};(('"causl" ('"sender" '"e")) '"e")}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{(('"causl" '"e") '"e'");"or"[]{"cand"[]{"not"[]{"assert"[]{('"first" '"e'")}};"or"[]{(('"causl" '"e") ('"pred" '"e'"));"equal"[]{'"E";'"e";('"pred" '"e'")}}};"cand"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"or"[]{(('"causl" '"e") ('"sender" '"e'"));"equal"[]{'"E";'"e";('"sender" '"e'")}}}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"equal"[]{"Id"[]{};('"loc" '"e");"ldst"[]{"lnk"[]{('"kind" '"e")}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."implies"[]{"not"[]{"equal"[]{"Id"[]{};('"loc" '"e");"lsrc"[]{'"l"}}};"equal"[]{"list"[]{"Msg_sub"[]{'"l";'"M"}};(('"sends" '"l") '"e");"nil"[]{}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"implies"[]{"equal"[]{"IdLnk"[]{};"lnk"[]{('"kind" '"e")};"lnk"[]{('"kind" '"e'")}};"iff"[]{(('"causl" '"e") '"e'");"or"[]{(('"causl" ('"sender" '"e")) ('"sender" '"e'"));"and"[]{"equal"[]{'"E";('"sender" '"e");('"sender" '"e'")};"lt"[]{('"index" '"e");('"index" '"e'")}}}}}}}}};"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{(('"sends" '"l") '"e")}};"n"."exists"[]{'"E";"e'"."cand"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"and"[]{"equal"[]{"IdLnk"[]{};"lnk"[]{('"kind" '"e'")};'"l"};"and"[]{"equal"[]{'"E";('"sender" '"e'");'"e"};"equal"[]{"int"[]{};('"index" '"e'");'"n"}}}}}}}}}}}}}}}}}}}}


interactive nuprl_ESAxioms_wf {| intro[] |}  '"V"  :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"T" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"V" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"loc" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"kind" '"x" in "Knd"[]{} }  -->
   [wf] sequent { <H>;"e": '"E" >- '"val" '"e" in "eventtype"[]{'"kind";'"loc";'"V";'"M";'"e"} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"when" '"x" '"e" in (('"T" ('"loc" '"e")) '"x") }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"after" '"x" '"e" in (('"T" ('"loc" '"e")) '"x") }  -->
   [wf] sequent { <H>;"l": "IdLnk"[]{};"x": '"E" >- '"sends" '"l" '"x" in "list"[]{"Msg_sub"[]{'"l";'"M"}} }  -->
   [wf] sequent { <H>;"x": "set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}} >- '"sender" '"x" in '"E" }  -->
   [wf] sequent { <H>;"e": "set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}} >- '"index" '"e" in "int_seg"[]{"number"[0:n]{};"length"[]{(('"sends" "lnk"[]{('"kind" '"e")}) ('"sender" '"e"))}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"first" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"e'": "set"[]{'"E";"e'"."not"[]{"assert"[]{('"first" '"e'")}}} >- '"pred" '"e'" in '"E" }  -->
   [wf] sequent { <H>;"x": '"E";"x1": '"E" >- '"causl" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"} in "univ"[level':l]{}) }

interactive nuprl_SES__implies__ES   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"T" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Knd"[]{};"x1": "Id"[]{} >- '"V" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"pred?" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"e": '"E" >- '"val" '"e" in (('"V" "kind"[]{'"info";'"e"}) "loc"[]{'"info";'"e"}) }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"when" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"after" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   [wf] sequent { <H> >- '"p" in "SESAxioms"[level:l]{'"E";'"T";'"pred?";'"info";'"when";'"after"} }  -->
   sequent { <H> >- "ESAxioms"[level:l]{'"E";'"T";"lambda"[]{"l"."lambda"[]{"tg".(('"V" "rcv"[]{'"l";'"tg"}) "ldst"[]{'"l"})}};"lambda"[]{"e"."loc"[]{'"info";'"e"}};"lambda"[]{"e"."kind"[]{'"info";'"e"}};'"val";'"when";'"after";"lambda"[]{"l"."lambda"[]{"e"."sends"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";'"val";"fst"[]{'"p"};'"e";'"l"}}};"lambda"[]{"e"."sender"[]{'"info";'"e"}};"lambda"[]{"e"."index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"p"};'"e"}};"lambda"[]{"e"."first"[]{'"pred?";'"e"}};"lambda"[]{"e"."pred"[]{'"pred?";'"e"}};"lambda"[]{"e"."lambda"[]{"e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}} }

define unfold_event_system : "event_system"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"V"."prod"[]{"fun"[]{"IdLnk"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"M"."prod"[]{"top"[]{};"unused"."prod"[]{"fun"[]{'"E";""."Id"[]{}};"loc"."prod"[]{"fun"[]{'"E";""."Knd"[]{}};"kind"."prod"[]{"fun"[]{'"E";"e"."eventtype"[]{'"kind";'"loc";'"V";'"M";'"e"}};"val"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" ('"loc" '"e")) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" ('"loc" '"e")) '"x")}};"after"."prod"[]{"fun"[]{"IdLnk"[]{};"l"."fun"[]{'"E";""."list"[]{"Msg_sub"[]{'"l";'"M"}}}};"sends"."prod"[]{"fun"[]{"set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}};"".'"E"};"sender"."prod"[]{"fun"[]{"set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}};"e"."int_seg"[]{"number"[0:n]{};"length"[]{(('"sends" "lnk"[]{('"kind" '"e")}) ('"sender" '"e"))}}};"index"."prod"[]{"fun"[]{'"E";""."bool"[]{}};"first"."prod"[]{"fun"[]{"set"[]{'"E";"e'"."not"[]{"assert"[]{('"first" '"e'")}}};"e'".'"E"};"pred"."prod"[]{"fun"[]{'"E";""."fun"[]{'"E";""."univ"[level:l]{}}};"causl"."prod"[]{"ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"};"p"."top"[]{}}}}}}}}}}}}}}}}}}}


interactive nuprl_event_system_wf {| intro[] |}   :
   sequent { <H> >- ("event_system"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_event_system_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"event_system"[level:l]{}} }

define unfold_mk__es : "mk-es"[]{'"E";'"eq";'"T";'"V";'"M";'"loc";'"k";'"v";'"w";'"a";'"snds";'"sndr";'"i";'"f";'"prd";'"cl";'"p"} <-->
      "pair"[]{'"E";"pair"[]{'"eq";"pair"[]{'"T";"pair"[]{'"V";"pair"[]{'"M";"pair"[]{"it"[]{};"pair"[]{'"loc";"pair"[]{'"k";"pair"[]{'"v";"pair"[]{'"w";"pair"[]{'"a";"pair"[]{'"snds";"pair"[]{'"sndr";"pair"[]{'"i";"pair"[]{'"f";"pair"[]{'"prd";"pair"[]{'"cl";"pair"[]{'"p";"it"[]{}}}}}}}}}}}}}}}}}}}


interactive nuprl_mk__es_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"T" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"V" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"loc" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"k" '"x" in "Knd"[]{} }  -->
   [wf] sequent { <H>;"e": '"E" >- '"v" '"e" in "eventtype"[]{'"k";'"loc";'"V";'"M";'"e"} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"w" '"x" '"e" in (('"T" ('"loc" '"e")) '"x") }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"a" '"x" '"e" in (('"T" ('"loc" '"e")) '"x") }  -->
   [wf] sequent { <H>;"l": "IdLnk"[]{};"x": '"E" >- '"snds" '"l" '"x" in "list"[]{"Msg_sub"[]{'"l";'"M"}} }  -->
   [wf] sequent { <H>;"x": "set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"k" '"e")}}} >- '"sndr" '"x" in '"E" }  -->
   [wf] sequent { <H>;"e": "set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"k" '"e")}}} >- '"i" '"e" in "int_seg"[]{"number"[0:n]{};"length"[]{(('"snds" "lnk"[]{('"k" '"e")}) ('"sndr" '"e"))}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"f" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"e'": "set"[]{'"E";"e'"."not"[]{"assert"[]{('"f" '"e'")}}} >- '"prd" '"e'" in '"E" }  -->
   [wf] sequent { <H>;"x": '"E";"x1": '"E" >- '"cl" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"p" in "ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"k";'"v";'"w";'"a";'"snds";'"sndr";'"i";'"f";'"prd";'"cl"} }  -->
   sequent { <H> >- ("mk-es"[]{'"E";'"eq";'"T";'"V";'"M";'"loc";'"k";'"v";'"w";'"a";'"snds";'"sndr";'"i";'"f";'"prd";'"cl";'"p"} in "event_system"[level:l]{}) }

define unfold_mk__eval : "mk-eval"[]{'"E";'"eq";'"prd";'"info";'"oax";'"T";'"w";'"a";'"sax";'"V";'"v"} <-->
      "pair"[]{'"E";"pair"[]{'"eq";"pair"[]{'"prd";"pair"[]{'"info";"pair"[]{'"oax";"pair"[]{'"T";"pair"[]{'"w";"pair"[]{'"a";"pair"[]{'"sax";"pair"[]{'"V";"pair"[]{'"v";"it"[]{}}}}}}}}}}}}


interactive nuprl_mk__eval_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"E"} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"prd" '"x" in "union"[]{'"E";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"E" >- '"info" '"x" in "union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}} }  -->
   [wf] sequent { <H> >- '"oax" in "EOrderAxioms"[level:l]{'"E";'"prd";'"info"} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"T" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"w" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"e": '"E" >- '"a" '"x" '"e" in (('"T" "loc"[]{'"info";'"e"}) '"x") }  -->
   [wf] sequent { <H> >- '"sax" in "all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"prd";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"w" '"x") '"e");(('"a" '"x") "pred"[]{'"prd";'"e"})}}}} }  -->
   [wf] sequent { <H>;"x": "Knd"[]{};"x1": "Id"[]{} >- '"V" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"e": '"E" >- '"v" '"e" in (('"V" "kind"[]{'"info";'"e"}) "loc"[]{'"info";'"e"}) }  -->
   sequent { <H> >- ("mk-eval"[]{'"E";'"eq";'"prd";'"info";'"oax";'"T";'"w";'"a";'"sax";'"V";'"v"} in "EVal"[level:l]{}) }

interactive nuprl_EVal__to__ES   :
   sequent { <H> >- "EVal"[level:l]{} }  -->
   sequent { <H> >- "event_system"[level:l]{} }

define unfold_EVal_to_ES : "EVal_to_ES"[level:l]{'"e"} <-->
      "spread"[]{'"e";"E", "e1"."spread"[]{'"e1";"eq", "e2"."spread"[]{'"e2";"pred?", "e3"."spread"[]{'"e3";"info", "e4"."spread"[]{'"e4";"oaxioms", "e5"."spread"[]{'"e5";"T", "e6"."spread"[]{'"e6";"when", "e7"."spread"[]{'"e7";"after", "e8"."spread"[]{'"e8";"saxiom", "e9"."spread"[]{'"e9";"V", "e10"."spread"[]{'"e10";"val", "e11"."spread"[]{'"oaxioms";"o1", "o2"."mk-es"[]{'"E";'"eq";'"T";"lambda"[]{"i"."lambda"[]{"a".(('"V" "locl"[]{'"a"}) '"i")}};"lambda"[]{"l"."lambda"[]{"tg".(('"V" "rcv"[]{'"l";'"tg"}) "ldst"[]{'"l"})}};"lambda"[]{"e"."loc"[]{'"info";'"e"}};"lambda"[]{"e"."kind"[]{'"info";'"e"}};'"val";'"when";'"after";"lambda"[]{"l"."lambda"[]{"e"."sends"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";'"val";'"o1";'"e";'"l"}}};"lambda"[]{"e"."sender"[]{'"info";'"e"}};"lambda"[]{"e"."index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";'"o1";'"e"}};"lambda"[]{"e"."first"[]{'"pred?";'"e"}};"lambda"[]{"e"."pred"[]{'"pred?";'"e"}};"lambda"[]{"e"."lambda"[]{"e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%7"."decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) '"e") '"e'") "it"[]{});"%9"."inl"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%10"."inl"[]{'"%10"}}}}) '"e") '"e'") '"%9")};"%10"."inr"[]{"decide"[]{'"%10";"%11"."inl"[]{"it"[]{}};"%12"."inr"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%13"."inl"[]{'"%13"}}}}) '"e'") '"e") '"%12")}}}}}}};"pair"[]{"lambda"[]{"e"."pair"[]{"lambda"[]{"%"."lambda"[]{"e'"."lambda"[]{"%6"."lambda"[]{"%12"."any"[]{"any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e"."implies"[]{"cless"[]{'"E";'"pred?";'"info";'"e";'"e"};"false"[]{}}}) "lambda"[]{"j"."lambda"[]{"%"."lambda"[]{"%2"."it"[]{}}}}) '"e") "spread"[]{((((((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};(("rel_star"[]{'"E";"lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}} '"e") '"e'")}}) "lambda"[]{"j1"."lambda"[]{"%3"."decide"[]{("termof"[]{} "first"[]{'"pred?";'"j1"});"%5"."lambda"[]{"%6"."pair"[]{"number"[0:n]{};"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(((('"p5" '"e") '"j1") "it"[]{}) "it"[]{})}}}}}};"%6"."lambda"[]{"%7".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) '"e") "pred"[]{'"pred?";'"j1"}) '"j1") ((('"%3" "pred"[]{'"pred?";'"j1"}) "pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12"."it"[]{}}}}})) ((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "pred"[]{'"pred?";'"j1"}) '"j1") "pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}))}}}}) '"e'") "it"[]{});"n", "%14"."decide"[]{"int_eq"[]{'"n";"number"[0:n]{};"inl"[]{"it"[]{}};"inr"[]{"lambda"[]{""."it"[]{}}}};"%16".'"%12";"%17".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") "pair"[]{'"n";(((((((("termof"[]{} '"n") '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%18"."inl"[]{'"%18"}}}}) '"e") '"e'") '"%14")}) '"%12")}})}}}}}};"lambda"[]{"%"."decide"[]{("termof"[]{} "first"[]{'"pred?";'"e"});"%7".'"%7";"%8"."any"[]{((('"%" "pred"[]{'"pred?";'"e"}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(('"p9" '"e") "lambda"[]{""."it"[]{}})}}}}) ((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "pred"[]{'"pred?";'"e"}) '"e") "inl"[]{"pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}}))}}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"%"."pair"[]{"pair"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(('"p9" '"e") "lambda"[]{""."it"[]{}})}}}};((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "pred"[]{'"pred?";'"e"}) '"e") "inl"[]{"pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}})};"lambda"[]{"e'"."lambda"[]{"%10"."lambda"[]{"%11"."spread"[]{'"%11";"%12", "%13"."spread"[]{"decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) "pred"[]{'"pred?";'"e"}) '"e'") "it"[]{});"%22".'"%22";"%23"."decide"[]{'"%23";"%24"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e'") '"%12")};"%25"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e'") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e'") "pred"[]{'"pred?";'"e"}) '"e'") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"e'") "pred"[]{'"pred?";'"e"}) '"%25")) '"%12"))}}};"n", "%27"."spread"[]{"decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) '"e'") '"e") "it"[]{});"%22".'"%22";"%23"."decide"[]{'"%23";"%24"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e") '"%13")};"%25"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"e") '"e'") '"%25")) '"%13"))}}};"n1", "%28"."decide"[]{("termof"[]{} "beq_int"[]{"add"[]{'"n";'"n1"};"number"[0:n]{}});"%32"."it"[]{};"%33"."spread"[]{((((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) '"n") '"n1") "pred"[]{'"pred?";'"e"}) '"e'") '"e") '"%27") '"%28");"z", "%30"."spread"[]{'"%30";"%31", "%32"."spread"[]{'"%31";"%33", "%34"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"z") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"z") '"z") "pair"[]{"sub"[]{"add"[]{'"n";'"n1"};"number"[1:n]{}};'"%32"}))}}}}}}}}}}}}}};"pair"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"saxiom"}}}};"pair"[]{(("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}});"pair"[]{((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}});"pair"[]{"lambda"[]{"e"."lambda"[]{"%"."it"[]{}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"%".((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "sender"[]{'"info";'"e"}) '"e") "inr"[]{"pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"it"[]{}}})}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."decide"[]{((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"%");"%20"."decide"[]{'"%20";"%21"."inl"[]{"pair"[]{"spread"[]{'"%21";"%22", "%23".'"%22"};"spread"[]{'"%21";"%22", "%23"."inr"[]{"it"[]{}}}}};"%22"."inr"[]{"pair"[]{"spread"[]{'"%22";"%23", "%24".("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%13"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%13"."it"[]{}}}}} '"%23")};"spread"[]{'"%22";"%23", "%24"."inr"[]{"it"[]{}}}}}};"%21"."spread"[]{'"%21";"z", "%22"."spread"[]{'"%22";"%23", "%24"."decide"[]{'"%24";"%25"."inl"[]{"pair"[]{"spread"[]{'"%25";"%26", "%27".'"%26"};"spread"[]{'"%25";"%26", "%27"."inl"[]{'"%23"}}}};"%26"."inr"[]{"pair"[]{"spread"[]{'"%26";"%27", "%28".("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%24"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%24"."it"[]{}}}}} '"%27")};"spread"[]{'"%26";"%27", "%28"."inl"[]{'"%23"}}}}}}}}}}};"pair"[]{"lambda"[]{"e"."decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"l"."lambda"[]{"%"."it"[]{}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."lambda"[]{"%16"."lambda"[]{"%17"."spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12"."pair"[]{"lambda"[]{"%22"."decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) "sender"[]{'"info";'"e"}) "sender"[]{'"info";'"e'"}) "it"[]{});"%27"."inl"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%28"."inl"[]{'"%28"}}}}) "sender"[]{'"info";'"e"}) "sender"[]{'"info";'"e'"}) '"%27")};"%28"."decide"[]{'"%28";"%29"."inr"[]{"pair"[]{"it"[]{};"decide"[]{"less"[]{"index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};'"e"};"index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};'"e'"};"inr"[]{"lambda"[]{""."lambda"[]{""."it"[]{}}}};"inl"[]{"lambda"[]{""."it"[]{}}}};"%31"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e1"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"e1";'"e1"}}}) "lambda"[]{"j"."lambda"[]{"%34"."lambda"[]{"%35"."it"[]{}}}}) '"e") "decide"[]{"decide"[]{(((((((("termof"[]{} '"E") '"eq") "receives"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) '"e'") '"e") "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e'");"%47", "%48".('"%48" "pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16");"pair"[]{"it"[]{};"it"[]{}}})}) "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e");"%47", "%48".('"%48" "pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"pair"[]{"it"[]{};"it"[]{}}})}) "lambda"[]{""."it"[]{}});"%33"."inl"[]{(((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"pred?") '"info") '"e") '"e'") "sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) "spread"[]{'"p7";"f", "%22"."pair"[]{'"f";"lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%27".((('"%22" '"x") '"y") "inl"[]{'"%27"})}}}}}) "spread"[]{("spread"[]{((((("termof"[]{} '"E") "eventlist"[]{'"pred?";"sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}}) "lambda"[]{"r"."rcv-from-on"[]{'"eq";"idlnk-deq"[]{};'"info";"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"};'"r"}}) '"e'") '"e");"%35", "%36".'"%35"} '"%33");"%37", "%38"."spread"[]{'"%38";"%39", "%40".'"%40"}})};"%34"."inr"[]{"it"[]{}}};"%34".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") '"%22") '"%34");"%35".'"%22"})};"%32"."it"[]{}}}};"%30"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e1"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"e1";'"e1"}}}) "lambda"[]{"j"."lambda"[]{"%39"."lambda"[]{"%40"."it"[]{}}}}) '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") '"%22") (((((('"p12" '"e'") '"e") ("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16")) ("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%")) "it"[]{}) ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%31"."inl"[]{'"%31"}}}}) "sender"[]{'"info";'"e'"}) "sender"[]{'"info";'"e"}) '"%30"))))}}}};"lambda"[]{"%22"."decide"[]{'"%22";"%23".(((((('"p12" '"e") '"e'") ("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%")) ("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16")) "it"[]{}) '"%23");"%24"."spread"[]{'"%24";"%25", "%26".(((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"pred?") '"info") '"e'") '"e") "sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) "spread"[]{'"p7";"f", "%22"."pair"[]{'"f";"lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%27".((('"%22" '"x") '"y") "inl"[]{'"%27"})}}}}}) "spread"[]{("spread"[]{((((("termof"[]{} '"E") "eventlist"[]{'"pred?";"sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}}) "lambda"[]{"r"."rcv-from-on"[]{'"eq";"idlnk-deq"[]{};'"info";"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"};'"r"}}) '"e") '"e'");"%29", "%30".'"%29"} (((((((("termof"[]{} '"E") '"eq") "receives"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) '"e") '"e'") "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e");"%42", "%43".('"%43" "pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"pair"[]{"it"[]{};"it"[]{}}})}) "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e'");"%42", "%43".('"%43" "pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16");"pair"[]{"it"[]{};"it"[]{}}})}) "it"[]{}));"%31", "%32"."spread"[]{'"%32";"%33", "%34".'"%34"}})}}}}}}}}}}}}};"lambda"[]{"e"."lambda"[]{"l"."lambda"[]{"n"."spread"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{"pair"[]{"fst"[]{'"oaxioms"};"pair"[]{"pair"[]{'"p5";"pair"[]{'"p7";"pair"[]{'"p9";"pair"[]{'"p11";'"p12"}}}};'"saxiom"}}}) '"p7") '"p9") '"p5") '"e") '"l") '"n")}}}};"e'", "%20"."spread"[]{'"%20";"%21", "%22"."spread"[]{'"%22";"%23", "%24"."spread"[]{'"%24";"%25", "%26"."pair"[]{'"e'";"pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%21");"pair"[]{"it"[]{};"pair"[]{"it"[]{};"it"[]{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}


interactive nuprl_EVal_to_ES_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"e" in "EVal"[level:l]{} }  -->
   sequent { <H> >- ("EVal_to_ES"[level:l]{'"e"} in "event_system"[level:l]{}) }

interactive nuprl_ES__to__EVal   :
   sequent { <H> >- "event_system"[level:l]{} }  -->
   sequent { <H> >- "EVal"[level:l]{} }

define unfold_es__E : "es-E"[]{'"es"} <-->
      "fst"[]{'"es"}


interactive nuprl_es__E_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- ("es-E"[]{'"the_es"} in "univ"[level:l]{}) }

interactive nuprl_es__E_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "type"{"es-E"[]{'"the_es"}} }

define unfold_es__eq__E : "es-eq-E"[]{'"es";'"e";'"e'"} <-->
      (("eqof"[]{"fst"[]{"snd"[]{'"es"}}} '"e") '"e'")


interactive nuprl_es__eq__E_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-eq-E"[]{'"the_es";'"e";'"e'"} in "bool"[]{}) }

interactive nuprl_assert__es__eq__E univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";'"e'"};"assert"[]{"es-eq-E"[]{'"the_es";'"e";'"e'"}}} }

interactive nuprl_decidable__es__E_equal univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";'"e'"}} }

define unfold_es__LnkTag__deq : "es-LnkTag-deq"[]{} <-->
      "product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}}


interactive nuprl_es__LnkTag__deq_wf {| intro[] |}   :
   sequent { <H> >- ("es-LnkTag-deq"[]{} in "deq"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}}}) }

define unfold_es__Msg : "es-Msg"[]{'"es"} <-->
      "Msg"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}


interactive nuprl_es__Msg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- ("es-Msg"[]{'"the_es"} in "univ"[level:l]{}) }

interactive nuprl_es__Msg_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "type"{"es-Msg"[]{'"the_es"}} }

define unfold_es__Msgl : "es-Msgl"[]{'"es";'"l"} <-->
      "set"[]{"es-Msg"[]{'"es"};"m"."haslink"[]{'"l";'"m"}}


interactive nuprl_es__Msgl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("es-Msgl"[]{'"the_es";'"l"} in "univ"[level:l]{}) }

interactive nuprl_es__Msgl_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "type"{"es-Msgl"[]{'"the_es";'"l"}} }

define unfold_es__loc : "es-loc"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}} '"e")


interactive nuprl_es__loc_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-loc"[]{'"the_es";'"e"} in "Id"[]{}) }

define unfold_es__kind : "es-kind"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}} '"e")


interactive nuprl_es__kind_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-kind"[]{'"the_es";'"e"} in "Knd"[]{}) }

define unfold_es__isrcv : "es-isrcv"[]{'"es";'"e"} <-->
      "isrcv"[]{"es-kind"[]{'"es";'"e"}}


interactive nuprl_es__isrcv_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-isrcv"[]{'"the_es";'"e"} in "bool"[]{}) }

define unfold_es__tag : "es-tag"[]{'"es";'"e"} <-->
      "tagof"[]{"es-kind"[]{'"es";'"e"}}


interactive nuprl_es__tag_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-tag"[]{'"the_es";'"e"} in "Id"[]{}) }

define unfold_es__lnk : "es-lnk"[]{'"es";'"e"} <-->
      "lnk"[]{"es-kind"[]{'"es";'"e"}}


interactive nuprl_es__lnk_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-lnk"[]{'"the_es";'"e"} in "IdLnk"[]{}) }

define unfold_es__act : "es-act"[]{'"es";'"e"} <-->
      "actof"[]{"es-kind"[]{'"es";'"e"}}


interactive nuprl_es__act_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}}} }  -->
   sequent { <H> >- ("es-act"[]{'"the_es";'"e"} in "Id"[]{}) }

define unfold_es__kindcase : "es-kindcase"[]{'"es";'"e";"a".'"f"['"a"];"l", "tg".'"g"['"l";'"tg"]} <-->
      "ifthenelse"[]{"es-isrcv"[]{'"es";'"e"};'"g"["es-lnk"[]{'"es";'"e"};"es-tag"[]{'"es";'"e"}];'"f"["es-act"[]{'"es";'"e"}]}


interactive nuprl_es__kindcase_wf {| intro[] |} univ[level:l] '"T" '"the_es" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x".'"f"['"x"]} '"e"  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"f"['"x"] in '"T" }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"g"['"x";'"x1"] in '"T" }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-kindcase"[]{'"the_es";'"e";"a".'"f"['"a"];"l", "tg".'"g"['"l";'"tg"]} in '"T") }

define unfold_es__msgtype : "es-msgtype"[]{'"es";'"m"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}} "mlnk"[]{'"m"}) "mtag"[]{'"m"})


interactive nuprl_es__msgtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-msgtype"[]{'"the_es";'"m"} in "univ"[level:l]{}) }

interactive nuprl_es__msgtype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "type"{"es-msgtype"[]{'"the_es";'"m"}} }

define unfold_es__rcvtype : "es-rcvtype"[]{'"es";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}} "es-lnk"[]{'"es";'"e"}) "es-tag"[]{'"es";'"e"})


interactive nuprl_es__rcvtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-rcvtype"[]{'"the_es";'"e"} in "univ"[level:l]{}) }

interactive nuprl_es__rcvtype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- "type"{"es-rcvtype"[]{'"the_es";'"e"}} }

define unfold_es__acttype : "es-acttype"[]{'"es";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}} "es-loc"[]{'"es";'"e"}) "es-act"[]{'"es";'"e"})


interactive nuprl_es__acttype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}}} }  -->
   sequent { <H> >- ("es-acttype"[]{'"the_es";'"e"} in "univ"[level:l]{}) }

interactive nuprl_es__acttype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}}} }  -->
   sequent { <H> >- "type"{"es-acttype"[]{'"the_es";'"e"}} }

define unfold_es__valtype : "es-valtype"[]{'"es";'"e"} <-->
      "ifthenelse"[]{"es-isrcv"[]{'"es";'"e"};"es-rcvtype"[]{'"es";'"e"};"es-acttype"[]{'"es";'"e"}}


interactive nuprl_es__valtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-valtype"[]{'"the_es";'"e"} in "univ"[level:l]{}) }

interactive nuprl_es__valtype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "type"{"es-valtype"[]{'"the_es";'"e"}} }

define unfold_es__vartype : "es-vartype"[]{'"es";'"i";'"x"} <-->
      (("fst"[]{"snd"[]{"snd"[]{'"es"}}} '"i") '"x")


interactive nuprl_es__vartype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("es-vartype"[]{'"the_es";'"i";'"x"} in "univ"[level:l]{}) }

interactive nuprl_es__vartype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"es-vartype"[]{'"the_es";'"i";'"x"}} }

define unfold_es__val : "es-val"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}} '"e")


interactive nuprl_es__val_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-val"[]{'"the_es";'"e"} in "es-valtype"[]{'"the_es";'"e"}) }

define unfold_es__when : "es-when"[]{'"es";'"x";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}} '"x") '"e")


interactive nuprl_es__when_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("es-when"[]{'"the_es";'"x";'"e"} in "es-vartype"[]{'"the_es";"es-loc"[]{'"the_es";'"e"};'"x"}) }

define unfold_es__after : "es-after"[]{'"es";'"x";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}} '"x") '"e")


interactive nuprl_es__after_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("es-after"[]{'"the_es";'"x";'"e"} in "es-vartype"[]{'"the_es";"es-loc"[]{'"the_es";'"e"};'"x"}) }

define unfold_es__sends : "es-sends"[]{'"es";'"l";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}} '"l") '"e")


interactive nuprl_es__sends_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-sends"[]{'"the_es";'"l";'"e"} in "list"[]{"es-Msgl"[]{'"the_es";'"l"}}) }

define unfold_es__sender : "es-sender"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}} '"e")


interactive nuprl_es__sender_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-sender"[]{'"the_es";'"e"} in "es-E"[]{'"the_es"}) }

define unfold_es__index : "es-index"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}} '"e")


interactive nuprl_es__index_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-index"[]{'"the_es";'"e"} in "int_seg"[]{"number"[0:n]{};"length"[]{"es-sends"[]{'"the_es";"es-lnk"[]{'"the_es";'"e"};"es-sender"[]{'"the_es";'"e"}}}}) }

define unfold_es__first : "es-first"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}} '"e")


interactive nuprl_es__first_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-first"[]{'"the_es";'"e"} in "bool"[]{}) }

define unfold_es__pred : "es-pred"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}}} '"e")


interactive nuprl_es__pred_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"the_es";'"e"}}} }  -->
   sequent { <H> >- ("es-pred"[]{'"the_es";'"e"} in "es-E"[]{'"the_es"}) }

define unfold_es__causl : "es-causl"[]{'"es";'"e";'"e'"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}}}} '"e") '"e'")


interactive nuprl_es__causl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-causl"[]{'"the_es";'"e";'"e'"} in "univ"[level:l]{}) }

define unfold_es__locl : "es-locl"[]{'"es";'"e";'"e'"} <-->
      "and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"es-loc"[]{'"es";'"e'"}};"es-causl"[]{'"es";'"e";'"e'"}}


interactive nuprl_es__locl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-locl"[]{'"the_es";'"e";'"e'"} in "univ"[level:l]{}) }

define unfold_es__le : "es-le"[]{'"es";'"e";'"e'"} <-->
      "or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}}


interactive nuprl_es__le_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-le"[]{'"the_es";'"e";'"e'"} in "univ"[level:l]{}) }

interactive nuprl_es__axioms univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "and"[]{"trans"[]{"es-E"[]{'"the_es"};"e", "e'"."es-locl"[]{'"the_es";'"e";'"e'"}};"and"[]{"strongwellfounded"[]{"es-E"[]{'"the_es"};"e", "e'"."es-locl"[]{'"the_es";'"e";'"e'"}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"es-E"[]{'"the_es"};"e'"."iff"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"the_es";'"e"};"es-loc"[]{'"the_es";'"e'"}};"or"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"or"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";'"e'"};"es-locl"[]{'"the_es";'"e'";'"e"}}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."iff"[]{"assert"[]{"es-first"[]{'"the_es";'"e"}};"all"[]{"es-E"[]{'"the_es"};"e'"."not"[]{"es-locl"[]{'"the_es";'"e'";'"e"}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."implies"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e"}}};"and"[]{"es-locl"[]{'"the_es";"es-pred"[]{'"the_es";'"e"};'"e"};"all"[]{"es-E"[]{'"the_es"};"e'"."not"[]{"and"[]{"es-locl"[]{'"the_es";"es-pred"[]{'"the_es";'"e"};'"e'"};"es-locl"[]{'"the_es";'"e'";'"e"}}}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."implies"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{"es-vartype"[]{'"the_es";"es-loc"[]{'"the_es";'"e"};'"x"};"es-when"[]{'"the_es";'"x";'"e"};"es-after"[]{'"the_es";'"x";"es-pred"[]{'"the_es";'"e"}}}}}};"and"[]{"trans"[]{"es-E"[]{'"the_es"};"e", "e'"."es-causl"[]{'"the_es";'"e";'"e'"}};"and"[]{"strongwellfounded"[]{"es-E"[]{'"the_es"};"e", "e'"."es-causl"[]{'"the_es";'"e";'"e'"}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}};"equal"[]{"es-Msg"[]{'"the_es"};"select"[]{"es-index"[]{'"the_es";'"e"};"es-sends"[]{'"the_es";"es-lnk"[]{'"the_es";'"e"};"es-sender"[]{'"the_es";'"e"}}};"msg"[]{"es-lnk"[]{'"the_es";'"e"};"es-tag"[]{'"the_es";'"e"};"es-val"[]{'"the_es";'"e"}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"es-E"[]{'"the_es"};"e'"."implies"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"es-causl"[]{'"the_es";'"e";'"e'"}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}};"es-causl"[]{'"the_es";"es-sender"[]{'"the_es";'"e"};'"e"}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"es-E"[]{'"the_es"};"e'"."implies"[]{"es-causl"[]{'"the_es";'"e";'"e'"};"or"[]{"cand"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e'"}}};"or"[]{"es-causl"[]{'"the_es";'"e";"es-pred"[]{'"the_es";'"e'"}};"equal"[]{"es-E"[]{'"the_es"};'"e";"es-pred"[]{'"the_es";'"e'"}}}};"cand"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e'"}};"or"[]{"es-causl"[]{'"the_es";'"e";"es-sender"[]{'"the_es";'"e'"}};"equal"[]{"es-E"[]{'"the_es"};'"e";"es-sender"[]{'"the_es";'"e'"}}}}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}};"equal"[]{"Id"[]{};"es-loc"[]{'"the_es";'"e"};"ldst"[]{"es-lnk"[]{'"the_es";'"e"}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"IdLnk"[]{};"l"."implies"[]{"not"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"the_es";'"e"};"lsrc"[]{'"l"}}};"equal"[]{"list"[]{"es-Msgl"[]{'"the_es";'"l"}};"es-sends"[]{'"the_es";'"l";'"e"};"nil"[]{}}}}};"and"[]{"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"es-E"[]{'"the_es"};"e'"."implies"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}};"implies"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e'"}};"implies"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"the_es";'"e"};"es-lnk"[]{'"the_es";'"e'"}};"iff"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"or"[]{"es-locl"[]{'"the_es";"es-sender"[]{'"the_es";'"e"};"es-sender"[]{'"the_es";'"e'"}};"and"[]{"equal"[]{"es-E"[]{'"the_es"};"es-sender"[]{'"the_es";'"e"};"es-sender"[]{'"the_es";'"e'"}};"lt"[]{"es-index"[]{'"the_es";'"e"};"es-index"[]{'"the_es";'"e'"}}}}}}}}}};"all"[]{"es-E"[]{'"the_es"};"e"."all"[]{"IdLnk"[]{};"l"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"es-sends"[]{'"the_es";'"l";'"e"}}};"n"."exists"[]{"es-E"[]{'"the_es"};"e'"."cand"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e'"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"the_es";'"e'"};'"l"};"and"[]{"equal"[]{"es-E"[]{'"the_es"};"es-sender"[]{'"the_es";'"e'"};'"e"};"equal"[]{"int"[]{};"es-index"[]{'"the_es";'"e'"};'"n"}}}}}}}}}}}}}}}}}}}}}}} }

interactive nuprl_es__locl__wellfnd   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "well_founded"[level:l]{"es-E"[]{'"the_es"};"x", "y"."es-locl"[]{'"the_es";'"x";'"y"}} }

interactive nuprl_es__locl__trans univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "trans"[]{"es-E"[]{'"the_es"};"x", "y"."es-locl"[]{'"the_es";'"x";'"y"}} }

interactive nuprl_es__le__trans univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "trans"[]{"es-E"[]{'"the_es"};"x", "y"."es-le"[]{'"the_es";'"x";'"y"}} }

interactive nuprl_es__le__total univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"es-loc"[]{'"es";'"e'"}} }  -->
   sequent { <H> >- "or"[]{"es-le"[]{'"es";'"e";'"e'"};"es-le"[]{'"es";'"e'";'"e"}} }

interactive nuprl_es__locl__swellfnd univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "strongwellfounded"[]{"es-E"[]{'"the_es"};"x", "y"."es-locl"[]{'"the_es";'"x";'"y"}} }

interactive nuprl_es__causl__wellfnd   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   sequent { <H> >- "well_founded"[level:l]{"es-E"[]{'"the_es"};"x", "y"."es-causl"[]{'"the_es";'"x";'"y"}} }

interactive nuprl_es__locl__antireflexive univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"es-locl"[]{'"the_es";'"e";'"e"}} }

interactive nuprl_es__le__not__locl univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"es-loc"[]{'"es";'"e'"}} }  -->
   sequent { <H> >- "iff"[]{"es-le"[]{'"es";'"e";'"e'"};"not"[]{"es-locl"[]{'"es";'"e'";'"e"}}} }

interactive nuprl_es__causal__antireflexive univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"es-causl"[]{'"the_es";'"e";'"e"}} }

interactive nuprl_es__causl__locl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "es-causl"[]{'"the_es";'"e";'"e'"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"the_es";'"e"};"es-loc"[]{'"the_es";'"e'"}} }  -->
   sequent { <H> >- "es-locl"[]{'"the_es";'"e";'"e'"} }

interactive nuprl_es__pred__locl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"the_es";'"j"}}} }  -->
   sequent { <H> >- "es-locl"[]{'"the_es";"es-pred"[]{'"the_es";'"j"};'"j"} }

interactive nuprl_es__le__self univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "es-le"[]{'"es";'"e";'"e"} }

interactive nuprl_es__pred__le univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"the_es";'"j"}}} }  -->
   sequent { <H> >- "es-le"[]{'"the_es";"es-pred"[]{'"the_es";'"j"};'"j"} }

interactive nuprl_es__pred__causl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"the_es";'"j"}}} }  -->
   sequent { <H> >- "es-causl"[]{'"the_es";"es-pred"[]{'"the_es";'"j"};'"j"} }

interactive nuprl_es__sender__causl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- "es-causl"[]{'"the_es";"es-sender"[]{'"the_es";'"e"};'"e"} }

interactive nuprl_es__first__implies univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-first"[]{'"the_es";'"j"}} }  -->
   sequent { <H> >- "not"[]{"es-locl"[]{'"the_es";'"e";'"j"}} }

interactive nuprl_es__loc__pred univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"the_es";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"the_es";"es-pred"[]{'"the_es";'"e"}};"es-loc"[]{'"the_es";'"e"}} }

interactive nuprl_es__loc__rcv univ[level:l] '"tg"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"ldst"[]{'"l"}};"equal"[]{"Id"[]{};"es-loc"[]{'"es";"es-sender"[]{'"es";'"e"}};"lsrc"[]{'"l"}}}} }

interactive nuprl_es__loc__sender univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"es";'"e"}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";"es-sender"[]{'"es";'"e"}};"lsrc"[]{"es-lnk"[]{'"es";'"e"}}} }

interactive nuprl_es__le__loc univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "es-le"[]{'"es";'"e";'"e'"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"es-loc"[]{'"es";'"e'"}} }

interactive nuprl_es__locl__iff univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"and"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e'"}}};"or"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";"es-pred"[]{'"the_es";'"e'"}};"es-locl"[]{'"the_es";'"e";"es-pred"[]{'"the_es";'"e'"}}}}} }

interactive nuprl_es__le__iff univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"es-le"[]{'"the_es";'"e";'"e'"};"or"[]{"cand"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e'"}}};"es-le"[]{'"the_es";'"e";"es-pred"[]{'"the_es";'"e'"}}};"equal"[]{"es-E"[]{'"the_es"};'"e";'"e'"}}} }

interactive nuprl_es__causl__iff univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"es-causl"[]{'"the_es";'"e";'"e'"};"or"[]{"cand"[]{"not"[]{"assert"[]{"es-first"[]{'"the_es";'"e'"}}};"or"[]{"es-causl"[]{'"the_es";'"e";"es-pred"[]{'"the_es";'"e'"}};"equal"[]{"es-E"[]{'"the_es"};'"e";"es-pred"[]{'"the_es";'"e'"}}}};"cand"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e'"}};"or"[]{"es-causl"[]{'"the_es";'"e";"es-sender"[]{'"the_es";'"e'"}};"equal"[]{"es-E"[]{'"the_es"};'"e";"es-sender"[]{'"the_es";'"e'"}}}}}} }

interactive nuprl_implies__es__pred univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "and"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"all"[]{"es-E"[]{'"the_es"};"e1"."not"[]{"and"[]{"es-locl"[]{'"the_es";'"e";'"e1"};"es-locl"[]{'"the_es";'"e1";'"e'"}}}}} }  -->
   sequent { <H> >- "equal"[]{"es-E"[]{'"the_es"};'"e";"es-pred"[]{'"the_es";'"e'"}} }

interactive nuprl_decidable__es__locl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "decidable"[]{"es-locl"[]{'"the_es";'"e";'"e'"}} }

define unfold_es__bless : "es-bless"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


interactive nuprl_es__bless_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-bless"[level:l]{'"es";'"e";'"e'"} in "bool"[]{}) }

interactive nuprl_assert__es__bless   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"es-bless"[level:l]{'"es";'"e";'"e'"}};"es-locl"[]{'"es";'"e";'"e'"}} }

interactive nuprl_decidable__es__le univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "decidable"[]{"es-le"[]{'"the_es";'"e";'"e'"}} }

define unfold_es__ble : "es-ble"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


interactive nuprl_es__ble_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-ble"[level:l]{'"es";'"e";'"e'"} in "bool"[]{}) }

interactive nuprl_assert__es__ble   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"es-ble"[level:l]{'"es";'"e";'"e'"}};"es-le"[]{'"es";'"e";'"e'"}} }

interactive nuprl_decidable__es__causl univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "decidable"[]{"es-causl"[]{'"the_es";'"e";'"e'"}} }

define unfold_es__bc : "es-bc"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


interactive nuprl_es__bc_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-bc"[level:l]{'"es";'"e";'"e'"} in "bool"[]{}) }

interactive nuprl_assert__es__bc   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"es-bc"[level:l]{'"es";'"e";'"e'"}};"es-causl"[]{'"es";'"e";'"e'"}} }

define unfold_es__ek : "es-ek"[]{'"es";'"k";"e", "v".'"P"['"e";'"v"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};'"P"['"e";"es-val"[]{'"es";'"e"}]}}


define unfold_es__er : "es-er"[]{'"es";'"l";'"tg";"e", "v".'"P"['"e";'"v"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"and"[]{"equal"[]{"Id"[]{};"es-tag"[]{'"es";'"e"};'"tg"};'"P"['"e";"es-val"[]{'"es";'"e"}]}}}}


define unfold_es__mtag : "es-mtag"[]{'"es";'"m"} <-->
      "mtag"[]{'"m"}


interactive nuprl_es__mtag_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-mtag"[]{'"the_es";'"m"} in "Id"[]{}) }

define unfold_es__mval : "es-mval"[]{'"es";'"m"} <-->
      "mval"[]{'"m"}


interactive nuprl_es__mval_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-mval"[]{'"the_es";'"m"} in "es-msgtype"[]{'"the_es";'"m"}) }

interactive nuprl_es__mval__valtype  '"e" '"l" '"i"  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"e1" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "lt"[]{'"i";"length"[]{"es-sends"[]{'"the_es";'"l";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"es-Msg"[]{'"the_es"};'"m";"select"[]{'"i";"es-sends"[]{'"the_es";'"l";'"e"}}} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e1"}} }  -->
   sequent { <H> >- "equal"[]{"IdLnk"[]{};"es-lnk"[]{'"the_es";'"e1"};'"l"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-tag"[]{'"the_es";'"e1"};"es-mtag"[]{'"the_es";'"m"}} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};"es-msgtype"[]{'"the_es";'"m"};"es-valtype"[]{'"the_es";'"e1"}} }

interactive nuprl_es__msg__rcvd   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "mem"[]{'"m";"es-sends"[]{'"the_es";'"l";'"e"};"es-Msg"[]{'"the_es"}} }  -->
   sequent { <H> >- "es-er"[]{'"the_es";'"l";"es-mtag"[]{'"the_es";'"m"};"e'", "v"."and"[]{"es-causl"[]{'"the_es";'"e";'"e'"};"cand"[]{"equal"[]{"univ"[level:l]{};"es-msgtype"[]{'"the_es";'"m"};"es-valtype"[]{'"the_es";'"e'"}};"equal"[]{"es-valtype"[]{'"the_es";'"e'"};'"v";"es-mval"[]{'"the_es";'"m"}}}}} }

define unfold_es__before : "es-before"[]{'"es";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"es-before"."lambda"[]{"e"."ifthenelse"[]{"es-first"[]{'"es";'"e"};"nil"[]{};"append"[]{('"es-before" "es-pred"[]{'"es";'"e"});"cons"[]{"es-pred"[]{'"es";'"e"};"nil"[]{}}}}}}) '"e")


interactive nuprl_es__before_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-before"[]{'"the_es";'"e"} in "list"[]{"es-E"[]{'"the_es"}}) }

interactive nuprl_member__es__before univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"e";"es-before"[]{'"the_es";'"e'"};"es-E"[]{'"the_es"}};"es-locl"[]{'"the_es";'"e";'"e'"}} }

interactive nuprl_l_before__es__before univ[level:l] '"e"  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"y" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "l_before"[]{'"e'";'"y";"es-before"[]{'"the_es";'"e"};"es-E"[]{'"the_es"}} }  -->
   sequent { <H> >- "es-locl"[]{'"the_es";'"e'";'"y"} }

define unfold_es__interval : "es-interval"[level:l]{'"es";'"e";'"e'"} <-->
      "filter"[]{"lambda"[]{"ev"."es-ble"[level:l]{'"es";'"e";'"ev"}};"append"[]{"es-before"[]{'"es";'"e'"};"cons"[]{'"e'";"nil"[]{}}}}


interactive nuprl_es__interval_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-interval"[level:l]{'"es";'"e";'"e'"} in "list"[]{"es-E"[]{'"es"}}) }

interactive nuprl_member__es__interval   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"ev" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"ev";"es-interval"[level:l]{'"es";'"e";'"e'"};"es-E"[]{'"es"}};"and"[]{"es-le"[]{'"es";'"e";'"ev"};"es-le"[]{'"es";'"ev";'"e'"}}} }

interactive nuprl_es__interval_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-interval"[level:l]{'"es";'"e";'"e'"} in "list"[]{"set"[]{"es-E"[]{'"es"};"ev"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"ev"};"es-loc"[]{'"es";'"e'"}}}}) }

define unfold_es__haslnk : "es-haslnk"[]{'"es";'"l";'"e"} <-->
      "band"[]{"es-isrcv"[]{'"es";'"e"};"eq_lnk"[]{"es-lnk"[]{'"es";'"e"};'"l"}}


interactive nuprl_es__haslnk_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-haslnk"[]{'"the_es";'"l";'"e"} in "bool"[]{}) }

interactive nuprl_assert__es__haslnk univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"es-haslnk"[]{'"the_es";'"l";'"e"}};"cand"[]{"assert"[]{"es-isrcv"[]{'"the_es";'"e"}};"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"the_es";'"e"};'"l"}}} }

define unfold_es__rcvs : "es-rcvs"[]{'"es";'"l";'"e'"} <-->
      "filter"[]{"lambda"[]{"e"."es-haslnk"[]{'"es";'"l";'"e"}};"es-before"[]{'"es";'"e'"}}


interactive nuprl_member__es__rcvs univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"e";"es-rcvs"[]{'"the_es";'"l";'"e'"};"es-E"[]{'"the_es"}};"and"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"assert"[]{"es-haslnk"[]{'"the_es";'"l";'"e"}}}} }

define unfold_es__snds : "es-snds"[]{'"es";'"l";'"e"} <-->
      "concat"[]{"map"[]{"lambda"[]{"e"."es-sends"[]{'"es";'"l";'"e"}};"es-before"[]{'"es";'"e"}}}


interactive nuprl_es__snds_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-snds"[]{'"the_es";'"l";'"e"} in "list"[]{"es-Msgl"[]{'"the_es";'"l"}}) }

interactive nuprl_member__es__snds univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"m";"es-snds"[]{'"the_es";'"l";'"e'"};"es-Msg"[]{'"the_es"}};"exists"[]{"es-E"[]{'"the_es"};"e"."and"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"mem"[]{'"m";"es-sends"[]{'"the_es";'"l";'"e"};"es-Msg"[]{'"the_es"}}}}} }

define unfold_es__snds__index : "es-snds-index"[]{'"es";'"l";'"e";'"n"} <-->
      "append"[]{"es-snds"[]{'"es";'"l";'"e"};"firstn"[]{'"n";"es-sends"[]{'"es";'"l";'"e"}}}


interactive nuprl_es__snds__index_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("es-snds-index"[]{'"the_es";'"l";'"e";'"n"} in "list"[]{"es-Msgl"[]{'"the_es";'"l"}}) }

interactive nuprl_member__es__snds__index univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{"es-sends"[]{'"the_es";'"l";'"e'"}};"number"[1:n]{}}} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"m";"es-snds-index"[]{'"the_es";'"l";'"e'";'"n"};"es-Msg"[]{'"the_es"}};"or"[]{"exists"[]{"es-E"[]{'"the_es"};"e"."and"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"mem"[]{'"m";"es-sends"[]{'"the_es";'"l";'"e"};"es-Msg"[]{'"the_es"}}}};"exists"[]{"int_seg"[]{"number"[0:n]{};'"n"};"i"."equal"[]{"es-Msg"[]{'"the_es"};'"m";"select"[]{'"i";"es-sends"[]{'"the_es";'"l";'"e'"}}}}}} }

interactive nuprl_firstn__before univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"n";"length"[]{"es-before"[]{'"the_es";'"e'"}}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"es-E"[]{'"the_es"}};"firstn"[]{'"n";"es-before"[]{'"the_es";'"e'"}};"es-before"[]{'"the_es";"select"[]{'"n";"es-before"[]{'"the_es";'"e'"}}}} }

interactive nuprl_es__before__decomp univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "mem"[]{'"e";"es-before"[]{'"the_es";'"e'"};"es-E"[]{'"the_es"}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{"es-E"[]{'"the_es"}};"l"."equal"[]{"list"[]{"es-E"[]{'"the_es"}};"es-before"[]{'"the_es";'"e'"};"append"[]{"es-before"[]{'"the_es";'"e"};"append"[]{"cons"[]{'"e";"nil"[]{}};'"l"}}}} }

interactive nuprl_last__es__snds__index univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{"es-sends"[]{'"the_es";'"l";'"e'"}};"number"[1:n]{}}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{"es-Msgl"[]{'"the_es";'"l"}};"es-snds-index"[]{'"the_es";'"l";'"e'";'"n"};"nil"[]{}}} }  -->
   sequent { <H> >- "exists"[]{"es-E"[]{'"the_es"};"e"."exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"es-sends"[]{'"the_es";'"l";'"e"}}};"m"."and"[]{"and"[]{"or"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"and"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";'"e'"};"lt"[]{'"m";'"n"}}};"equal"[]{"list"[]{"es-Msgl"[]{'"the_es";'"l"}};"es-snds-index"[]{'"the_es";'"l";'"e'";'"n"};"append"[]{"es-snds-index"[]{'"the_es";'"l";'"e";'"m"};"cons"[]{"select"[]{'"m";"es-sends"[]{'"the_es";'"l";'"e"}};"nil"[]{}}}}};"all"[]{"es-E"[]{'"the_es"};"e''"."all"[]{"nat"[]{};"k"."implies"[]{"and"[]{"or"[]{"es-locl"[]{'"the_es";'"e";'"e''"};"and"[]{"equal"[]{"es-E"[]{'"the_es"};'"e";'"e''"};"lt"[]{'"m";'"k"}}};"or"[]{"es-locl"[]{'"the_es";'"e''";'"e'"};"and"[]{"equal"[]{"es-E"[]{'"the_es"};'"e''";'"e'"};"lt"[]{'"k";'"n"}}}};"le"[]{"length"[]{"es-sends"[]{'"the_es";'"l";'"e''"}};'"k"}}}}}}} }

define unfold_es__msg : "es-msg"[]{'"es";'"e"} <-->
      "msg"[]{"es-lnk"[]{'"es";'"e"};"es-tag"[]{'"es";'"e"};"es-val"[]{'"es";'"e"}}


interactive nuprl_es__msg_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- ("es-msg"[]{'"the_es";'"e"} in "es-Msg"[]{'"the_es"}) }

interactive nuprl_es__msg_wf2 {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "set"[]{"es-E"[]{'"the_es"};"e"."assert"[]{"es-haslnk"[]{'"the_es";'"l";'"e"}}} }  -->
   sequent { <H> >- ("es-msg"[]{'"the_es";'"e"} in "es-Msgl"[]{'"the_es";'"l"}) }

interactive nuprl_es__msg__member__sends univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"es";'"e"}} }  -->
   sequent { <H> >- "mem"[]{"es-msg"[]{'"es";'"e"};"es-sends"[]{'"es";"es-lnk"[]{'"es";'"e"};"es-sender"[]{'"es";'"e"}};"es-Msg"[]{'"es"}} }

define unfold_es__msgs : "es-msgs"[]{'"the_es";'"l";'"e'"} <-->
      "map"[]{"lambda"[]{"e"."es-msg"[]{'"the_es";'"e"}};"es-rcvs"[]{'"the_es";'"l";'"e'"}}


interactive nuprl_es__msgs_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- ("es-msgs"[]{'"the_es";'"l";'"e'"} in "list"[]{"es-Msgl"[]{'"the_es";'"l"}}) }

interactive nuprl_mlnk_wf2 {| intro[] |} univ[level:l] '"the_es"  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- ("mlnk"[]{'"m"} in "IdLnk"[]{}) }

interactive nuprl_haslink_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"j"}} }  -->
   sequent { <H> >- ("haslink"[]{"es-lnk"[]{'"the_es";'"j"};'"m"} in "univ"[level:l]{}) }

interactive nuprl_haslink_wf2_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msg"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"j"}} }  -->
   sequent { <H> >- "type"{"haslink"[]{"es-lnk"[]{'"the_es";'"j"};'"m"}} }

interactive nuprl_member__es__msgs univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"m" in "es-Msgl"[]{'"the_es";'"l"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"m";"es-msgs"[]{'"the_es";'"l";'"e'"};"es-Msgl"[]{'"the_es";'"l"}};"exists"[]{"es-E"[]{'"the_es"};"e"."cand"[]{"and"[]{"es-locl"[]{'"the_es";'"e";'"e'"};"assert"[]{"es-haslnk"[]{'"the_es";'"l";'"e"}}};"equal"[]{"es-Msgl"[]{'"the_es";'"l"};'"m";"es-msg"[]{'"the_es";'"e"}}}}} }

interactive nuprl_es__fifo__nil univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"j" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"j"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"es-Msgl"[]{'"the_es";"es-lnk"[]{'"the_es";'"j"}}};"es-snds-index"[]{'"the_es";"es-lnk"[]{'"the_es";'"j"};"es-sender"[]{'"the_es";'"j"};"es-index"[]{'"the_es";'"j"}};"nil"[]{}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"es-Msg"[]{'"the_es"}};"es-msgs"[]{'"the_es";"es-lnk"[]{'"the_es";'"j"};'"j"};"nil"[]{}} }

interactive nuprl_es__fifo univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"the_es";'"e"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"es-Msg"[]{'"the_es"}};"es-snds-index"[]{'"the_es";"es-lnk"[]{'"the_es";'"e"};"es-sender"[]{'"the_es";'"e"};"es-index"[]{'"the_es";'"e"}};"es-msgs"[]{'"the_es";"es-lnk"[]{'"the_es";'"e"};'"e"}} }

define unfold_es__tg__sends : "es-tg-sends"[]{'"es";'"l";'"tg";'"e"} <-->
      "filter"[]{"lambda"[]{"m"."eq_id"[]{"es-mtag"[]{'"es";'"m"};'"tg"}};"es-sends"[]{'"es";'"l";'"e"}}


interactive nuprl_es__tg__sends_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"the_es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("es-tg-sends"[]{'"the_es";'"l";'"tg";'"e"} in "list"[]{"es-Msgl"[]{'"the_es";'"l"}}) }

interactive nuprl_es__after__pred univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"es";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"es-vartype"[]{'"es";"es-loc"[]{'"es";'"e"};'"x"};"es-after"[]{'"es";'"x";"es-pred"[]{'"es";'"e"}};"es-when"[]{'"es";'"x";'"e"}} }

define unfold_alle__at : "alle-at"[]{'"es";'"i";"e".'"P"['"e"]} <-->
      "all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};'"P"['"e"]}}


interactive nuprl_alle__at_wf {| intro[] |}  '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("alle-at"[]{'"es";'"i";"e".'"P"['"e"]} in "univ"[level:l]{}) }

define unfold_alle__at1 : "alle-at1"[]{'"es";'"i";'"x";"x".'"P"['"x"]} <-->
      "alle-at"[]{'"es";'"i";"e".'"P"["es-when"[]{'"es";'"x";'"e"}]}


interactive nuprl_alle__at1_wf {| intro[] |}  '"x" '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-vartype"[]{'"es";'"i";'"x"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("alle-at1"[]{'"es";'"i";'"x";"v".'"P"['"v"]} in "univ"[level:l]{}) }

define unfold_alle__at2 : "alle-at2"[]{'"es";'"i";'"x1";'"x2";"x1", "x2".'"P"['"x1";'"x2"]} <-->
      "alle-at"[]{'"es";'"i";"e".'"P"["es-when"[]{'"es";'"x1";'"e"};"es-when"[]{'"es";'"x2";'"e"}]}


interactive nuprl_alle__at2_wf {| intro[] |}  '"y" '"x" '"i" '"es" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-vartype"[]{'"es";'"i";'"x"};"x1": "es-vartype"[]{'"es";'"i";'"y"} >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("alle-at2"[]{'"es";'"i";'"x";'"y";"v1", "v2".'"P"['"v1";'"v2"]} in "univ"[level:l]{}) }

interactive nuprl_alle__at__iff univ[level:l] '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "iff"[]{"alle-at"[]{'"es";'"i";"e".'"P"['"e"]};"and"[]{"alle-at"[]{'"es";'"i";"e"."implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};'"P"['"e"]}};"alle-at"[]{'"es";'"i";"e"."implies"[]{"not"[]{"assert"[]{"es-first"[]{'"es";'"e"}}};"implies"[]{'"P"["es-pred"[]{'"es";'"e"}];'"P"['"e"]}}}}} }

interactive nuprl_es__invariant1 univ[level:l] '"T" "lambda"[]{"x".'"I"['"x"]} '"x" '"i" '"es"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"I"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};'"I"["es-when"[]{'"es";'"x";'"e"}]}}} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{'"I"["es-when"[]{'"es";'"x";'"e"}];'"I"["es-after"[]{'"es";'"x";'"e"}]}} }  -->
   sequent { <H> >- "alle-at1"[]{'"es";'"i";'"x";"x".'"I"['"x"]} }

interactive nuprl_es__invariant2 univ[level:l] '"y" '"x" '"i" '"es" "lambda"[]{"x1", "x".'"I"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-vartype"[]{'"es";'"i";'"x"};"x1": "es-vartype"[]{'"es";'"i";'"y"} >- '"I"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "and"[]{"alle-at"[]{'"es";'"i";"e"."implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};'"I"["es-when"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"y";'"e"}]}};"alle-at"[]{'"es";'"i";"e"."implies"[]{'"I"["es-when"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"y";'"e"}];'"I"["es-after"[]{'"es";'"x";'"e"};"es-after"[]{'"es";'"y";'"e"}]}}} }  -->
   sequent { <H> >- "alle-at2"[]{'"es";'"i";'"x";'"y";"x", "y".'"I"['"x";'"y"]} }

define unfold_existse__at : "existse-at"[]{'"es";'"i";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};'"P"['"e"]}}


interactive nuprl_existse__at_wf {| intro[] |}  '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("existse-at"[]{'"es";'"i";"e".'"P"['"e"]} in "univ"[level:l]{}) }

interactive nuprl_change__lemma univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{"equal"[]{'"T";'"x";'"y"}} }  -->
   sequent { <H> >- "subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "es-le"[]{'"es";'"e";'"e'"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e'"};'"i"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e'"};"es-when"[]{'"es";'"x";'"e"}}} }  -->
   sequent { <H> >- "exists"[]{"es-E"[]{'"es"};"ev"."and"[]{"and"[]{"es-le"[]{'"es";'"e";'"ev"};"es-le"[]{'"es";'"ev";'"e'"}};"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"ev"};"es-when"[]{'"es";'"x";'"ev"}}}}} }

interactive nuprl_es__first__exists univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"assert"[]{"es-first"[]{'"es";'"e"}};"es-le"[]{'"es";'"e";'"e'"}}} }

interactive nuprl_change__since__init univ[level:l] '"i" '"c"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{"equal"[]{'"T";'"x";'"y"}} }  -->
   sequent { <H> >- "subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"} }  -->
   sequent { <H>; "e": "es-E"[]{'"es"} ; "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"} ; "assert"[]{"es-first"[]{'"es";'"e"}}  >- "equal"[]{'"T";"es-when"[]{'"es";'"x";'"e"};'"c"} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e'"};'"i"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e'"};'"c"}} }  -->
   sequent { <H> >- "exists"[]{"es-E"[]{'"es"};"ev"."and"[]{"es-le"[]{'"es";'"ev";'"e'"};"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"ev"};"es-when"[]{'"es";'"x";'"ev"}}}}} }

interactive nuprl_es__rcv__kind univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"es";'"e"}} }  -->
   sequent { <H> >- "equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-tag"[]{'"es";'"e"};'"tg"} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}} }

interactive nuprl_es__kind__rcv univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}} }  -->
   sequent { <H> >- "guard"[]{"cand"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"and"[]{"equal"[]{"Id"[]{};"es-tag"[]{'"es";'"e"};'"tg"};"equal"[]{"Id"[]{};"es-loc"[]{'"es";"es-sender"[]{'"es";'"e"}};"lsrc"[]{'"l"}}}}}} }

define unfold_existse__le : "existse-le"[]{'"es";'"e'";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"es-le"[]{'"es";'"e";'"e'"};'"P"['"e"]}}


interactive nuprl_existse__le_wf {| intro[] |}  '"es" "lambda"[]{"x".'"P"['"x"]} '"e'"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H>;"x": "es-E"[]{'"es"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("existse-le"[]{'"es";'"e'";"e".'"P"['"e"]} in "univ"[level:l]{}) }

define unfold_alle__ge : "alle-ge"[]{'"es";'"e";"e'".'"P"['"e'"]} <-->
      "all"[]{"es-E"[]{'"es"};"e'"."implies"[]{"es-le"[]{'"es";'"e";'"e'"};'"P"['"e'"]}}


interactive nuprl_alle__ge_wf {| intro[] |}  '"es" "lambda"[]{"x".'"P"['"x"]} '"e'"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H>;"x": "es-E"[]{'"es"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("alle-ge"[]{'"es";'"e'";"e".'"P"['"e"]} in "univ"[level:l]{}) }

define unfold_alle__rcv : "alle-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} <-->
      "all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};'"P"['"e"]}}


interactive nuprl_alle__rcv_wf {| intro[] |}  '"es" "lambda"[]{"x".'"P"['"x"]} '"tg" '"l"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."assert"[]{"es-isrcv"[]{'"es";'"e"}}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("alle-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} in "univ"[level:l]{}) }

define unfold_existse__rcv : "existse-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};'"P"['"e"]}}


interactive nuprl_existse__rcv_wf {| intro[] |}  '"es" "lambda"[]{"x".'"P"['"x"]} '"tg" '"l"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."assert"[]{"es-isrcv"[]{'"es";'"e"}}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("existse-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} in "univ"[level:l]{}) }

interactive nuprl_decidable__existse__le univ[level:l] '"es" "lambda"[]{"x".'"P"['"x"]} '"e'"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e'" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H>;"x": "es-E"[]{'"es"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H>; "e": "es-E"[]{'"es"}  >- "decidable"[]{'"P"['"e"]} }  -->
   sequent { <H> >- "decidable"[]{"existse-le"[]{'"es";'"e'";"e".'"P"['"e"]}} }

interactive nuprl_es__bound__list univ[level:l] '"T" '"es" "lambda"[]{"x".'"P"['"x"]} '"i" "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]} '"L"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "es-E"[]{'"es"};"x1": '"T" >- '"Q"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H>; "x": '"T"  >- "decidable"[]{'"P"['"x"]} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x"."all"[]{"es-E"[]{'"es"};"e"."implies"[]{'"Q"['"e";'"x"];"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}}} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x"."implies"[]{'"P"['"x"];"exists"[]{"es-E"[]{'"es"};"e".'"Q"['"e";'"x"]}}} }  -->
   sequent { <H>; "not"[]{"l_exists"[]{'"L";'"T";"x".'"P"['"x"]}}  >- "existse-at"[]{'"es";'"i";"e'"."true"[]{}} }  -->
   sequent { <H> >- "existse-at"[]{'"es";'"i";"e'"."l_all"[]{'"L";'"T";"x"."implies"[]{'"P"['"x"];"exists"[]{"es-E"[]{'"es"};"e"."and"[]{"es-le"[]{'"es";'"e";'"e'"};'"Q"['"e";'"x"]}}}}} }

interactive nuprl_es__bound__list2 univ[level:l] '"T" '"L" '"es" "lambda"[]{"x".'"P"['"x"]} '"i" "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "es-E"[]{'"es"};"x1": "set"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}} >- '"Q"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H>; "x": '"T"  >- "decidable"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x"."all"[]{"es-E"[]{'"es"};"e"."implies"[]{'"Q"['"e";'"x"];"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}}} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x"."implies"[]{'"P"['"x"];"exists"[]{"es-E"[]{'"es"};"e".'"Q"['"e";'"x"]}}} }  -->
   sequent { <H>; "not"[]{"l_exists"[]{'"L";'"T";"x".'"P"['"x"]}}  >- "existse-at"[]{'"es";'"i";"e'"."true"[]{}} }  -->
   sequent { <H> >- "existse-at"[]{'"es";'"i";"e'"."l_all"[]{'"L";'"T";"x"."implies"[]{'"P"['"x"];"exists"[]{"es-E"[]{'"es"};"e"."and"[]{"es-le"[]{'"es";'"e";'"e'"};'"Q"['"e";'"x"]}}}}} }

define unfold_es__state : "es-state"[]{'"es";'"i"} <-->
      "fun"[]{"Id"[]{};"x"."es-vartype"[]{'"es";'"i";'"x"}}


interactive nuprl_es__state_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("es-state"[]{'"es";'"i"} in "univ"[level:l]{}) }

interactive nuprl_es__state_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"es-state"[]{'"es";'"i"}} }

define unfold_es__state__ap : "es-state-ap"[]{'"s";'"x"} <-->
      ('"s" '"x")


interactive nuprl_es__state__ap_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "es-state"[]{'"es";'"i"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("es-state-ap"[]{'"s";'"x"} in "es-vartype"[]{'"es";'"i";'"x"}) }

define unfold_es__state__when : "es-state-when"[]{'"es";'"e"} <-->
      "lambda"[]{"x"."es-when"[]{'"es";'"x";'"e"}}


interactive nuprl_es__state__when_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-state-when"[]{'"es";'"e"} in "es-state"[]{'"es";"es-loc"[]{'"es";'"e"}}) }

define unfold_es__state__after : "es-state-after"[]{'"es";'"e"} <-->
      "lambda"[]{"x"."es-after"[]{'"es";'"x";'"e"}}


interactive nuprl_es__state__after_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- ("es-state-after"[]{'"es";'"e"} in "es-state"[]{'"es";"es-loc"[]{'"es";'"e"}}) }

interactive nuprl_state__after__pred univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"es-first"[]{'"es";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"es-state"[]{'"es";"es-loc"[]{'"es";'"e"}};"es-state-after"[]{'"es";"es-pred"[]{'"es";'"e"}};"es-state-when"[]{'"es";'"e"}} }

define unfold_es__stable : "es-stable"[]{'"es";'"i";"state".'"P"['"state"]} <-->
      "alle-at"[]{'"es";'"i";"e"."implies"[]{'"P"["es-state-when"[]{'"es";'"e"}];'"P"["es-state-after"[]{'"es";'"e"}]}}


interactive nuprl_es__stable_wf {| intro[] |}  '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-state"[]{'"es";'"i"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("es-stable"[]{'"es";'"i";"state".'"P"['"state"]} in "univ"[level:l]{}) }

interactive nuprl_stable__implies univ[level:l] '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-state"[]{'"es";'"i"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "es-stable"[]{'"es";'"i";"state".'"P"['"state"]} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{'"P"["es-state-when"[]{'"es";'"e"}];"alle-ge"[]{'"es";'"e";"e'".'"P"["es-state-after"[]{'"es";'"e'"}]}}} }

interactive nuprl_stable__implies2 univ[level:l] '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "es-state"[]{'"es";'"i"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "es-stable"[]{'"es";'"i";"state".'"P"['"state"]} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{'"P"["es-state-after"[]{'"es";'"e"}];"alle-ge"[]{'"es";'"e";"e'".'"P"["es-state-after"[]{'"es";'"e'"}]}}} }

define unfold_es__frame : "es-frame"[]{'"es";'"i";'"L";'"x";'"T"} <-->
      "cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."implies"[]{"not"[]{"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}


interactive nuprl_es__frame_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("es-frame"[]{'"es";'"i";'"L";'"x";'"T"} in "univ"[level:l]{}) }

interactive nuprl_es__stable__1 univ[level:l] '"T" '"x" '"Lx" '"i" '"es" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Lx" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Lx";'"x";'"T"} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{"mem"[]{"es-kind"[]{'"es";'"e"};'"Lx";"Knd"[]{}};"implies"[]{'"P"["es-when"[]{'"es";'"x";'"e"}];'"P"["es-after"[]{'"es";'"x";'"e"}]}}} }  -->
   sequent { <H> >- "es-stable"[]{'"es";'"i";"state".'"P"["es-state-ap"[]{'"state";'"x"}]} }

interactive nuprl_es__stable__2 univ[level:l] '"Ty" '"Tx" '"x" '"Lx" '"i" '"es" '"y" '"Ly" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"Tx" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Ty" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"Tx";"x1": '"Ty" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Lx" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"Ly" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Lx";'"x";'"Tx"} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Ly";'"y";'"Ty"} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{"mem"[]{"es-kind"[]{'"es";'"e"};"append"[]{'"Lx";'"Ly"};"Knd"[]{}};"implies"[]{'"P"["es-when"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"y";'"e"}];'"P"["es-after"[]{'"es";'"x";'"e"};"es-after"[]{'"es";'"y";'"e"}]}}} }  -->
   sequent { <H> >- "es-stable"[]{'"es";'"i";"state".'"P"["es-state-ap"[]{'"state";'"x"};"es-state-ap"[]{'"state";'"y"}]} }

interactive nuprl_es__stable__3 univ[level:l] '"Tz" '"Ty" '"Tx" '"x" '"Lx" '"i" '"es" '"y" '"Ly" '"z" '"Lz" "lambda"[]{"x2", "x1", "x".'"P"['"x2";'"x1";'"x"]}  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"z" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"Tx" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Ty" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Tz" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"Tx";"x1": '"Ty";"x2": '"Tz" >- '"P"['"x";'"x1";'"x2"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Lx" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"Ly" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"Lz" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Lx";'"x";'"Tx"} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Ly";'"y";'"Ty"} }  -->
   sequent { <H> >- "es-frame"[]{'"es";'"i";'"Lz";'"z";'"Tz"} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{"mem"[]{"es-kind"[]{'"es";'"e"};"append"[]{'"Lx";"append"[]{'"Ly";'"Lz"}};"Knd"[]{}};"implies"[]{'"P"["es-when"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"y";'"e"};"es-when"[]{'"es";'"z";'"e"}];'"P"["es-after"[]{'"es";'"x";'"e"};"es-after"[]{'"es";'"y";'"e"};"es-after"[]{'"es";'"z";'"e"}]}}} }  -->
   sequent { <H> >- "es-stable"[]{'"es";'"i";"state".'"P"["es-state-ap"[]{'"state";'"x"};"es-state-ap"[]{'"state";'"y"};"es-state-ap"[]{'"state";'"z"}]} }

define unfold_es__responsive : "es-responsive"[]{'"es";'"l1";'"tg1";'"l2";'"tg2"} <-->
      "and"[]{"alle-rcv"[]{'"es";'"l1";'"tg1";"e"."existse-rcv"[]{'"es";'"l2";'"tg2";"e'"."and"[]{"es-le"[]{'"es";'"e";"es-sender"[]{'"es";'"e'"}};"and"[]{"alle-rcv"[]{'"es";'"l1";'"tg1";"e2"."implies"[]{"es-locl"[]{'"es";'"e";'"e2"};"es-locl"[]{'"es";"es-sender"[]{'"es";'"e'"};'"e2"}}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e''"."implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}}}}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e'"."existse-rcv"[]{'"es";'"l1";'"tg1";"e"."and"[]{"es-le"[]{'"es";'"e";"es-sender"[]{'"es";'"e'"}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e''"."implies"[]{"es-locl"[]{'"es";"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"es-locl"[]{'"es";"es-sender"[]{'"es";'"e''"};'"e"}}}}}}}


interactive nuprl_es__responsive_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"l2" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg2" in "Id"[]{} }  -->
   sequent { <H> >- ("es-responsive"[]{'"es";'"l1";'"tg1";'"l2";'"tg2"} in "univ"[level:l]{}) }

interactive nuprl_es__responsive__bijection univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"l2" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg2" in "Id"[]{} }  -->
   sequent { <H> >- "es-responsive"[]{'"es";'"l1";'"tg1";'"l2";'"tg2"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l1";'"tg1"}}};""."set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l2";'"tg2"}}}};"f"."biject"[]{"set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l1";'"tg1"}}};"set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l2";'"tg2"}}};'"f"}} }

define unfold_es__only__sender : "es-only-sender"[]{'"es";'"k";'"B";'"l";'"tg";'"T";"s", "v".'"f"['"s";'"v"]} <-->
      "and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e'"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";"es-sender"[]{'"es";'"e'"}};'"k"};"cand"[]{"subtype"[]{"es-valtype"[]{'"es";"es-sender"[]{'"es";'"e'"}};'"B"};"cand"[]{"subtype"[]{"es-valtype"[]{'"es";'"e'"};'"T"};"and"[]{"equal"[]{'"T";"es-val"[]{'"es";'"e'"};'"f"["es-state-when"[]{'"es";"es-sender"[]{'"es";'"e'"}};"es-val"[]{'"es";"es-sender"[]{'"es";'"e'"}}]};"all"[]{"es-E"[]{'"es"};"e''"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e''"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}}}}}}}}}


interactive nuprl_es__only__sender_wf {| intro[] |}  '"T" '"B" '"l" '"es" "lambda"[]{"x1", "x".'"f"['"x1";'"x"]} '"tg" '"k"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "es-state"[]{'"es";"lsrc"[]{'"l"}};"x1": '"B" >- '"f"['"x";'"x1"] in '"T" }  -->
   sequent { <H> >- ("es-only-sender"[]{'"es";'"k";'"B";'"l";'"tg";'"T";"s", "v".'"f"['"s";'"v"]} in "univ"[level:l]{}) }


(**** display forms ****)


dform nuprl_event_system_typename_df : except_mode[src] :: "event_system_typename"[]{} =
   `"event_system_typename()"


dform nuprl_strongwellfounded_df : except_mode[src] :: "strongwellfounded"[]{'"T";"x", "y".'"R"} =
   `"SWellFounded(" slot{'"R"} `")"


dform nuprl_rel_plus_df : except_mode[src] :: "rel_plus"[]{'"T";'"R"} =
   `"" slot{'"R"} `"^+"


dform nuprl_first_df : except_mode[src] :: "first"[]{'"pred?";'"e"} =
   `"first(" slot{'"pred?"} `";" slot{'"e"} `")"

dform nuprl_first_df : except_mode[src] :: "first"[]{'"pred?";'"e"} =
   `"first(" slot{'"e"} `")"


dform nuprl_pred_df : except_mode[src] :: "pred"[]{'"pred?";'"e"} =
   `"pred(" slot{'"pred?"} `";" slot{'"e"} `")"

dform nuprl_pred_df : except_mode[src] :: "pred"[]{'"pred?";'"e"} =
   `"pred(" slot{'"e"} `")"


dform nuprl_ecase1_df : except_mode[src] :: "ecase1"[]{'"e";'"info";"i".'"f";"l", "e'".'"g"} =
   `"ecase1(" slot{'"e"} `";" slot{'"info"} `";" slot{'"i"} `"." slot{'"f"} `";"
    slot{'"l"} `"," slot{'"e'"} `"." slot{'"g"} `")"


dform nuprl_loc_df : except_mode[src] :: "loc"[]{'"info";'"e"} =
   `"loc(" slot{'"info"} `";" slot{'"e"} `")"

dform nuprl_loc_df : except_mode[src] :: "loc"[]{'"info";'"e"} =
   `"loc(" slot{'"e"} `")"


dform nuprl_rcv___df : except_mode[src] :: "rcv?"[]{'"info";'"e"} =
   `"rcv?(" slot{'"info"} `";" slot{'"e"} `")"

dform nuprl_rcv___df : except_mode[src] :: "rcv?"[]{'"info";'"e"} =
   `"rcv?(" slot{'"e"} `")"


dform nuprl_sender_df : except_mode[src] :: "sender"[]{'"info";'"e"} =
   `"sender(" slot{'"info"} `";" slot{'"e"} `")"

dform nuprl_sender_df : except_mode[src] :: "sender"[]{'"info";'"e"} =
   `"sender(" slot{'"e"} `")"


dform nuprl_link_df : except_mode[src] :: "link"[]{'"info";'"e"} =
   `"link(" slot{'"info"} `";" slot{'"e"} `")"

dform nuprl_link_df : except_mode[src] :: "link"[]{'"info";'"e"} =
   `"link(" slot{'"e"} `")"


dform nuprl_pred___df : except_mode[src] :: "pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"} =
   `"pred!(" slot{'"E"} `";" slot{'"pred?"} `";" slot{'"info"} `";" slot{'"e"} `";"
    slot{'"e'"} `")"

dform nuprl_pred___df : except_mode[src] :: "pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"} =
   `"pred!(" slot{'"e"} `";" slot{'"e'"} `")"


dform nuprl_cless_df : except_mode[src] :: "cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} =
   `"cless(" slot{'"E"} `";" slot{'"pred?"} `";" slot{'"info"} `";" slot{'"e"} `";"
    slot{'"e'"} `")"

dform nuprl_cless_df : except_mode[src] :: "cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} =
   `"" slot{'"e"} `" < " slot{'"e'"} `""


dform nuprl_sends__bound_df : except_mode[src] :: "sends-bound"[]{'"p";'"e";'"l"} =
   `"sends-bound(" slot{'"p"} `";" slot{'"e"} `";" slot{'"l"} `")"


dform nuprl_eventlist_df : except_mode[src] :: "eventlist"[]{'"pred?";'"e"} =
   `"eventlist(" slot{'"pred?"} `";" slot{'"e"} `")"


dform nuprl_rcv__from__on_df : except_mode[src] :: "rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"} =
   `"rcv-from-on(" slot{'"dE"} `";" slot{'"dL"} `";" slot{'"info"} `";" slot{'"e"}
    `";" slot{'"l"} `";" slot{'"r"} `")"


dform nuprl_receives_df : except_mode[src] :: "receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"} =
   `"receives(" slot{'"dE"} `";" slot{'"dL"} `";" slot{'"pred?"} `";" slot{'"info"}
    `";" slot{'"p"} `";" slot{'"e"} `";" slot{'"l"} `")"


dform nuprl_index_df : except_mode[src] :: "index"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"r"} =
   `"index(" slot{'"dE"} `";" slot{'"dL"} `";" slot{'"pred?"} `";" slot{'"info"}
    `";" slot{'"p"} `";" slot{'"r"} `")"


dform nuprl_EOrderAxioms_df : except_mode[src] :: "EOrderAxioms"[level:l]{'"types";'"pred?";'"info"} =
   `"EOrderAxioms{i:l}(" slot{'"types"} `";" sbreak["",""] `"" slot{'"pred?"} `";"
    sbreak["",""] `"" slot{'"info"} `")"


dform nuprl_EOrder_df : except_mode[src] :: "EOrder"[level:l]{} =
   `"EventsWithOrder"


dform nuprl_EState_df : except_mode[src] :: "EState"[level:l]{} =
   `"EventsWithState"


dform nuprl_EKind_df : except_mode[src] :: "EKind"[level:l]{} =
   `"EventsWithKinds"


dform nuprl_kind_df : except_mode[src] :: "kind"[]{'"info";'"e"} =
   `"kind(" slot{'"info"} `";" slot{'"e"} `")"


dform nuprl_rtag_df : except_mode[src] :: "rtag"[]{'"info";'"e"} =
   `"rtag(" slot{'"info"} `";" slot{'"e"} `")"


dform nuprl_EVal_df : except_mode[src] :: "EVal"[level:l]{} =
   `"EventsWithValues"


dform nuprl_rmsg_df : except_mode[src] :: "rmsg"[]{'"info";'"val";'"e"} =
   `"rmsg(" slot{'"info"} `";" slot{'"val"} `";" slot{'"e"} `")"


dform nuprl_sends_df : except_mode[src] :: "sends"[]{'"dE";'"dL";'"pred?";'"info";'"val";'"p";'"e";'"l"} =
   `"sends(" slot{'"dE"} `";" slot{'"dL"} `";" slot{'"pred?"} `";" slot{'"info"}
    `";" slot{'"val"} `";" slot{'"p"} `";" slot{'"e"} `";" slot{'"l"} `")"


dform nuprl_SESAxioms_df : except_mode[src] :: "SESAxioms"[level:l]{'"E";'"T";'"pred?";'"info";'"when";'"after"} =
   `"SESAxioms{i:l}(" slot{'"E"} `";" slot{'"T"} `";;;" slot{'"pred?"} `";"
    slot{'"info"} `";" slot{'"when"} `";" slot{'"after"} `")"


dform nuprl_eventtype_df : except_mode[src] :: "eventtype"[]{'"k";'"loc";'"V";'"M";'"e"} =
   `"eventtype(" slot{'"k"} `";" slot{'"loc"} `";" slot{'"V"} `";" slot{'"M"} `";"
    slot{'"e"} `")"


dform nuprl_ESAxioms_df : except_mode[src] :: "ESAxioms"[level:l]{'"types";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"} =
   `"ESAxioms(" pushm[0:n] `"" slot{'"types"} `";" slot{'"T"} `";" slot{'"M"} `";"
    sbreak["",""] `"" slot{'"loc"} `";" slot{'"kind"} `";" slot{'"val"} `";"
    sbreak["",""] `"" slot{'"when"} `";" slot{'"after"} `";" sbreak["",""] `""
    slot{'"sends"} `";" slot{'"sender"} `";" slot{'"index"} `";" sbreak["",""] `""
    slot{'"first"} `";" slot{'"pred"} `";" sbreak["",""] `"" slot{'"causl"} popm `")"


dform nuprl_event_system_df : except_mode[src] :: "event_system"[level:l]{} =
   `"ES"


dform nuprl_mk__es_df : except_mode[src] :: "mk-es"[]{'"E";'"eq";'"T";'"V";'"M";'"loc";'"k";'"v";'"w";'"a";'"snds";'"sndr";'"i";'"f";'"prd";'"cl";'"p"} =
   `"mk-es(" slot{'"E"} `";" slot{'"eq"} `";" slot{'"T"} `";" slot{'"V"} `";"
    slot{'"M"} `";" slot{'"loc"} `";" slot{'"k"} `";" slot{'"v"} `";" slot{'"w"}
    `";" slot{'"a"} `";" slot{'"snds"} `";" slot{'"sndr"} `";" slot{'"i"} `";"
    slot{'"f"} `";" slot{'"prd"} `";" slot{'"cl"} `";" slot{'"p"} `")"


dform nuprl_mk__eval_df : except_mode[src] :: "mk-eval"[]{'"E";'"eq";'"prd";'"info";'"oax";'"T";'"w";'"a";'"sax";'"V";'"v"} =
   `"mk-eval(" slot{'"E"} `";" slot{'"eq"} `";" slot{'"prd"} `";" slot{'"info"}
    `";" slot{'"oax"} `";" slot{'"T"} `";" slot{'"w"} `";" slot{'"a"} `";"
    slot{'"sax"} `";" slot{'"V"} `";" slot{'"v"} `")"


dform nuprl_EVal_to_ES_df : except_mode[src] :: "EVal_to_ES"[level:l]{'"e"} =
   `"EVal_to_ES{i:l}(" slot{'"e"} `")"


dform nuprl_es__E_df : except_mode[src] :: "es-E"[]{'"es"} =
   `"E"


dform nuprl_es__eq__E_df : except_mode[src] :: "es-eq-E"[]{'"es";'"e";'"e'"} =
   `"" slot{'"e"} `" = " slot{'"e'"} `""


dform nuprl_es__LnkTag__deq_df : except_mode[src] :: "es-LnkTag-deq"[]{} =
   `"es-LnkTag-deq"


dform nuprl_es__Msg_df : except_mode[src] :: "es-Msg"[]{'"es"} =
   `"Msg"


dform nuprl_es__Msgl_df : except_mode[src] :: "es-Msgl"[]{'"es";'"l"} =
   `"(Msg on " slot{'"l"} `")"


dform nuprl_es__loc_df : except_mode[src] :: "es-loc"[]{'"es";'"e"} =
   `"loc(" slot{'"e"} `")"


dform nuprl_es__kind_df : except_mode[src] :: "es-kind"[]{'"es";'"e"} =
   `"kind(" slot{'"e"} `")"


dform nuprl_es__isrcv_df : except_mode[src] :: "es-isrcv"[]{'"es";'"e"} =
   `"isrcv(" slot{'"e"} `")"


dform nuprl_es__tag_df : except_mode[src] :: "es-tag"[]{'"es";'"e"} =
   `"tag(" slot{'"e"} `")"


dform nuprl_es__lnk_df : except_mode[src] :: "es-lnk"[]{'"es";'"e"} =
   `"lnk(" slot{'"e"} `")"


dform nuprl_es__act_df : except_mode[src] :: "es-act"[]{'"es";'"e"} =
   `"act(" slot{'"e"} `")"


dform nuprl_es__kindcase_df : except_mode[src] :: "es-kindcase"[]{'"es";'"e";"a".'"f";"l", "tg".'"g"} =
   `"" pushm[0:n] `"case(kind(" slot{'"e"} `"))" sbreak["",""] `"act(" slot{'"a"}
    `") => " slot{'"f"} `"" sbreak["",""] `"rcv(" slot{'"l"} `"," slot{'"tg"}
    `") => " slot{'"g"} `"" sbreak["",""] `"" popm  `""


dform nuprl_es__msgtype_df : except_mode[src] :: "es-msgtype"[]{'"es";'"m"} =
   `"msgtype(" slot{'"m"} `")"


dform nuprl_es__rcvtype_df : except_mode[src] :: "es-rcvtype"[]{'"es";'"e"} =
   `"rcvtype(" slot{'"e"} `")"


dform nuprl_es__acttype_df : except_mode[src] :: "es-acttype"[]{'"es";'"e"} =
   `"acttype(" slot{'"e"} `")"


dform nuprl_es__valtype_df : except_mode[src] :: "es-valtype"[]{'"es";'"e"} =
   `"valtype(" slot{'"e"} `")"


dform nuprl_es__vartype_df : except_mode[src] :: "es-vartype"[]{'"es";'"i";'"x"} =
   `"vartype(" slot{'"i"} `";" slot{'"x"} `")"


dform nuprl_es__val_df : except_mode[src] :: "es-val"[]{'"es";'"e"} =
   `"val(" slot{'"e"} `")"


dform nuprl_es__when_df : except_mode[src] :: "es-when"[]{'"es";'"x";'"e"} =
   `"(" slot{'"x"} `" when " slot{'"e"} `")"


dform nuprl_es__after_df : except_mode[src] :: "es-after"[]{'"es";'"x";'"e"} =
   `"(" slot{'"x"} `" after " slot{'"e"} `")"


dform nuprl_es__sends_df : except_mode[src] :: "es-sends"[]{'"es";'"l";'"e"} =
   `"sends(" slot{'"l"} `";" slot{'"e"} `")"


dform nuprl_es__sender_df : except_mode[src] :: "es-sender"[]{'"es";'"e"} =
   `"sender(" slot{'"e"} `")"


dform nuprl_es__index_df : except_mode[src] :: "es-index"[]{'"es";'"e"} =
   `"index(" slot{'"e"} `")"


dform nuprl_es__first_df : except_mode[src] :: "es-first"[]{'"es";'"e"} =
   `"first(" slot{'"e"} `")"


dform nuprl_es__pred_df : except_mode[src] :: "es-pred"[]{'"es";'"e"} =
   `"pred(" slot{'"e"} `")"


dform nuprl_es__causl_df : except_mode[src] :: "es-causl"[]{'"es";'"e";'"e'"} =
   `"(" slot{'"e"} `" < " slot{'"e'"} `")"


dform nuprl_es__locl_df : except_mode[src] :: "es-locl"[]{'"es";'"e";'"e'"} =
   `"(" slot{'"e"} `" <loc " slot{'"e'"} `")"


dform nuprl_es__le_df : except_mode[src] :: "es-le"[]{'"es";'"e";'"e'"} =
   `"es-le(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `")"

dform nuprl_es__le_df : except_mode[src] :: "es-le"[]{'"es";'"e";'"e'"} =
   `"" slot{'"e"} `" " le `" " slot{'"e'"} `" "


dform nuprl_es__bless_df : except_mode[src] :: "es-bless"[level:l]{'"es";'"e";'"e'"} =
   `"es-bless{i:l}(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `")"

dform nuprl_es__bless_df : except_mode[src] :: "es-bless"[level:l]{'"es";'"e";'"e'"} =
   `"" slot{'"e"} `" <loc " slot{'"e'"} `""


dform nuprl_es__ble_df : except_mode[src] :: "es-ble"[level:l]{'"es";'"e";'"e'"} =
   `"es-ble{i:l}(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `")"


dform nuprl_es__bc_df : except_mode[src] :: "es-bc"[level:l]{'"es";'"e";'"e'"} =
   `"es-bc{i:l}(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `")"


dform nuprl_es__ek_df : except_mode[src] :: "es-ek"[]{'"es";'"k";"e", "v".'"P"} =
   `"" "exists" `"" slot{'"e"} `"=" slot{'"k"} `"(" slot{'"v"} `")." slot{'"P"} `""


dform nuprl_es__er_df : except_mode[src] :: "es-er"[]{'"es";'"l";'"tg";"e", "v".'"P"} =
   `"" "exists" `"" slot{'"e"} `":rvc(" slot{'"l"} `"," slot{'"tg"} `"," slot{'"v"} `")."
    slot{'"P"} `""


dform nuprl_es__mtag_df : except_mode[src] :: "es-mtag"[]{'"es";'"m"} =
   `"mtag(" slot{'"m"} `")"


dform nuprl_es__mval_df : except_mode[src] :: "es-mval"[]{'"es";'"m"} =
   `"mval(" slot{'"m"} `")"


dform nuprl_es__before_df : except_mode[src] :: "es-before"[]{'"es";'"e"} =
   `"before(" slot{'"e"} `")"


dform nuprl_es__interval_df : except_mode[src] :: "es-interval"[level:l]{'"es";'"e";'"e'"} =
   `"es-interval{i:l}(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `")"

dform nuprl_es__interval_df : except_mode[src] :: "es-interval"[level:l]{'"es";'"e";'"e'"} =
   `"[" slot{'"e"} `", " slot{'"e'"} `"]"


dform nuprl_es__haslnk_df : except_mode[src] :: "es-haslnk"[]{'"es";'"l";'"e"} =
   `"haslnk(" slot{'"l"} `";" slot{'"e"} `")"


dform nuprl_es__rcvs_df : except_mode[src] :: "es-rcvs"[]{'"es";'"l";'"e'"} =
   `"rcvs(" slot{'"l"} `";before(" slot{'"e'"} `"))"


dform nuprl_es__snds_df : except_mode[src] :: "es-snds"[]{'"es";'"l";'"e"} =
   `"snds(" slot{'"l"} `";before(" slot{'"e"} `"))"


dform nuprl_es__snds__index_df : except_mode[src] :: "es-snds-index"[]{'"es";'"l";'"e";'"n"} =
   `"snds(" slot{'"l"} `", before(" slot{'"e"} `"," slot{'"n"} `"))"


dform nuprl_es__msg_df : except_mode[src] :: "es-msg"[]{'"es";'"e"} =
   `"emsg(" slot{'"e"} `")"


dform nuprl_es__msgs_df : except_mode[src] :: "es-msgs"[]{'"the_es";'"l";'"e'"} =
   `"msgs(" slot{'"l"} `";before(" slot{'"e'"} `"))"


dform nuprl_es__tg__sends_df : except_mode[src] :: "es-tg-sends"[]{'"es";'"l";'"tg";'"e"} =
   `"sends(" slot{'"l"} `"," slot{'"tg"} `"," slot{'"e"} `")"


dform nuprl_alle__at_df : except_mode[src] :: "alle-at"[]{'"es";'"i";"e".'"P"} =
   `"alle-at(" slot{'"es"} `";" slot{'"i"} `";" slot{'"e"} `"." slot{'"P"} `")"

dform nuprl_alle__at_df : except_mode[src] :: "alle-at"[]{'"es";'"i";"e".'"P"} =
   `"" forall `"" slot{'"e"} `"@" slot{'"i"} `"." slot{'"P"} `""


dform nuprl_alle__at1_df : except_mode[src] :: "alle-at1"[]{'"es";'"i";'"x";"v".'"P"} =
   `"@" slot{'"i"} `" always." slot{'"P"} `""


dform nuprl_alle__at2_df : except_mode[src] :: "alle-at2"[]{'"es";'"i";'"x1";'"x2";"v1", "v2".'"P"} =
   `"@" slot{'"i"} `" always." slot{'"P"} `""


dform nuprl_existse__at_df : except_mode[src] :: "existse-at"[]{'"es";'"i";"e".'"P"} =
   `"" "exists" `"" slot{'"e"} `"@" slot{'"i"} `"." slot{'"P"} `""


dform nuprl_existse__le_df : except_mode[src] :: "existse-le"[]{'"es";'"e'";"e".'"P"} =
   `"existse-le(" slot{'"es"} `";" slot{'"e'"} `";" slot{'"e"} `"." slot{'"P"} `")"

dform nuprl_existse__le_df : except_mode[src] :: "existse-le"[]{'"es";'"e'";"e".'"P"} =
   `"" "exists" `"" slot{'"e"} `"" le `"" slot{'"e'"} `"." slot{'"P"} `""


dform nuprl_alle__ge_df : except_mode[src] :: "alle-ge"[]{'"es";'"e";"e'".'"P"} =
   `"alle-ge(" slot{'"es"} `";" slot{'"e"} `";" slot{'"e'"} `"." slot{'"P"} `")"

dform nuprl_alle__ge_df : except_mode[src] :: "alle-ge"[]{'"es";'"e";"e'".'"P"} =
   `"" forall `"" slot{'"e'"} `"" ge `"" slot{'"e"} `"." slot{'"P"} `""


dform nuprl_alle__rcv_df : except_mode[src] :: "alle-rcv"[]{'"es";'"l";'"tg";"e".'"P"} =
   `"alle-rcv(" slot{'"es"} `";" slot{'"l"} `";" slot{'"tg"} `";" slot{'"e"} `"."
    slot{'"P"} `")"

dform nuprl_alle__rcv_df : except_mode[src] :: "alle-rcv"[]{'"es";'"l";'"tg";"e".'"P"} =
   `"" forall `"" slot{'"e"} `"=rcv(" slot{'"l"} `"," slot{'"tg"} `")." pushm[0:n] `""
    slot{'"P"} `"" popm


dform nuprl_existse__rcv_df : except_mode[src] :: "existse-rcv"[]{'"es";'"l";'"tg";"e".'"P"} =
   `"existse-rcv(" slot{'"es"} `";" slot{'"l"} `";" slot{'"tg"} `";" slot{'"e"}
    `"." slot{'"P"} `")"

dform nuprl_existse__rcv_df : except_mode[src] :: "existse-rcv"[]{'"es";'"l";'"tg";"e".'"P"} =
   `"" "exists" `"" slot{'"e"} `"=rcv(" slot{'"l"} `"," slot{'"tg"} `")." pushm[0:n] `""
    slot{'"P"} `"" popm


dform nuprl_es__state_df : except_mode[src] :: "es-state"[]{'"es";'"i"} =
   `"es-state(" slot{'"es"} `";" slot{'"i"} `")"

dform nuprl_es__state_df : except_mode[src] :: "es-state"[]{'"es";'"i"} =
   `"state@" slot{'"i"} `""


dform nuprl_es__state__ap_df : except_mode[src] :: "es-state-ap"[]{'"s";'"x"} =
   `"es-state-ap(" slot{'"s"} `";" slot{'"x"} `")"

dform nuprl_es__state__ap_df : except_mode[src] :: "es-state-ap"[]{'"s";'"x"} =
   `"" slot{'"s"} `"." slot{'"x"} `""


dform nuprl_es__state__when_df : except_mode[src] :: "es-state-when"[]{'"es";'"e"} =
   `"es-state-when(" slot{'"es"} `";" slot{'"e"} `")"

dform nuprl_es__state__when_df : except_mode[src] :: "es-state-when"[]{'"es";'"e"} =
   `"state when " slot{'"e"} `""


dform nuprl_es__state__after_df : except_mode[src] :: "es-state-after"[]{'"es";'"e"} =
   `"es-state-after(" slot{'"es"} `";" slot{'"e"} `")"

dform nuprl_es__state__after_df : except_mode[src] :: "es-state-after"[]{'"es";'"e"} =
   `"state after " slot{'"e"} `""


dform nuprl_es__stable_df : except_mode[src] :: "es-stable"[]{'"es";'"i";"state".'"P"} =
   `"es-stable(" slot{'"es"} `";" slot{'"i"} `";" slot{'"state"} `"." slot{'"P"}
    `")"

dform nuprl_es__stable_df : except_mode[src] :: "es-stable"[]{'"es";'"i";"state".'"P"} =
   `"@" slot{'"i"} `" stable " slot{'"state"} `"." slot{'"P"} `"  "


dform nuprl_es__frame_df : except_mode[src] :: "es-frame"[]{'"es";'"i";'"L";'"x";'"T"} =
   `"es-frame(" slot{'"es"} `";" slot{'"i"} `";" slot{'"L"} `";" slot{'"x"} `";"
    slot{'"T"} `")"


dform nuprl_es__responsive_df : except_mode[src] :: "es-responsive"[]{'"es";'"l1";'"tg1";'"l2";'"tg2"} =
   `"es-responsive(" slot{'"es"} `";" slot{'"l1"} `";" slot{'"tg1"} `";"
    slot{'"l2"} `";" slot{'"tg2"} `")"


dform nuprl_es__only__sender_df : except_mode[src] :: "es-only-sender"[]{'"es";'"k";'"B";'"l";'"tg";'"T";"s", "v".'"f"} =
   `"only " slot{'"k"} `"(" slot{'"v"} `"):" slot{'"B"} `" sends [" slot{'"tg"}
    `"," slot{'"f"} `"] : " slot{'"T"} `" on " slot{'"l"} `""


