extends Ma_event__system

open Dtactic


interactive nuprl_equal_functionality_wrt_subtype_rel   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{'"A";'"x";'"y"};"equal"[]{'"B";'"x";'"y"}}} }

interactive nuprl_subtype_rel_function   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   sequent { <H> >- "subtype"[]{'"C";'"A"} }  -->
   sequent { <H> >- "subtype"[]{'"B";'"D"} }  -->
   sequent { <H> >- "subtype"[]{"fun"[]{'"A";"".'"B"};"fun"[]{'"C";"".'"D"}} }

interactive nuprl_subtype_rel_dep_function  '"A" '"C" "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"C" >- "type"{'"D"['"x"] } }  -->
   sequent { <H> >- "subtype"[]{'"C";'"A"} }  -->
   sequent { <H>; "a": '"C"  >- "subtype"[]{'"B"['"a"];'"D"['"a"]} }  -->
   sequent { <H> >- "subtype"[]{"fun"[]{'"A";"a".'"B"['"a"]};"fun"[]{'"C";"c".'"D"['"c"]}} }

interactive nuprl_subtype_rel_product  '"A" '"C" "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"C" >- "type"{'"D"['"x"] } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"C"} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"D"['"a"]} }  -->
   sequent { <H> >- "subtype"[]{"prod"[]{'"A";"a".'"B"['"a"]};"prod"[]{'"C";"c".'"D"['"c"]}} }

interactive nuprl_subtype_rel_dep_product_iff  '"A" '"C" "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"C" >- "type"{'"D"['"x"] } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"C"} }  -->
   sequent { <H> >- "iff"[]{"all"[]{'"A";"a"."subtype"[]{'"B"['"a"];'"D"['"a"]}};"subtype"[]{"prod"[]{'"A";"a".'"B"['"a"]};"prod"[]{'"C";"c".'"D"['"c"]}}} }

interactive nuprl_subtype_rel_sum   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"C"} }  -->
   sequent { <H> >- "subtype"[]{'"B";'"D"} }  -->
   sequent { <H> >- "subtype"[]{"union"[]{'"A";'"B"};"union"[]{'"C";'"D"}} }

interactive nuprl_subtype_rel_set  '"A" '"B" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subtype"[]{"set"[]{'"A";"a".'"P"['"a"]};'"B"} }

interactive nuprl_subtype_rel_list   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subtype"[]{"list"[]{'"A"};"list"[]{'"B"}} }

interactive nuprl_subtype_rel_transitivity  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subtype"[]{'"B";'"C"} }  -->
   sequent { <H> >- "subtype"[]{'"A";'"C"} }

define unfold_strong__subtype : "subset"[]{'"A";'"B"} <-->
      "cand"[]{"subtype"[]{'"A";'"B"};"cand"[]{"subtype"[]{"set"[]{'"B";"b"."exists"[]{'"A";"a"."equal"[]{'"B";'"b";'"a"}}};'"A"};"all"[]{'"A";"a1"."all"[]{'"A";"a2"."implies"[]{"equal"[]{'"B";'"a1";'"a2"};"equal"[]{'"A";'"a1";'"a2"}}}}}}


interactive nuprl_strong__subtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("subset"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_strong__subtype__self   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A"} }

interactive nuprl_strong__subtype__equal univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"A";'"B"} }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }

interactive nuprl_strong__subtype__ext__equal   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subtype"[]{'"B";'"A"} }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }

interactive nuprl_strong__subtype_transitivity  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subset"[]{'"B";'"C"} }  -->
   sequent { <H> >- "subset"[]{'"A";'"C"} }

interactive nuprl_strong__subtype__void   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "subset"[]{"void"[]{};'"T"} }

interactive nuprl_subtype_rel__equal univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"A";'"B"} }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }

interactive nuprl_subtype_rel_self   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"A"} }

interactive nuprl_strong__subtype__set  '"B" '"A" "lambda"[]{"x".'"Q"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"B" >- "type"{'"Q"['"x"] } }  -->
   sequent { <H>; "x": '"A" ; '"P"['"x"]  >- '"Q"['"x"] }  -->
   sequent { <H> >- "subset"[]{"set"[]{'"A";"x".'"P"['"x"]};"set"[]{'"B";"x".'"Q"['"x"]}} }

interactive nuprl_strong__subtype__set2  '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "subset"[]{"set"[]{'"A";"x".'"P"['"x"]};'"A"} }

interactive nuprl_strong__subtype__set3  '"A" '"B" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subset"[]{"set"[]{'"A";"x".'"P"['"x"]};'"B"} }

interactive nuprl_strong__subtype__product   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"C"} }  -->
   sequent { <H> >- "subset"[]{'"B";'"D"} }  -->
   sequent { <H> >- "subset"[]{"prod"[]{'"A";"".'"B"};"prod"[]{'"C";"".'"D"}} }

interactive nuprl_strong__subtype__dep__product  '"A" '"C" "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"C" >- "type"{'"D"['"x"] } }  -->
   sequent { <H> >- "subset"[]{'"A";'"C"} }  -->
   sequent { <H>; "a": '"A"  >- "subset"[]{'"B"['"a"];'"D"['"a"]} }  -->
   sequent { <H> >- "subset"[]{"prod"[]{'"A";"a".'"B"['"a"]};"prod"[]{'"C";"c".'"D"['"c"]}} }

interactive nuprl_strong__subtype__union   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"C"} }  -->
   sequent { <H> >- "subset"[]{'"B";'"D"} }  -->
   sequent { <H> >- "subset"[]{"union"[]{'"A";'"B"};"union"[]{'"C";'"D"}} }

interactive nuprl_strong__subtype__list   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subset"[]{"list"[]{'"A"};"list"[]{'"B"}} }

interactive nuprl_strong__subtype__l_member__type  '"B" '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"B" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"B"} }  -->
   sequent { <H> >- ('"x" in '"A") }

interactive nuprl_strong__subtype__l_member  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"B" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"B"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"A"} }

interactive nuprl_strong__subtype__eq1  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "equal"[]{'"B";'"b";'"a"} }  -->
   sequent { <H> >- "cand"[]{('"b" in '"A");"equal"[]{'"A";'"b";'"a"}} }

interactive nuprl_strong__subtype__eq2  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "equal"[]{'"B";'"b";'"a"} }  -->
   sequent { <H> >- "equal"[]{'"A";'"b";'"a"} }

interactive nuprl_strong__subtype__eq3   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{'"B";'"b";'"a"};"equal"[]{'"A";'"b";'"a"}}} }

interactive nuprl_strong__subtype__eq4   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subset"[]{'"B";'"A"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{'"A";'"b";'"a"};"equal"[]{'"B";'"b";'"a"}}} }

interactive nuprl_strong__subtype__member   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{'"B";'"b";'"a"};('"b" in '"A")}} }

interactive nuprl_sq_stable__subtype_rel   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "sqst"[]{"subtype"[]{'"A";'"B"}} }

interactive nuprl_sq_stable__strong__subtype   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "sqst"[]{"subset"[]{'"A";'"B"}} }


(**** display forms ****)


dform nuprl_strong__subtype_df : except_mode[src] :: "subset"[]{'"A";'"B"} =
   `"strong-subtype(" slot{'"A"} `";" slot{'"B"} `")"


