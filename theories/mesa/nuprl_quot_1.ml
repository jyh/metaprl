extends Ma_rel_1

open Dtactic


interactive nuprl_quotient_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   sequent { <H> >- ("quot"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_quotient_wf_type {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   sequent { <H> >- "type"{"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]}} }

interactive nuprl_quotient_qinc  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   sequent { <H> >- "subtype"[]{'"T";"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]}} }

interactive nuprl_type_inj_wf_for_quot {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]} '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   sequent { <H> >- ("type_inj"[]{'"a";"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]}} in "quot"[]{'"T";"x", "y".'"E"['"x";'"y"]}) }

interactive nuprl_quot_elim  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]} '"b" '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]};'"a";'"b"};"squash"[]{'"E"['"a";'"b"]}} }

interactive nuprl_all_quot_elim  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]} "lambda"[]{"x".'"F"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   [wf] sequent { <H>;"x": "quot"[]{'"T";"x", "y".'"E"['"x";'"y"]} >- "type"{'"F"['"x"] } }  -->
   sequent { <H>; "w": "quot"[]{'"T";"x", "y".'"E"['"x";'"y"]}  >- "sqst"[]{("lambda"[]{"x".'"F"['"x"]} '"w")} }  -->
   sequent { <H> >- "iff"[]{"all"[]{"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]};"z".'"F"['"z"]};"all"[]{'"T";"z".'"F"['"z"]}} }

interactive nuprl_dec_iff_ex_bvfun  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "iff"[]{"all"[]{'"T";"x"."all"[]{'"T";"y"."decidable"[]{'"E"['"x";'"y"]}}};"exists"[]{"fun"[]{'"T";""."fun"[]{'"T";""."bool"[]{}}};"f"."all"[]{'"T";"x"."all"[]{'"T";"y"."iff"[]{"assert"[]{"infix_ap"[]{'"f";'"x";'"y"}};'"E"['"x";'"y"]}}}}} }

interactive nuprl_decidable__quotient_equal  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]} '"v" '"u"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{'"E"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"u" in "quot"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"v" in "quot"[]{'"T";"x", "y".'"E"['"x";'"y"]} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"quot"[]{'"T";"x", "y".'"E"['"x";'"y"]};'"u";'"v"}} }


(**** display forms ****)


