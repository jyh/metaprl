extends Ma_Obvious

open Dtactic


interactive nuprl_simp_lemma1   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "iff"[]{"implies"[]{"false"[]{};'"P"};"true"[]{}} }

interactive nuprl_ite_false   :
   [wf] sequent { <H> >- '"b" in "bool"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"x" } }  -->
   sequent { <H> >- "iff"[]{"ifthenelse"[]{'"b";'"x";"false"[]{}};"and"[]{"assert"[]{'"b"};'"x"}} }

interactive nuprl_iflift_1  '"B" '"A" '"y" '"x" '"c" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"c" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in '"B" }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "equal"[]{'"B";'"f"["ifthenelse"[]{'"c";'"x";'"y"}];"ifthenelse"[]{'"c";'"f"['"x"];'"f"['"y"]}} }

interactive_rw nuprl_iflift_sq_1  '"y" '"x" '"c" "lambda"[]{"x".'"f"['"x"]}  :
   ('"c" in "bool"[]{}) -->
   '"f"["ifthenelse"[]{'"c";'"x";'"y"}] <--> "ifthenelse"[]{'"c";'"f"['"x"];'"f"['"y"]}

interactive nuprl_cand_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"a1" } }  -->
   [wf] sequent { <H> >- "type"{'"a2" } }  -->
   [wf] sequent { <H> >- "type"{'"b1" } }  -->
   [wf] sequent { <H> >- "type"{'"b2" } }  -->
   sequent { <H> >- "iff"[]{'"a1";'"a2"} }  -->
   sequent { <H> >- "iff"[]{'"b1";'"b2"} }  -->
   sequent { <H> >- "iff"[]{"cand"[]{'"a1";'"b1"};"cand"[]{'"a2";'"b2"}} }

interactive_rw nuprl_trivial_ite_2   :
   ('"b" in "bool"[]{}) -->
   "ifthenelse"[]{'"b";'"a";'"a"} <--> '"a"

interactive_rw nuprl_ite_and_reduce   :
   ('"b1" in "bool"[]{}) -->
   ('"b2" in "bool"[]{}) -->
   "ifthenelse"[]{'"b1";"ifthenelse"[]{'"b2";'"x";'"y"};'"y"} <--> "ifthenelse"[]{"band"[]{'"b1";'"b2"};'"x";'"y"}

define unfold_so_lambda3 : "lambda"[]{"x", "y", "z".'"t"['"x";'"y";'"z"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z".'"t"['"x";'"y";'"z"]}}}


define unfold_so_lambda4 : "lambda"[]{"x", "y", "z", "w".'"t"['"x";'"y";'"z";'"w"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"w".'"t"['"x";'"y";'"z";'"w"]}}}}


define unfold_so_lambda5 : "lambda"[]{"x", "y", "z", "w", "v".'"t"['"x";'"y";'"z";'"w";'"v"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"w"."lambda"[]{"v".'"t"['"x";'"y";'"z";'"w";'"v"]}}}}}


define unfold_so_lambda6 : "lambda"[]{"x", "y", "z", "u", "v", "w".'"t"['"x";'"y";'"z";'"u";'"v";'"w"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"u"."lambda"[]{"v"."lambda"[]{"w".'"t"['"x";'"y";'"z";'"u";'"v";'"w"]}}}}}}


interactive_rw nuprl_select_cons_tl_sq  '"T"  :
   "type"{'"T"} -->
   ('"x" in '"T") -->
   ('"l" in "list"[]{'"T"}) -->
   ('"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}}) -->
   "select"[]{"add"[]{'"i";"number"[1:n]{}};"cons"[]{'"x";'"l"}} <--> "select"[]{'"i";'"l"}

define unfold_hide : "hide"[]{'"x"} <-->
      '"x"


interactive nuprl_hide_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- ("hide"[]{'"x"} in '"T") }

define unfold_exists__ : "exists!"[]{'"T";"x".'"P"['"x"]} <-->
      "exists"[]{'"T";"x"."and"[]{'"P"['"x"];"all"[]{'"T";"y"."implies"[]{'"P"['"y"];"equal"[]{'"T";'"y";'"x"}}}}}


interactive nuprl_exists___wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("exists!"[]{'"T";"x".'"P"['"x"]} in "univ"[level:l]{}) }

define unfold_opt : "opt"[]{'"b";'"x"} <-->
      "ifthenelse"[]{'"b";"inl"[]{'"x"};"inr"[]{"it"[]{}}}


interactive nuprl_opt_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in "bool"[]{} }  -->
   sequent { <H> >- ("opt"[]{'"b";'"x"} in "union"[]{'"T";"unit"[]{}}) }

define unfold_isect2 : "isect2"[]{'"T1";'"T2"} <-->
      "isect"[]{"bool"[]{};"b"."ifthenelse"[]{'"b";'"T1";'"T2"}}


interactive nuprl_isect2_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T2" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("isect2"[]{'"T1";'"T2"} in "univ"[level:l]{}) }

interactive nuprl_isect2_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   sequent { <H> >- "type"{"isect2"[]{'"T1";'"T2"}} }

interactive nuprl_isect2_decomp   :
   [wf] sequent { <H> >- "type"{'"t1" } }  -->
   [wf] sequent { <H> >- "type"{'"t2" } }  -->
   [wf] sequent { <H> >- '"x" in "isect2"[]{'"t1";'"t2"} }  -->
   sequent { <H> >- "and"[]{('"x" in '"t1");('"x" in '"t2")} }

interactive nuprl_isect_prod_lemma   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- "subtype"[]{"isect2"[]{"prod"[]{'"A";"".'"B"};"prod"[]{'"A";"".'"C"}};"prod"[]{'"A";""."isect2"[]{'"B";'"C"}}} }

define unfold_decision : "decision"[]{} <-->
      "union"[]{"top"[]{};"top"[]{}}


interactive nuprl_decision_wf {| intro[] |}   :
   sequent { <H> >- ("decision"[]{} in "univ"[level:l]{}) }

interactive nuprl_decision_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"decision"[]{}} }

define unfold_dec2bool : "dec2bool"[]{'"d"} <-->
      "decide"[]{'"d";"x"."btrue"[]{};"x"."bfalse"[]{}}


interactive nuprl_dec2bool_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"d" in "decision"[]{} }  -->
   sequent { <H> >- ("dec2bool"[]{'"d"} in "bool"[]{}) }

interactive nuprl_inr_eq_bfalse   :
   sequent { <H> >- "equal"[]{"decision"[]{};"inr"[]{'"x"};"bfalse"[]{}} }

interactive nuprl_inl_eq_btrue   :
   sequent { <H> >- "equal"[]{"decision"[]{};"inl"[]{'"x"};"btrue"[]{}} }

interactive nuprl_bool_decision   :
   [wf] sequent { <H> >- '"x" in "bool"[]{} }  -->
   sequent { <H> >- ('"x" in "decision"[]{}) }

interactive nuprl_inr_wf {| intro[] |}   :
   sequent { <H> >- ("inr"[]{'"x"} in "decision"[]{}) }

interactive nuprl_comb_for_inr_wf   :
   sequent { <H> >- ("lambda"[]{"x"."lambda"[]{"z"."inr"[]{'"x"}}} in "fun"[]{"top"[]{};"x"."fun"[]{"squash"[]{"true"[]{}};""."decision"[]{}}}) }

interactive nuprl_inl_wf {| intro[] |}   :
   sequent { <H> >- ("inl"[]{'"x"} in "decision"[]{}) }

interactive nuprl_comb_for_inl_wf   :
   sequent { <H> >- ("lambda"[]{"x"."lambda"[]{"z"."inl"[]{'"x"}}} in "fun"[]{"top"[]{};"x"."fun"[]{"squash"[]{"true"[]{}};""."decision"[]{}}}) }

interactive nuprl_decidable_decision  '"P"  :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- '"x" in "decidable"[]{'"P"} }  -->
   sequent { <H> >- ('"x" in "decision"[]{}) }

interactive nuprl_dec2bool_decidable   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- '"p" in "decidable"[]{'"P"} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"assert"[]{"dec2bool"[]{'"p"}};'"P"}} }

interactive nuprl_eqtt_assert_2   :
   [wf] sequent { <H> >- '"b" in "decision"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"decision"[]{};'"b";"btrue"[]{}};"assert"[]{'"b"}} }

interactive nuprl_eqff_assert_2   :
   [wf] sequent { <H> >- '"b" in "decision"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"decision"[]{};'"b";"bfalse"[]{}};"not"[]{"assert"[]{'"b"}}} }

interactive nuprl_assert_dec2bool   :
   [wf] sequent { <H> >- '"d" in "decision"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"dec2bool"[]{'"d"}};"assert"[]{'"d"}} }

define unfold_increasing : "increasing"[]{'"f";'"k"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};"i"."lt"[]{('"f" '"i");('"f" "add"[]{'"i";"number"[1:n]{}})}}


interactive nuprl_increasing_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int"[]{} }  -->
   sequent { <H> >- ("increasing"[]{'"f";'"k"} in "univ"[level:l]{}) }

interactive nuprl_decidable__cand univ[level:l]  :
   [wf] sequent { <H> >- '"P" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"Q" in "isect"[]{'"P";"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H>; '"P"  >- "decidable"[]{'"Q"} }  -->
   sequent { <H> >- "decidable"[]{"cand"[]{'"P";'"Q"}} }

interactive nuprl_subtype_top   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "subtype"[]{'"T";"top"[]{}} }


(**** display forms ****)


dform nuprl_hide_df : except_mode[src] :: "hide"[]{'"x"} =
   `"..."


dform nuprl_exists___df : except_mode[src] :: "exists!"[]{'"A";"x".'"B"} =
   `"" szone `"" "exists" `"!" pushm[0:n] `"" slot{'"x"} `":" pushm[0:n] `"" slot{'"A"} `""
    popm  `"" sbreak["",". "] `"" slot{'"B"} `"" popm  `"" ezone `""

dform nuprl_exists___df : except_mode[src] :: "exists!"[]{'"FLOATDOWN";"x".'"#"} =
   `"" szone `"" "exists" `"!" pushm[0:n] `"" slot{'"x"} `"" slot{'"#"} `"" popm  `"" ezone
    `""

dform nuprl_exists___df : except_mode[src] :: "exists!"[]{'"A";"x".'"B"} =
   `"," slot{'"x"} `":" pushm[0:n] `"" slot{'"A"} `"" popm  `"" sbreak["",". "] `""
    slot{'"B"} `"" popm  `""

dform nuprl_exists___df : except_mode[src] :: "exists!"[]{'"FLOATDOWN";"x".'"#"} =
   `"," slot{'"x"} `"" slot{'"#"} `""


dform nuprl_opt_df : except_mode[src] :: "opt"[]{'"b";'"x"} =
   `"(" slot{'"b"} `"?" slot{'"x"} `")"


dform nuprl_isect2_df : except_mode[src] :: "isect2"[]{'"T1";'"T2"} =
   `"" slot{'"T1"} `" " cap `" " slot{'"T2"} `""


dform nuprl_decision_df : except_mode[src] :: "decision"[]{} =
   `"Decision"


dform nuprl_dec2bool_df : except_mode[src] :: "dec2bool"[]{'"d"} =
   `"dec2bool(" slot{'"d"} `")"


dform nuprl_increasing_df : except_mode[src] :: "increasing"[]{'"f";'"k"} =
   `"increasing(" slot{'"f"} `";" slot{'"k"} `")"


dform nuprl_isect_df_2 : except_mode[src] :: "isect"[]{'"A";"".'"B"} =
   `"" slot{'"B"} `" given " slot{'"A"} `""


