extends Ma_standard

open Dtactic


define unfold_ycomb : "ycomb"[]{} <-->
      "lambda"[]{"f".("lambda"[]{"x".('"f" ('"x" '"x"))} "lambda"[]{"x".('"f" ('"x" '"x"))})}


define unfold_infix_ap : "infix_ap"[]{'"f";'"x";'"y"} <-->
      (('"f" '"x") '"y")


define unfold_so_lambda2 : "lambda"[]{"x", "y".'"t"['"x";'"y"]} <-->
      "lambda"[]{"x"."lambda"[]{"y".'"t"['"x";'"y"]}}


define unfold_label : "label"[L:t]{'"t"} <-->
      '"t"


define unfold_guard : "guard"[]{'"T"} <-->
      '"T"


define unfold_error : "error1"[]{} <-->
      "token"["error":t]{}


define unfold_cand : "cand"[]{'"A";'"B"} <-->
      "prod"[]{'"A";"".'"B"}


define unfold_parameter : "parameter"[level:l]{} <-->
      "!null_abstraction"[]{}


interactive nuprl_false_wf {| intro[] |}   :
   sequent { <H> >- ("false"[]{} in "univ"[1:l]{}) }

interactive nuprl_true_wf {| intro[] |}   :
   sequent { <H> >- ("true"[]{} in "univ"[1:l]{}) }

interactive nuprl_squash_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("squash"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_guard_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("guard"[]{'"T"} in "univ"[level:l]{}) }

interactive nuprl_guard_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "type"{"guard"[]{'"T"}} }

interactive nuprl_unit_wf {| intro[] |}   :
   sequent { <H> >- ("unit"[]{} in "univ"[1:l]{}) }

interactive nuprl_unit_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"unit"[]{}} }

interactive nuprl_not_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("not"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_comb_for_not_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"z"."not"[]{'"A"}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}) }

interactive nuprl_rev_implies_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rev_implies"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_comb_for_rev_implies_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"z"."rev_implies"[]{'"A";'"B"}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"univ"[level:l]{};"B"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}) }

interactive nuprl_iff_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("iff"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_comb_for_iff_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"z"."iff"[]{'"A";'"B"}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"univ"[level:l]{};"B"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}) }

interactive nuprl_nequal_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- ("nequal"[]{'"A";'"x";'"y"} in "univ"[level:l]{}) }

interactive nuprl_comb_for_member_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"a"."lambda"[]{"z".('"a" in '"A")}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{'"A";"a"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}) }

interactive nuprl_member_wf   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- (('"a" in '"A") in "univ"[level:l]{}) }

interactive nuprl_member_wf_type   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "type"{('"a" in '"A")} }

define unfold_icomb : "icomb"[]{} <-->
      "lambda"[]{"x".'"x"}


interactive nuprl_icomb_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- ("icomb"[]{} in "fun"[]{'"A";"".'"A"}) }

define unfold_kcomb : "kcomb"[]{} <-->
      "lambda"[]{"x"."lambda"[]{"y".'"x"}}


interactive nuprl_kcomb_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- ("kcomb"[]{} in "fun"[]{'"A";""."fun"[]{'"B";"".'"A"}}) }

define unfold_scomb : "scomb"[]{} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z".(('"x" '"z") ('"y" '"z"))}}}


interactive nuprl_scomb_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- ("scomb"[]{} in "fun"[]{"fun"[]{'"A";""."fun"[]{'"B";"".'"C"}};""."fun"[]{"fun"[]{'"A";"".'"B"};""."fun"[]{'"A";"".'"C"}}}) }

interactive nuprl_pi1_wf {| intro[] |}  "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- ("fst"[]{'"p"} in '"A") }

interactive nuprl_pi2_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"p"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- ("snd"[]{'"p"} in '"B"["fst"[]{'"p"}]) }

interactive nuprl_pair_eta_rw  '"A" "lambda"[]{"x".'"B"['"x"]} '"p"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "equal"[]{"prod"[]{'"A";"a".'"B"['"a"]};"pair"[]{"fst"[]{'"p"};"snd"[]{'"p"}};'"p"} }

define unfold_spread3 : "spreadn"[]{'"a";"x", "y", "z".'"t"['"x";'"y";'"z"]} <-->
      "spread"[]{'"a";"x", "zz"."spread"[]{'"zz";"y", "z".'"t"['"x";'"y";'"z"]}}


define unfold_spread4 : "spreadn"[]{'"a";"w", "x", "y", "z".'"t"['"w";'"x";'"y";'"z"]} <-->
      "spread"[]{'"a";"w", "zz1"."spread"[]{'"zz1";"x", "zz2"."spread"[]{'"zz2";"y", "z".'"t"['"w";'"x";'"y";'"z"]}}}


define unfold_spread5 : "spreadn"[]{'"u";"a", "b", "c", "d", "e".'"v"['"a";'"b";'"c";'"d";'"e"]} <-->
      "spread"[]{'"u";"a", "zz1"."spread"[]{'"zz1";"b", "zz2"."spread"[]{'"zz2";"c", "zz3"."spread"[]{'"zz3";"d", "e".'"v"['"a";'"b";'"c";'"d";'"e"]}}}}


define unfold_spread6 : "spreadn"[]{'"u";"a", "b", "c", "d", "e", "f".'"v"['"a";'"b";'"c";'"d";'"e";'"f"]} <-->
      "spread"[]{'"u";"a", "zz1"."spread"[]{'"zz1";"b", "zz2"."spread"[]{'"zz2";"c", "zz3"."spread"[]{'"zz3";"d", "zz4"."spread"[]{'"zz4";"e", "f".'"v"['"a";'"b";'"c";'"d";'"e";'"f"]}}}}}


define unfold_spread7 : "spreadn"[]{'"u";"a", "b", "c", "d", "e", "f", "g".'"v"['"a";'"b";'"c";'"d";'"e";'"f";'"g"]} <-->
      "spread"[]{'"u";"a", "zz1"."spread"[]{'"zz1";"b", "zz2"."spread"[]{'"zz2";"c", "zz3"."spread"[]{'"zz3";"d", "zz4"."spread"[]{'"zz4";"e", "zz5"."spread"[]{'"zz5";"f", "g".'"v"['"a";'"b";'"c";'"d";'"e";'"f";'"g"]}}}}}}


interactive nuprl_it_wf {| intro[] |}   :
   sequent { <H> >- ("it"[]{} in "unit"[]{}) }

interactive nuprl_unit_triviality   :
   [wf] sequent { <H> >- '"a" in "unit"[]{} }  -->
   sequent { <H> >- "equal"[]{"unit"[]{};'"a";"it"[]{}} }

interactive nuprl_decidable_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("decidable"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_decidable__or   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "decidable"[]{'"Q"} }  -->
   sequent { <H> >- "decidable"[]{"or"[]{'"P";'"Q"}} }

interactive nuprl_decidable__and   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "decidable"[]{'"Q"} }  -->
   sequent { <H> >- "decidable"[]{"and"[]{'"P";'"Q"}} }

interactive nuprl_decidable__implies   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "decidable"[]{'"Q"} }  -->
   sequent { <H> >- "decidable"[]{"implies"[]{'"P";'"Q"}} }

interactive nuprl_decidable__false   :
   sequent { <H> >- "decidable"[]{"false"[]{}} }

interactive nuprl_decidable__not   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "decidable"[]{"not"[]{'"P"}} }

interactive nuprl_decidable__iff   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "decidable"[]{'"Q"} }  -->
   sequent { <H> >- "decidable"[]{"iff"[]{'"P";'"Q"}} }

interactive nuprl_decidable__int_equal   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"int"[]{};'"i";'"j"}} }

interactive nuprl_decidable__lt   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "decidable"[]{"lt"[]{'"i";'"j"}} }

interactive nuprl_decidable__le   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "decidable"[]{"le"[]{'"i";'"j"}} }

interactive nuprl_decidable__atom_equal   :
   [wf] sequent { <H> >- '"a" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "atom"[]{} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"atom"[]{};'"a";'"b"}} }

interactive nuprl_iff_preserves_decidability  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "decidable"[]{'"A"} }  -->
   sequent { <H> >- "iff"[]{'"A";'"B"} }  -->
   sequent { <H> >- "decidable"[]{'"B"} }

define unfold_stable : "stable"[]{'"P"} <-->
      "implies"[]{"not"[]{"not"[]{'"P"}};'"P"}


interactive nuprl_stable_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("stable"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_stable__not   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "stable"[]{"not"[]{'"P"}} }

interactive nuprl_stable__function_equal   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"A" >- '"g" '"x" in '"B" }  -->
   sequent { <H>; "x": '"A"  >- "stable"[]{"equal"[]{'"B";('"f" '"x");('"g" '"x")}} }  -->
   sequent { <H> >- "stable"[]{"equal"[]{"fun"[]{'"A";"".'"B"};'"f";'"g"}} }

interactive nuprl_stable__from_decidable   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "stable"[]{'"P"} }

define unfold_sq_stable : "sqst"[]{'"P"} <-->
      "implies"[]{"squash"[]{'"P"};'"P"}


interactive nuprl_sq_stable_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("sqst"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_sq_stable__and   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "sqst"[]{'"P"} }  -->
   sequent { <H> >- "sqst"[]{'"Q"} }  -->
   sequent { <H> >- "sqst"[]{"and"[]{'"P";'"Q"}} }

interactive nuprl_sq_stable__implies   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "sqst"[]{'"Q"} }  -->
   sequent { <H> >- "sqst"[]{"implies"[]{'"P";'"Q"}} }

interactive nuprl_sq_stable__iff   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "sqst"[]{'"P"} }  -->
   sequent { <H> >- "sqst"[]{'"Q"} }  -->
   sequent { <H> >- "sqst"[]{"iff"[]{'"P";'"Q"}} }

interactive nuprl_sq_stable__all  '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "x": '"A"  >- "sqst"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "sqst"[]{"all"[]{'"A";"x".'"P"['"x"]}} }

interactive nuprl_sq_stable__equal   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "sqst"[]{"equal"[]{'"A";'"x";'"y"}} }

interactive nuprl_sq_stable__squash   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "sqst"[]{"squash"[]{'"P"}} }

interactive nuprl_sq_stable__from_stable   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "stable"[]{'"P"} }  -->
   sequent { <H> >- "sqst"[]{'"P"} }

interactive nuprl_sq_stable__not   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "sqst"[]{"not"[]{'"P"}} }

interactive nuprl_sq_stable_from_decidable   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "decidable"[]{'"P"} }  -->
   sequent { <H> >- "sqst"[]{'"P"} }

define unfold_xmiddle : "xmiddle"[level:l]{} <-->
      "all"[]{"univ"[level:l]{};"P"."decidable"[]{'"P"}}


interactive nuprl_xmiddle_wf {| intro[] |}   :
   sequent { <H> >- ("xmiddle"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_sq_stable_iff_stable   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "iff"[]{"sqst"[]{'"P"};"stable"[]{'"P"}} }

interactive nuprl_squash_elim   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   sequent { <H> >- "sqst"[]{'"P"} }  -->
   sequent { <H> >- "iff"[]{"squash"[]{'"P"};'"P"} }

interactive nuprl_dneg_elim   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "decidable"[]{'"A"} }  -->
   sequent { <H> >- "not"[]{"not"[]{'"A"}} }  -->
   sequent { <H> >- '"A" }

interactive nuprl_dneg_elim_a   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "decidable"[]{'"A"} }  -->
   sequent { <H> >- "iff"[]{"not"[]{"not"[]{'"A"}};'"A"} }

interactive nuprl_iff_symmetry   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"iff"[]{'"A";'"B"};"iff"[]{'"B";'"A"}} }

interactive nuprl_and_assoc   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{'"A";"and"[]{'"B";'"C"}};"and"[]{"and"[]{'"A";'"B"};'"C"}} }

interactive nuprl_and_comm   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{'"A";'"B"};"and"[]{'"B";'"A"}} }

interactive nuprl_or_assoc   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{'"A";"or"[]{'"B";'"C"}};"or"[]{"or"[]{'"A";'"B"};'"C"}} }

interactive nuprl_or_comm   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{'"A";'"B"};"or"[]{'"B";'"A"}} }

interactive nuprl_not_over_or   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"not"[]{"or"[]{'"A";'"B"}};"and"[]{"not"[]{'"A"};"not"[]{'"B"}}} }

interactive nuprl_not_over_or_a   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"not"[]{"or"[]{'"A";'"B"}};"guard"[]{"and"[]{"not"[]{'"A"};"not"[]{'"B"}}}} }

interactive nuprl_not_over_and_b   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "or"[]{"not"[]{'"A"};"not"[]{'"B"}} }  -->
   sequent { <H> >- "not"[]{"and"[]{'"A";'"B"}} }

interactive nuprl_not_over_and   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "decidable"[]{'"A"} }  -->
   sequent { <H> >- "iff"[]{"not"[]{"and"[]{'"A";'"B"}};"or"[]{"not"[]{'"A"};"not"[]{'"B"}}} }

interactive nuprl_and_false_l   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{"false"[]{};'"A"};"false"[]{}} }

interactive nuprl_and_false_r   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{'"A";"false"[]{}};"false"[]{}} }

interactive nuprl_and_true_l   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{"true"[]{};'"A"};'"A"} }

interactive nuprl_and_true_r   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"and"[]{'"A";"true"[]{}};'"A"} }

interactive nuprl_or_false_l   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{"false"[]{};'"A"};'"A"} }

interactive nuprl_or_false_r   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{'"A";"false"[]{}};'"A"} }

interactive nuprl_or_true_l   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{"true"[]{};'"A"};"true"[]{}} }

interactive nuprl_or_true_r   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "iff"[]{"or"[]{'"A";"true"[]{}};"true"[]{}} }

interactive nuprl_exists_over_and_r  '"T" "lambda"[]{"x".'"B"['"x"]} '"A"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"B"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"exists"[]{'"T";"x"."and"[]{'"A";'"B"['"x"]}};"and"[]{'"A";"exists"[]{'"T";"x".'"B"['"x"]}}} }

interactive nuprl_not_over_exists  '"T" "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"not"[]{"exists"[]{'"T";"x".'"Q"['"x"]}};"all"[]{'"T";"x"."not"[]{'"Q"['"x"]}}} }

interactive nuprl_equal_symmetry   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"equal"[]{'"T";'"x";'"y"};"equal"[]{'"T";'"y";'"x"}} }

interactive nuprl_iff_transitivity  '"Q"  :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   [wf] sequent { <H> >- "type"{'"R" } }  -->
   sequent { <H> >- "iff"[]{'"P";'"Q"} }  -->
   sequent { <H> >- "iff"[]{'"Q";'"R"} }  -->
   sequent { <H> >- "iff"[]{'"P";'"R"} }

interactive nuprl_implies_transitivity  '"Q"  :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   [wf] sequent { <H> >- "type"{'"R" } }  -->
   sequent { <H>; '"P"  >- '"Q" }  -->
   sequent { <H>; '"Q"  >- '"R" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"P";'"R"}} }

interactive nuprl_and_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "iff"[]{'"P1";'"P2"} }  -->
   sequent { <H> >- "iff"[]{'"Q1";'"Q2"} }  -->
   sequent { <H> >- "iff"[]{"and"[]{'"P1";'"Q1"};"and"[]{'"P2";'"Q2"}} }

interactive nuprl_and_functionality_wrt_implies   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"P1";'"P2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"Q1";'"Q2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"and"[]{'"P1";'"Q1"};"and"[]{'"P2";'"Q2"}}} }

interactive nuprl_implies_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "iff"[]{'"P1";'"P2"} }  -->
   sequent { <H> >- "iff"[]{'"Q1";'"Q2"} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"implies"[]{'"P1";'"Q1"};"implies"[]{'"P2";'"Q2"}}} }

interactive nuprl_implies_functionality_wrt_implies   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "guard"[]{"rev_implies"[]{'"P1";'"P2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"Q1";'"Q2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"implies"[]{'"P1";'"Q1"};"implies"[]{'"P2";'"Q2"}}} }

interactive nuprl_decidable_functionality   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "iff"[]{'"P";'"Q"} }  -->
   sequent { <H> >- "iff"[]{"decidable"[]{'"P"};"decidable"[]{'"Q"}} }

interactive nuprl_iff_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "iff"[]{'"P1";'"P2"} }  -->
   sequent { <H> >- "iff"[]{'"Q1";'"Q2"} }  -->
   sequent { <H> >- "iff"[]{"iff"[]{'"P1";'"Q1"};"iff"[]{'"P2";'"Q2"}} }

interactive nuprl_all_functionality_wrt_iff univ[level:l] '"S" '"T" "lambda"[]{"x".'"Q"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"Q"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"S";'"T"} }  -->
   sequent { <H>; "x": '"S"  >- "iff"[]{'"P"['"x"];'"Q"['"x"]} }  -->
   sequent { <H> >- "iff"[]{"all"[]{'"S";"x".'"P"['"x"]};"all"[]{'"T";"y".'"Q"['"y"]}} }

interactive nuprl_all_functionality_wrt_implies univ[level:l] '"S" '"T" "lambda"[]{"x".'"Q"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"Q"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"S";'"T"} }  -->
   sequent { <H>; "z": '"S"  >- "guard"[]{"implies"[]{'"P"['"z"];'"Q"['"z"]}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"all"[]{'"S";"x".'"P"['"x"]};"all"[]{'"T";"y".'"Q"['"y"]}}} }

interactive nuprl_exists_functionality_wrt_iff univ[level:l] '"S" '"T" "lambda"[]{"x".'"Q"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"Q"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"S";'"T"} }  -->
   sequent { <H>; "x": '"S"  >- "iff"[]{'"P"['"x"];'"Q"['"x"]} }  -->
   sequent { <H> >- "iff"[]{"exists"[]{'"S";"x".'"P"['"x"]};"exists"[]{'"T";"y".'"Q"['"y"]}} }

interactive nuprl_exists_functionality_wrt_implies univ[level:l] '"S" '"T" "lambda"[]{"x".'"Q"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"Q"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"S";'"T"} }  -->
   sequent { <H>; "x": '"S"  >- "guard"[]{"implies"[]{'"P"['"x"];'"Q"['"x"]}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"exists"[]{'"S";"x".'"P"['"x"]};"exists"[]{'"T";"y".'"Q"['"y"]}}} }

interactive nuprl_not_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "iff"[]{'"P";'"Q"} }  -->
   sequent { <H> >- "iff"[]{"not"[]{'"P"};"not"[]{'"Q"}} }

interactive nuprl_not_functionality_wrt_implies   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "guard"[]{"rev_implies"[]{'"P";'"Q"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"not"[]{'"P"};"not"[]{'"Q"}}} }

interactive nuprl_or_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "iff"[]{'"P1";'"P2"} }  -->
   sequent { <H> >- "iff"[]{'"Q1";'"Q2"} }  -->
   sequent { <H> >- "iff"[]{"or"[]{'"P1";'"Q1"};"or"[]{'"P2";'"Q2"}} }

interactive nuprl_or_functionality_wrt_implies   :
   [wf] sequent { <H> >- "type"{'"P1" } }  -->
   [wf] sequent { <H> >- "type"{'"P2" } }  -->
   [wf] sequent { <H> >- "type"{'"Q1" } }  -->
   [wf] sequent { <H> >- "type"{'"Q2" } }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"P1";'"P2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"Q1";'"Q2"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"or"[]{'"P1";'"Q1"};"or"[]{'"P2";'"Q2"}}} }

interactive nuprl_squash_functionality_wrt_implies   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "guard"[]{"implies"[]{'"P";'"Q"}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"squash"[]{'"P"};"squash"[]{'"Q"}}} }

interactive nuprl_squash_functionality_wrt_iff   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H> >- "guard"[]{"iff"[]{'"P";'"Q"}} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"squash"[]{'"P"};"squash"[]{'"Q"}}} }

interactive nuprl_implies_antisymmetry   :
   [wf] sequent { <H> >- "type"{'"P" } }  -->
   [wf] sequent { <H> >- "type"{'"Q" } }  -->
   sequent { <H>; '"P"  >- '"Q" }  -->
   sequent { <H>; '"Q"  >- '"P" }  -->
   sequent { <H> >- "iff"[]{'"P";'"Q"} }

define unfold_let : "let"[]{'"a";"x".'"b"['"x"]} <-->
      ("lambda"[]{"x".'"b"['"x"]} '"a")


interactive nuprl_let_wf {| intro[] |}  '"A" '"B" "lambda"[]{"x".'"b"['"x"]} '"a"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H>;"x": '"A" >- '"b"['"x"] in '"B" }  -->
   sequent { <H> >- ("let"[]{'"a";"x".'"b"['"x"]} in '"B") }

define unfold_type_inj : "type_inj"[]{'"x";'"T"} <-->
      '"x"


define unfold_choicef : "choicef"[]{'"xm";'"T";"x".'"P"['"x"]} <-->
      "decide"[]{('"xm" "set"[]{'"T";"y".'"P"['"y"]});"z".'"z";"w"."token"["???":t]{}}


interactive nuprl_choicef_wf {| intro[] |} univ[level:l] '"T" "lambda"[]{"x".'"P"['"x"]} '"xm"  :
   [wf] sequent { <H> >- '"xm" in "xmiddle"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "exists"[]{'"T";"a".'"P"['"a"]} }  -->
   sequent { <H> >- ("choicef"[]{'"xm";'"T";"x".'"P"['"x"]} in '"T") }

interactive nuprl_choicef_lemma univ[level:l] '"T" "lambda"[]{"x".'"P"['"x"]} '"%xm"  :
   [wf] sequent { <H> >- '"%xm" in "xmiddle"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "exists"[]{'"T";"a".'"P"['"a"]} }  -->
   sequent { <H> >- '"P"["choicef"[]{'"%xm";'"T";"x".'"P"['"x"]}] }

interactive nuprl_fun_thru_spread  '"A" "lambda"[]{"x".'"B"['"x"]} '"D" '"C" "lambda"[]{"x1", "x".'"b"['"x1";'"x"]} '"p" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"x".'"B"['"x"]} }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   [wf] sequent { <H>;"x": '"C" >- '"f" '"x" in '"D" }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B"['"x"] >- '"b"['"x";'"x1"] in '"C" }  -->
   sequent { <H> >- "equal"[]{'"D";('"f" "spread"[]{'"p";"x", "y".'"b"['"x";'"y"]});"spread"[]{'"p";"x", "y".('"f" '"b"['"x";'"y"])}} }

interactive nuprl_spread_to_pi12  '"A" "lambda"[]{"x".'"B"['"x"]} '"C" "lambda"[]{"x1", "x".'"b"['"x1";'"x"]} '"p"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"x".'"B"['"x"]} }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B"['"x"] >- '"b"['"x";'"x1"] in '"C" }  -->
   sequent { <H> >- "equal"[]{'"C";"spread"[]{'"p";"x", "y".'"b"['"x";'"y"]};'"b"["fst"[]{'"p"};"snd"[]{'"p"}]} }

define unfold_singleton : "singleton"[]{'"a";'"T"} <-->
      "set"[]{'"T";"x"."equal"[]{'"T";'"x";'"a"}}


interactive nuprl_singleton_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   sequent { <H> >- ("singleton"[]{'"a";'"T"} in "univ"[level:l]{}) }

interactive nuprl_singleton_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   sequent { <H> >- "type"{"singleton"[]{'"a";'"T"}} }

interactive nuprl_singleton_properties   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "singleton"[]{'"a";'"T"} }  -->
   sequent { <H> >- "equal"[]{'"T";'"x";'"a"} }

define unfold_unique_set : "unique_set"[]{'"T";"x".'"P"['"x"]} <-->
      "set"[]{'"T";"x"."and"[]{'"P"['"x"];"all"[]{'"T";"y"."implies"[]{'"P"['"y"];"equal"[]{'"T";'"y";'"x"}}}}}


interactive nuprl_unique_set_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("unique_set"[]{'"T";"x".'"P"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_unique_set_wf_type {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "type"{"unique_set"[]{'"T";"x".'"P"['"x"]}} }

define unfold_uni_sat : "uni_sat"[]{'"T";'"a";"x".'"Q"['"x"]} <-->
      "and"[]{'"Q"['"a"];"all"[]{'"T";"a'"."implies"[]{'"Q"['"a'"];"equal"[]{'"T";'"a'";'"a"}}}}


interactive nuprl_uni_sat_wf {| intro[] |}  '"T" "lambda"[]{"x".'"Q"['"x"]} '"a"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"Q"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("uni_sat"[]{'"T";'"a";"x".'"Q"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_uni_sat_imp_in_uni_set  '"T" "lambda"[]{"x".'"Q"['"x"]} '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- "uni_sat"[]{'"T";'"a";"x".'"Q"['"x"]} }  -->
   sequent { <H> >- ('"a" in "unique_set"[]{'"T";"x".'"Q"['"x"]}) }

interactive nuprl_sq_stable__uni_sat  '"T" "lambda"[]{"x".'"Q"['"x"]} '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q"['"x"] } }  -->
   sequent { <H>; "x": '"T"  >- "sqst"[]{'"Q"['"x"]} }  -->
   sequent { <H> >- "sqst"[]{"uni_sat"[]{'"T";'"a";"x".'"Q"['"x"]}} }


(**** display forms ****)


dform nuprl_ycomb_df : except_mode[src] :: "ycomb"[]{} =
   `"Y"











dform nuprl_infix_ap_df : except_mode[src] :: "infix_ap"[]{'"f";'"a";'"b"} =
   `"" szone `"" slot{'"a"} `" " sbreak["",""] `"" slot{'"f"} `" " pushm[0:n] `""
    slot{'"b"} `"" popm  `"" ezone `""



dform nuprl_so_lambda2_df : except_mode[src] :: "lambda"[]{"x", "y".'"t"} =
   `"" lambda `"" subtwo `"" slot{'"x"} `" " slot{'"y"} `"." slot{'"t"} `""


dform nuprl_label_df : except_mode[src] :: "label"[L:t]{'"t"} =
   `"..." slot{'"L"} `"... " slot{'"t"} `""


dform nuprl_guard_df : except_mode[src] :: "guard"[]{'"t"} =
   `"{" slot{'"t"} `"}"


dform nuprl_error_df : except_mode[src] :: "error1"[]{} =
   `"???"



dform nuprl_cand_df : except_mode[src] :: "cand"[]{'"P";'"Q"} =
   `"" szone `"" slot{'"P"} `"" sbreak[""," "] `"c" wedge `" " pushm[0:n] `"" slot{'"Q"}
    `"" popm  `"" ezone `""

dform nuprl_cand_df : except_mode[src] :: "cand"[]{'"P";'"#"} =
   `"" szone `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"c" wedge `" "
    slot{'"#"} `"" ezone `""

dform nuprl_cand_df : except_mode[src] :: "cand"[]{'"P";'"Q"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"c" wedge `" " pushm[0:n]
    `"" slot{'"Q"} `"" popm  `""

dform nuprl_cand_df : except_mode[src] :: "cand"[]{'"P";'"#"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"c" wedge `" " slot{'"#"}
    `""


dform nuprl_parameter_df : except_mode[src] :: "parameter"[i:l]{} =
   `"parm{" slot{'"i"} `"}"


dform nuprl_icomb_df : except_mode[src] :: "icomb"[]{} =
   `"I"


dform nuprl_kcomb_df : except_mode[src] :: "kcomb"[]{} =
   `"K"


dform nuprl_scomb_df : except_mode[src] :: "scomb"[]{} =
   `"S"


dform nuprl_spread3_df : except_mode[src] :: "spreadn"[]{'"a";"x", "y", "z".'"t"} =
   `"let " slot{'"x"} `"," slot{'"y"} `"," slot{'"z"} `" = " slot{'"a"} `" in "
    slot{'"t"} `""


dform nuprl_spread4_df : except_mode[src] :: "spreadn"[]{'"a";"w", "x", "y", "z".'"t"} =
   `"let " slot{'"w"} `"," slot{'"x"} `"," slot{'"y"} `"," slot{'"z"} `" = "
    slot{'"a"} `" in " slot{'"t"} `""


dform nuprl_spread5_df : except_mode[src] :: "spreadn"[]{'"a";"v", "w", "x", "y", "z".'"t"} =
   `"let " slot{'"v"} `"," slot{'"w"} `"," slot{'"x"} `"," slot{'"y"} `","
    slot{'"z"} `" = " slot{'"a"} `" in " slot{'"t"} `""


dform nuprl_spread6_df : except_mode[src] :: "spreadn"[]{'"a";"u", "v", "w", "x", "y", "z".'"t"} =
   `"let " slot{'"u"} `"," slot{'"v"} `"," slot{'"w"} `"," slot{'"x"} `","
    slot{'"y"} `"," slot{'"z"} `" = " slot{'"a"} `" in " slot{'"t"} `""


dform nuprl_spread7_df : except_mode[src] :: "spreadn"[]{'"a";"t", "u", "v", "w", "x", "y", "z".'"b"} =
   `"let " slot{'"t"} `"," slot{'"u"} `"," slot{'"v"} `"," slot{'"w"} `","
    slot{'"x"} `"," slot{'"y"} `"," slot{'"z"} `" = " slot{'"a"} `" in " slot{'"b"}
    `""




dform nuprl_stable_df : except_mode[src] :: "stable"[]{'"p"} =
   `"Stable{" slot{'"p"} `"}"


dform nuprl_sq_stable_df : except_mode[src] :: "sqst"[]{'"t"} =
   `"SqStable(" slot{'"t"} `")"


dform nuprl_xmiddle_df : except_mode[src] :: "xmiddle"[i:l]{} =
   `"XM{" slot{'"i"} `"}"

dform nuprl_xmiddle_df : except_mode[src] :: "xmiddle"[level:l]{} =
   `"XM"


dform nuprl_let_df : except_mode[src] :: "let"[]{'"a";"x".'"b"} =
   `"" szone `"let " slot{'"x"} `" = " slot{'"a"} `" in" sbreak["","  "] `" "
    slot{'"b"} `"" ezone `""


dform nuprl_type_inj_df : except_mode[src] :: "type_inj"[]{'"x";'"T"} =
   `"[" slot{'"x"} `"]{" slot{'"T"} `"}"


dform nuprl_assume_xm_df : except_mode[src] :: "all"[]{"xmiddle"[level:l]{};"%xm".'"A"} =
   `"[C] " slot{'"A"} `""


dform nuprl_choicef_df : except_mode[src] :: "choicef"[]{'"a";'"T";"x".'"P"} =
   `"" member `"" slot{'"x"} `":" slot{'"T"} `". " slot{'"P"} `""

dform nuprl_choicef_df : except_mode[src] :: "choicef"[]{'"%xm";'"T";"x".'"P"} =
   `"" member `"" slot{'"x"} `":" slot{'"T"} `". " slot{'"P"} `""


dform nuprl_singleton_df : except_mode[src] :: "singleton"[]{'"x";'"A"} =
   `"{" slot{'"x"} `":" slot{'"A"} `"}"

dform nuprl_singleton_df : except_mode[src] :: "singleton"[]{'"a";"atom"[]{}} =
   `"{" slot{'"a"} `"}"


dform nuprl_unique_set_df : except_mode[src] :: "unique_set"[]{'"T";"x".'"P"} =
   `"{!" slot{'"x"} `":" slot{'"T"} `" | " szone sbreak["",""] ezone `"" pushm[0:n]
    `"" slot{'"P"} `"" popm  `"}"


dform nuprl_uni_sat_df : except_mode[src] :: "uni_sat"[]{'"T";'"a";"x".'"Q"} =
   `"" szone `"" slot{'"a"} `" = !" pushm[1:n] `"" slot{'"x"} `":" slot{'"T"} `""
    sbreak["",". "] `"" slot{'"Q"} `"" popm  `"" ezone `""


