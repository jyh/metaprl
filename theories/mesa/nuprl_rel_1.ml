extends Ma_rfunction_1

open Dtactic


define unfold_refl : "refl"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a".'"E"['"a";'"a"]}


interactive nuprl_refl_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("refl"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_refl_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]};"refl"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

define unfold_sym : "sym"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."all"[]{'"T";"b"."implies"[]{'"E"['"a";'"b"];'"E"['"b";'"a"]}}}


interactive nuprl_sym_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("sym"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_sym_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"sym"[]{'"T";"x", "y".'"R"['"x";'"y"]};"sym"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

define unfold_trans : "trans"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."all"[]{'"T";"b"."all"[]{'"T";"c"."implies"[]{'"E"['"a";'"b"];"implies"[]{'"E"['"b";'"c"];'"E"['"a";'"c"]}}}}}


interactive nuprl_trans_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("trans"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_trans_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"trans"[]{'"T";"y", "x".'"R"['"x";'"y"]};"trans"[]{'"T";"y", "x".'"R'"['"x";'"y"]}} }

interactive nuprl_trans_rel_self_functionality  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"a'"."all"[]{'"T";"b"."all"[]{'"T";"b'"."implies"[]{'"R"['"b";'"a"];"implies"[]{'"R"['"a'";'"b'"];"implies"[]{'"R"['"a";'"a'"];'"R"['"b";'"b'"]}}}}}}}} }

define unfold_equiv_rel : "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"E"['"x";'"y"]};"and"[]{"sym"[]{'"T";"x", "y".'"E"['"x";'"y"]};"trans"[]{'"T";"x", "y".'"E"['"x";'"y"]}}}


interactive nuprl_equiv_rel_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_equiv_rel_subtyping  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]} "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "equiv_rel"[]{"set"[]{'"T";"z".'"Q"['"z"]};"x", "y".'"R"['"x";'"y"]} }

define unfold_preorder : "preorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]};"trans"[]{'"T";"x", "y".'"R"['"x";'"y"]}}


interactive nuprl_preorder_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("preorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

define unfold_symmetrize : "symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} <-->
      "and"[]{'"R"['"a";'"b"];'"R"['"b";'"a"]}


interactive nuprl_symmetrize_wf {| intro[] |} univ[j:l] '"T" '"b" '"a" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[j:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- ("symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} in "univ"[level:l]{}) }

interactive nuprl_symmetrized_preorder  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "preorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"a", "b"."symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"}} }

interactive nuprl_trans_rel_func_wrt_sym_self  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"a'"."all"[]{'"T";"b"."all"[]{'"T";"b'"."implies"[]{"symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"};"implies"[]{"symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a'";'"b'"};"iff"[]{'"R"['"a";'"a'"];'"R"['"b";'"b'"]}}}}}}}} }

interactive nuprl_equiv_rel_iff   :
   sequent { <H> >- "equiv_rel"[]{"univ"[level:l]{};"A", "B"."iff"[]{'"A";'"B"}} }

interactive nuprl_equiv_rel_functionality_wrt_iff univ[level:l] '"T" '"T'" "lambda"[]{"x1", "x".'"E'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T'" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T'";"x1": '"T'" >- '"E'"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"T";'"T'"} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"E"['"x";'"y"];'"E'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]};"equiv_rel"[]{'"T'";"x", "y".'"E'"['"x";'"y"]}} }

interactive nuprl_equiv_rel_self_functionality  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"a'"."all"[]{'"T";"b"."all"[]{'"T";"b'"."implies"[]{'"R"['"a";'"b"];"implies"[]{'"R"['"a'";'"b'"];"iff"[]{'"R"['"a";'"a'"];'"R"['"b";'"b'"]}}}}}}}} }

interactive nuprl_squash_thru_equiv_rel  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E"['"x";'"x1"] } }  -->
   sequent { <H> >- "squash"[]{"equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]}} }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"x", "y"."squash"[]{'"E"['"x";'"y"]}} }

define unfold_eqfun_p : "eqfun_p"[]{'"T";'"eq"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."iff"[]{"assert"[]{"infix_ap"[]{'"eq";'"x";'"y"}};"equal"[]{'"T";'"x";'"y"}}}}


interactive nuprl_eqfun_p_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"eq" '"x" '"x1" in "bool"[]{} }  -->
   sequent { <H> >- ("eqfun_p"[]{'"T";'"eq"} in "univ"[level:l]{}) }

interactive nuprl_sq_stable__eqfun_p   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"eq" '"x" '"x1" in "bool"[]{} }  -->
   sequent { <H> >- "sqst"[]{"eqfun_p"[]{'"T";'"eq"}} }

define unfold_anti_sym : "anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{'"R"['"x";'"y"];"implies"[]{'"R"['"y";'"x"];"equal"[]{'"T";'"x";'"y"}}}}}


interactive nuprl_anti_sym_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_anti_sym_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]};"anti_sym"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

define unfold_st_anti_sym : "st_anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."not"[]{"and"[]{'"R"['"x";'"y"];'"R"['"y";'"x"]}}}}


interactive nuprl_st_anti_sym_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("st_anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

define unfold_strict_part : "strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} <-->
      "and"[]{'"R"['"a";'"b"];"not"[]{'"R"['"b";'"a"]}}


interactive nuprl_strict_part_wf {| intro[] |}  '"T" '"b" '"a" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- ("strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} in "univ"[level:l]{}) }

interactive nuprl_strict_part_irrefl  "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{'"T";'"a";'"b"}} }

define unfold_connex : "connex"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."or"[]{'"R"['"x";'"y"];'"R"['"y";'"x"]}}}


interactive nuprl_connex_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("connex"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_connex_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]};"connex"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

interactive nuprl_connex_functionality_wrt_implies  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "guard"[]{"implies"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]};"connex"[]{'"T";"x", "y".'"R'"['"x";'"y"]}}} }

interactive nuprl_connex_iff_trichot  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "a": '"T" ; "b": '"T"  >- "decidable"[]{'"R"['"a";'"b"]} }  -->
   sequent { <H> >- "iff"[]{"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]};"guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"b"."or"[]{"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"};"or"[]{"symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"};"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"b";'"a"}}}}}}} }

define unfold_order : "order"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]};"and"[]{"trans"[]{'"T";"x", "y".'"R"['"x";'"y"]};"anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]}}}


interactive nuprl_order_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("order"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_order_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"order"[]{'"T";"x", "y".'"R"['"x";'"y"]};"order"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

define unfold_linorder : "linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"order"[]{'"T";"x", "y".'"R"['"x";'"y"]};"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]}}


interactive nuprl_linorder_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_linorder_functionality_wrt_iff  '"T" "lambda"[]{"x1", "x".'"R'"['"x1";'"x"]} "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R'"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "iff"[]{'"R"['"x";'"y"];'"R'"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]};"linorder"[]{'"T";"x", "y".'"R'"['"x";'"y"]}} }

interactive nuprl_sq_stable__refl  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "sqst"[]{'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "sqst"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]}} }

interactive nuprl_sq_stable__sym  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "sqst"[]{'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "sqst"[]{"sym"[]{'"T";"y", "x".'"R"['"x";'"y"]}} }

interactive nuprl_sq_stable__trans  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "sqst"[]{'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "sqst"[]{"trans"[]{'"T";"y", "x".'"R"['"x";'"y"]}} }

interactive nuprl_sq_stable__anti_sym  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "sqst"[]{"anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]}} }

interactive nuprl_sq_stable__connex  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "sqst"[]{"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]}} }

interactive nuprl_order_split  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]} '"b" '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "order"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{"equal"[]{'"T";'"x";'"y"}} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "iff"[]{'"R"['"a";'"b"];"or"[]{"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"};"equal"[]{'"T";'"a";'"b"}}} }

define unfold_irrefl : "irrefl"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."not"[]{'"E"['"a";'"a"]}}


interactive nuprl_irrefl_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"E"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"E"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("irrefl"[]{'"T";"x", "y".'"E"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_trans_imp_sp_trans  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"a", "b".'"R"['"a";'"b"]} }  -->
   sequent { <H> >- "trans"[]{'"T";"a", "b"."strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"}} }

interactive nuprl_trans_imp_sp_trans_a  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"a", "b".'"R"['"a";'"b"]} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"b"."all"[]{'"T";"c"."implies"[]{'"R"['"a";'"b"];"implies"[]{"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"b";'"c"};"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"c"}}}}}}} }

interactive nuprl_trans_imp_sp_trans_b  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"a", "b".'"R"['"a";'"b"]} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"a"."all"[]{'"T";"b"."all"[]{'"T";"c"."implies"[]{"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"};"implies"[]{'"R"['"b";'"c"];"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"c"}}}}}}} }

interactive nuprl_linorder_le_neg  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]} '"b" '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H> >- "linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "iff"[]{"not"[]{'"R"['"a";'"b"]};"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"b";'"a"}} }

interactive nuprl_linorder_lt_neg  '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]} '"b" '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{'"R"['"x";'"y"]} }  -->
   sequent { <H> >- "linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "iff"[]{"not"[]{"strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"}};'"R"['"b";'"a"]} }


(**** display forms ****)


dform nuprl_refl_df : except_mode[src] :: "refl"[]{'"T";"x", "y".'"E"} =
   `"Refl(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"E"} `")"

dform nuprl_refl_df : except_mode[src] :: "refl"[]{'"T";"_1", "_2".'"E"} =
   `"Refl(" slot{'"T"} `")(" slot{'"E"} `")"


dform nuprl_sym_df : except_mode[src] :: "sym"[]{'"T";"x", "y".'"E"} =
   `"Sym(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"E"} `")"


dform nuprl_trans_df : except_mode[src] :: "trans"[]{'"T";"x", "y".'"E"} =
   `"Trans(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"E"} `")"

dform nuprl_trans_df : except_mode[src] :: "trans"[]{'"T";"_1", "_2".'"E"} =
   `"Trans(" slot{'"T"} `")(" slot{'"E"} `")"


dform nuprl_equiv_rel_df : except_mode[src] :: "equiv_rel"[]{'"T";"x", "y".'"E"} =
   `"EquivRel(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"E"} `")"

dform nuprl_equiv_rel_df : except_mode[src] :: "equiv_rel"[]{'"T";"_1", "_2".'"E"} =
   `"EquivRel(" slot{'"T"} `")(" slot{'"E"} `")"


dform nuprl_preorder_df : except_mode[src] :: "preorder"[]{'"T";"x", "y".'"R"} =
   `"Preorder(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_symmetrize_df : except_mode[src] :: "symmetrize"[]{"x", "y".'"R";'"a";'"b"} =
   `"Symmetrize(" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `";" slot{'"a"} `";"
    slot{'"b"} `")"

dform nuprl_symmetrize_df : except_mode[src] :: "symmetrize"[]{"_1", "_2".'"R";'"a";'"b"} =
   `"" longrightarrow `"" longleftarrow `"(" slot{'"R"} `")(" slot{'"a"} `"," slot{'"b"} `")"


dform nuprl_eqfun_p_df : except_mode[src] :: "eqfun_p"[]{'"T";'"eq"} =
   `"IsEqFun(" slot{'"T"} `";" slot{'"eq"} `")"


dform nuprl_anti_sym_df : except_mode[src] :: "anti_sym"[]{'"T";"x", "y".'"R"} =
   `"AntiSym(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_st_anti_sym_df : except_mode[src] :: "st_anti_sym"[]{'"T";"x", "y".'"R"} =
   `"StAntiSym(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_strict_part_df : except_mode[src] :: "strict_part"[]{"x", "y".'"R";'"a";'"b"} =
   `"strict_part(" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `";" slot{'"a"} `";"
    slot{'"b"} `")"


dform nuprl_connex_df : except_mode[src] :: "connex"[]{'"T";"x", "y".'"R"} =
   `"Connex(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_order_df : except_mode[src] :: "order"[]{'"T";"x", "y".'"R"} =
   `"Order(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_linorder_df : except_mode[src] :: "linorder"[]{'"T";"x", "y".'"R"} =
   `"Linorder(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"R"} `")"


dform nuprl_irrefl_df : except_mode[src] :: "irrefl"[]{'"T";"x", "y".'"E"} =
   `"Irrefl(" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"E"} `")"


