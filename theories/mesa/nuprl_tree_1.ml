extends Ma_basic

open Dtactic


define unfold_tree_con : "tree_con"[]{'"E";'"T"} <-->
      "union"[]{'"E";"prod"[]{'"T";"".'"T"}}


interactive nuprl_tree_con_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("tree_con"[]{'"E";'"T"} in "univ"[level:l]{}) }

interactive nuprl_tree_con_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "type"{"tree_con"[]{'"E";'"T"}} }

define unfold_tree_leaf : "tree_leaf"[]{'"x"} <-->
      "inl"[]{'"x"}


define unfold_case_tree_leaf : "case_tree_leaf"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z"."decide"[]{'"x1";"x2".'"body"['"x2"];"_".(('"cont" '"z") '"z")}}}


interactive nuprl_tree_leaf_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"E" }  -->
   sequent { <H> >- ("tree_leaf"[]{'"x"} in "tree_con"[]{'"E";'"T"}) }

define unfold_tree_node : "tree_node"[]{'"x"} <-->
      "inr"[]{'"x"}


define unfold_case_tree_node : "case_tree_node"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z".("lambda"[]{"x1".(("case_inr"[]{"x2".'"body"["hd"[]{"cons"[]{'"x2";"tl"[]{'"x1"}}}];'"cont"} "hd"[]{'"x1"}) '"z")} "cons"[]{'"x1";"nil"[]{}})}}


interactive nuprl_tree_node_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in "prod"[]{'"T";"".'"T"} }  -->
   sequent { <H> >- ("tree_node"[]{'"x"} in "tree_con"[]{'"E";'"T"}) }

define unfold_tree : "tree"[]{'"E"} <-->
      "srec"[]{"T"."tree_con"[]{'"E";'"T"}}


interactive nuprl_tree_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"E" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("tree"[]{'"E"} in "univ"[level:l]{}) }

interactive nuprl_tree_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   sequent { <H> >- "type"{"tree"[]{'"E"}} }

interactive nuprl_tree_subtype   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   sequent { <H> >- "subtype"[]{"tree"[]{'"E"};"tree_con"[]{'"E";"tree"[]{'"E"}}} }

interactive nuprl_tree_subtype2   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   sequent { <H> >- "subtype"[]{"tree_con"[]{'"E";"tree"[]{'"E"}};"tree"[]{'"E"}} }

define unfold_node : "node"[]{'"x";'"y"} <-->
      "tree_node"[]{"pair"[]{'"x";'"y"}}


define unfold_case_node : "case_node"[]{"x", "y".'"body"['"x";'"y"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z"."decide"[]{'"x1";"_".(('"cont" '"z") '"z");"x2"."spread"[]{'"x2";"x3", "x2@0".'"body"['"x3";'"x2@0"]}}}}


interactive nuprl_tree_leaf_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"x" in '"E" }  -->
   sequent { <H> >- ("tree_leaf"[]{'"x"} in "tree"[]{'"E"}) }

interactive nuprl_comb_for_tree_leaf_wf2   :
   sequent { <H> >- ("lambda"[]{"E"."lambda"[]{"x"."lambda"[]{"z"."tree_leaf"[]{'"x"}}}} in "fun"[]{"univ"[level:l]{};"E"."fun"[]{'"E";"x"."fun"[]{"squash"[]{"true"[]{}};""."tree"[]{'"E"}}}}) }

interactive nuprl_tree_node_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"x" in "tree"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"y" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("tree_node"[]{"pair"[]{'"x";'"y"}} in "tree"[]{'"E"}) }

interactive nuprl_node_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"x" in "tree"[]{'"E"} }  -->
   [wf] sequent { <H> >- '"y" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("node"[]{'"x";'"y"} in "tree"[]{'"E"}) }

interactive nuprl_comb_for_node_wf   :
   sequent { <H> >- ("lambda"[]{"E"."lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."node"[]{'"x";'"y"}}}}} in "fun"[]{"univ"[level:l]{};"E"."fun"[]{"tree"[]{'"E"};"x"."fun"[]{"tree"[]{'"E"};"y"."fun"[]{"squash"[]{"true"[]{}};""."tree"[]{'"E"}}}}}) }

define unfold_t_iterate : "t_iterate"[]{'"l";'"n";'"t"} <-->
      (("ycomb"[]{} "lambda"[]{"t_iterate"."lambda"[]{"t"."case"[]{'"t";"case_node"[]{"x", "y".(('"n" ('"t_iterate" '"x")) ('"t_iterate" '"y"));"case_tree_leaf"[]{"x".('"l" '"x");"case_default"[]{"true"[]{}}}}}}}) '"t")


interactive nuprl_t_iterate_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"E" >- '"l" '"x" in '"A" }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"A" >- '"n" '"x" '"x1" in '"A" }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("t_iterate"[]{'"l";'"n";'"t"} in '"A") }

define unfold_is_leaf : "is_leaf"[]{'"t"} <-->
      "case"[]{'"t";"case_tree_leaf"[]{"l"."btrue"[]{};"case_default"[]{"bfalse"[]{}}}}


interactive nuprl_is_leaf_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("is_leaf"[]{'"t"} in "bool"[]{}) }

define unfold_is_node : "is_node"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y"."btrue"[]{};"case_default"[]{"bfalse"[]{}}}}


interactive nuprl_is_node_wf {| intro[] |}  '"E"  :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("is_node"[]{'"t"} in "bool"[]{}) }

define unfold_left_child : "left_child"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y".'"x";"case_default"[]{'"t"}}}


interactive nuprl_left_child_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("left_child"[]{'"t"} in "tree"[]{'"E"}) }

define unfold_right_child : "right_child"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y".'"y";"case_default"[]{'"t"}}}


interactive nuprl_right_child_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- ("right_child"[]{'"t"} in "tree"[]{'"E"}) }

define unfold_leaf_value : "leaf_value"[]{'"t"} <-->
      "case"[]{'"t";"case_tree_leaf"[]{"l".'"l";"case_default"[]{"true"[]{}}}}


interactive nuprl_leaf_value_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"t" in "tree"[]{'"E"} }  -->
   sequent { <H> >- "assert"[]{"is_leaf"[]{'"t"}} }  -->
   sequent { <H> >- ("leaf_value"[]{'"t"} in '"E") }

interactive nuprl_tree_leaf_one_one   :
   [wf] sequent { <H> >- "type"{'"E" } }  -->
   [wf] sequent { <H> >- '"x1" in '"E" }  -->
   [wf] sequent { <H> >- '"x2" in '"E" }  -->
   sequent { <H> >- "equal"[]{"tree"[]{'"E"};"tree_leaf"[]{'"x1"};"tree_leaf"[]{'"x2"}} }  -->
   sequent { <H> >- "equal"[]{'"E";'"x1";'"x2"} }

interactive nuprl_comb_for_tree_leaf_wf   :
   sequent { <H> >- ("lambda"[]{"E"."lambda"[]{"T"."lambda"[]{"x"."lambda"[]{"z"."tree_leaf"[]{'"x"}}}}} in "fun"[]{"univ"[level:l]{};"E"."fun"[]{"univ"[level:l]{};"T"."fun"[]{'"E";"x"."fun"[]{"squash"[]{"true"[]{}};""."tree_con"[]{'"E";'"T"}}}}}) }


(**** display forms ****)


dform nuprl_tree_con_df : except_mode[src] :: "tree_con"[]{'"E";'"T"} =
   `"tree_con(" slot{'"E"} `";" slot{'"T"} `")"


dform nuprl_tree_leaf_df : except_mode[src] :: "tree_leaf"[]{'"x"} =
   `"tree_leaf(" slot{'"x"} `")"


dform nuprl_case_tree_leaf_df : except_mode[src] :: "case_tree_leaf"[]{"x".'"body";'"cont"} =
   `"" pushm[4:n] `"Case " szone `"" pushm[0:n] `"tree_leaf(" slot{'"x"} `")" popm
    `"" ezone `" =>" sbreak[""," "] `"" slot{'"body"} `"" popm  `"" sbreak[""," "]
    `"" slot{'"cont"} `""


dform nuprl_tree_node_df : except_mode[src] :: "tree_node"[]{'"x"} =
   `"tree_node(" slot{'"x"} `")"


dform nuprl_case_tree_node_df : except_mode[src] :: "case_tree_node"[]{"x".'"body";'"cont"} =
   `"" pushm[4:n] `"Case " szone `"" pushm[0:n] `"tree_node(" slot{'"x"} `")" popm
    `"" ezone `" =>" sbreak[""," "] `"" slot{'"body"} `"" popm  `"" sbreak[""," "]
    `"" slot{'"cont"} `""


dform nuprl_tree_df : except_mode[src] :: "tree"[]{'"E"} =
   `"Tree(" slot{'"E"} `")"


dform nuprl_node_df : except_mode[src] :: "node"[]{'"x";'"y"} =
   `"" szone `"" pushm[0:n] `"tree_node(<" slot{'"x"} `", " slot{'"y"} `">)" popm
    `"" ezone `""


dform nuprl_case_node_df : except_mode[src] :: "case_node"[]{"x", "y".'"body";'"cont"} =
   `"" pushm[4:n] `"Case " szone `"" pushm[0:n] `"" slot{'"x"} `";" slot{'"y"} `""
    popm  `"" ezone `" =>" sbreak[""," "] `"" slot{'"body"} `"" popm  `""
    sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_t_iterate_df : except_mode[src] :: "t_iterate"[]{'"l";'"n";'"t"} =
   `"t_iterate(" slot{'"l"} `";" slot{'"n"} `";" slot{'"t"} `")"


dform nuprl_is_leaf_df : except_mode[src] :: "is_leaf"[]{'"t"} =
   `"is_leaf(" slot{'"t"} `")"


dform nuprl_is_node_df : except_mode[src] :: "is_node"[]{'"t"} =
   `"is_node(" slot{'"t"} `")"


dform nuprl_left_child_df : except_mode[src] :: "left_child"[]{'"t"} =
   `"left_child(" slot{'"t"} `")"


dform nuprl_right_child_df : except_mode[src] :: "right_child"[]{'"t"} =
   `"right_child(" slot{'"t"} `")"


dform nuprl_leaf_value_df : except_mode[src] :: "leaf_value"[]{'"t"} =
   `"leaf_value(" slot{'"t"} `")"


