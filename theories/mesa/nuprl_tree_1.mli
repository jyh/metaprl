extends Ma_basic


define unfold_tree_con : "tree_con"[]{'"E";'"T"} <-->
      "union"[]{'"E";"prod"[]{'"T";"".'"T"}}


define unfold_tree_leaf : "tree_leaf"[]{'"x"} <-->
      "inl"[]{'"x"}


define unfold_case_tree_leaf : "case_tree_leaf"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z"."decide"[]{'"x1";"x2".'"body"['"x2"];"_".(('"cont" '"z") '"z")}}}


define unfold_tree_node : "tree_node"[]{'"x"} <-->
      "inr"[]{'"x"}


define unfold_case_tree_node : "case_tree_node"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z".("lambda"[]{"x1".(("case_inr"[]{"x2".'"body"["hd"[]{"cons"[]{'"x2";"tl"[]{'"x1"}}}];'"cont"} "hd"[]{'"x1"}) '"z")} "cons"[]{'"x1";"nil"[]{}})}}


define unfold_tree : "tree"[]{'"E"} <-->
      "srec"[]{"T"."tree_con"[]{'"E";'"T"}}


define unfold_node : "node"[]{'"x";'"y"} <-->
      "tree_node"[]{"pair"[]{'"x";'"y"}}


define unfold_case_node : "case_node"[]{"x", "y".'"body"['"x";'"y"];'"cont"} <-->
      "lambda"[]{"x1"."lambda"[]{"z"."decide"[]{'"x1";"_".(('"cont" '"z") '"z");"x2"."spread"[]{'"x2";"x3", "x2@0".'"body"['"x3";'"x2@0"]}}}}


define unfold_t_iterate : "t_iterate"[]{'"l";'"n";'"t"} <-->
      (("ycomb"[]{} "lambda"[]{"t_iterate"."lambda"[]{"t"."case"[]{'"t";"case_node"[]{"x", "y".(('"n" ('"t_iterate" '"x")) ('"t_iterate" '"y"));"case_tree_leaf"[]{"x".('"l" '"x");"case_default"[]{"true"[]{}}}}}}}) '"t")


define unfold_is_leaf : "is_leaf"[]{'"t"} <-->
      "case"[]{'"t";"case_tree_leaf"[]{"l"."btrue"[]{};"case_default"[]{"bfalse"[]{}}}}


define unfold_is_node : "is_node"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y"."btrue"[]{};"case_default"[]{"bfalse"[]{}}}}


define unfold_left_child : "left_child"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y".'"x";"case_default"[]{'"t"}}}


define unfold_right_child : "right_child"[]{'"t"} <-->
      "case"[]{'"t";"case_node"[]{"x", "y".'"y";"case_default"[]{'"t"}}}


define unfold_leaf_value : "leaf_value"[]{'"t"} <-->
      "case"[]{'"t";"case_tree_leaf"[]{"l".'"l";"case_default"[]{"true"[]{}}}}


