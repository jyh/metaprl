extends Ma_standard


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


define unfold_icomb : "icomb"[]{} <-->
      "lambda"[]{"x".'"x"}


define unfold_kcomb : "kcomb"[]{} <-->
      "lambda"[]{"x"."lambda"[]{"y".'"x"}}


define unfold_scomb : "scomb"[]{} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z".(('"x" '"z") ('"y" '"z"))}}}


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


define unfold_stable : "stable"[]{'"P"} <-->
      "implies"[]{"not"[]{"not"[]{'"P"}};'"P"}


define unfold_sq_stable : "sqst"[]{'"P"} <-->
      "implies"[]{"squash"[]{'"P"};'"P"}


define unfold_xmiddle : "xmiddle"[level:l]{} <-->
      "all"[]{"univ"[level:l]{};"P"."decidable"[]{'"P"}}


define unfold_let : "let"[]{'"a";"x".'"b"['"x"]} <-->
      ("lambda"[]{"x".'"b"['"x"]} '"a")


define unfold_type_inj : "type_inj"[]{'"x";'"T"} <-->
      '"x"


define unfold_choicef : "choicef"[]{'"xm";'"T";"x".'"P"['"x"]} <-->
      "decide"[]{('"xm" "set"[]{'"T";"y".'"P"['"y"]});"z".'"z";"w"."token"["???":t]{}}


define unfold_singleton : "singleton"[]{'"a";'"T"} <-->
      "set"[]{'"T";"x"."equal"[]{'"T";'"x";'"a"}}


define unfold_unique_set : "unique_set"[]{'"T";"x".'"P"['"x"]} <-->
      "set"[]{'"T";"x"."and"[]{'"P"['"x"];"all"[]{'"T";"y"."implies"[]{'"P"['"y"];"equal"[]{'"T";'"y";'"x"}}}}}


define unfold_uni_sat : "uni_sat"[]{'"T";'"a";"x".'"Q"['"x"]} <-->
      "and"[]{'"Q"['"a"];"all"[]{'"T";"a'"."implies"[]{'"Q"['"a'"];"equal"[]{'"T";'"a'";'"a"}}}}


