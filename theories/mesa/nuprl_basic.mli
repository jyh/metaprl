extends Ma_Obvious


define unfold_so_lambda3 : "lambda"[]{"x", "y", "z".'"t"['"x";'"y";'"z"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z".'"t"['"x";'"y";'"z"]}}}


define unfold_so_lambda4 : "lambda"[]{"x", "y", "z", "w".'"t"['"x";'"y";'"z";'"w"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"w".'"t"['"x";'"y";'"z";'"w"]}}}}


define unfold_so_lambda5 : "lambda"[]{"x", "y", "z", "w", "v".'"t"['"x";'"y";'"z";'"w";'"v"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"w"."lambda"[]{"v".'"t"['"x";'"y";'"z";'"w";'"v"]}}}}}


define unfold_so_lambda6 : "lambda"[]{"x", "y", "z", "u", "v", "w".'"t"['"x";'"y";'"z";'"u";'"v";'"w"]} <-->
      "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"z"."lambda"[]{"u"."lambda"[]{"v"."lambda"[]{"w".'"t"['"x";'"y";'"z";'"u";'"v";'"w"]}}}}}}


define unfold_hide : "hide"[]{'"x"} <-->
      '"x"


define unfold_exists__ : "exists!"[]{'"T";"x".'"P"['"x"]} <-->
      "exists"[]{'"T";"x"."and"[]{'"P"['"x"];"all"[]{'"T";"y"."implies"[]{'"P"['"y"];"equal"[]{'"T";'"y";'"x"}}}}}


define unfold_opt : "opt"[]{'"b";'"x"} <-->
      "ifthenelse"[]{'"b";"inl"[]{'"x"};"inr"[]{"it"[]{}}}


define unfold_isect2 : "isect2"[]{'"T1";'"T2"} <-->
      "isect"[]{"bool"[]{};"b"."ifthenelse"[]{'"b";'"T1";'"T2"}}


define unfold_decision : "decision"[]{} <-->
      "union"[]{"top"[]{};"top"[]{}}


define unfold_dec2bool : "dec2bool"[]{'"d"} <-->
      "decide"[]{'"d";"x"."btrue"[]{};"x"."bfalse"[]{}}


define unfold_increasing : "increasing"[]{'"f";'"k"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};"i"."lt"[]{('"f" '"i");('"f" "add"[]{'"i";"number"[1:n]{}})}}


