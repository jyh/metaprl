extends Ma_num_thy_1


define unfold_switch : "switch"[]{'"t";'"b"} <-->
      ('"b" '"t")


define unfold_switch_case : "switch_case"[]{'"v";'"case";'"cont"} <-->
      "lambda"[]{"x"."ifthenelse"[]{"beq_int"[]{'"x";'"v"};'"case";('"cont" '"x")}}


define unfold_switch_default : "switch_default"[]{'"body"} <-->
      "lambda"[]{"x".'"body"}


define unfold_switch_done : "switch_done"[]{} <-->
      "lambda"[]{"x"."!undefined"[]{}}


define unfold_case : "case"[]{'"value";'"body"} <-->
      (('"body" '"value") '"value")


define unfold_case_default : "case_default"[]{'"body"} <-->
      "lambda"[]{"value"."lambda"[]{"value".'"body"}}


define unfold_case_pair : "case_pair"[]{"x", "y".'"body"['"x";'"y"]} <-->
      "lambda"[]{"value"."lambda"[]{"cont"."spread"[]{'"value";"x", "y".'"body"['"x";'"y"]}}}


define unfold_case_inl : "case_inl"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"value"."lambda"[]{"contvalue"."decide"[]{'"value";"x".'"body"['"x"];"_".(('"cont" '"contvalue") '"contvalue")}}}


define unfold_case_inr : "case_inr"[]{"x".'"body"['"x"];'"cont"} <-->
      "lambda"[]{"value"."lambda"[]{"contvalue"."decide"[]{'"value";"_".(('"cont" '"contvalue") '"contvalue");"x".'"body"['"x"]}}}


define unfold_case_cons : "case_cons"[]{"x", "y".'"body"['"x";'"y"];'"cont"} <-->
      "lambda"[]{"value"."lambda"[]{"contvalue"."list_ind"[]{'"value";(('"cont" '"contvalue") '"contvalue");"hd", "tl", "f".'"body"['"hd";'"tl"]}}}


define unfold_case_nil : "case_nil"[]{'"body";'"cont"} <-->
      "lambda"[]{"value"."lambda"[]{"contvalue"."list_ind"[]{'"value";'"body";"hd", "tl", "f".(('"cont" '"contvalue") '"contvalue")}}}


define unfold_case_it : "case_it"[]{'"body"} <-->
      "lambda"[]{"value"."lambda"[]{"contvalue".'"body"}}


