extends Ma_sqequal_1


define unfold_identity : "identity"[]{} <-->
      "lambda"[]{"x".'"x"}


define unfold_tidentity : "tidentity"[]{'"T"} <-->
      "identity"[]{}


define unfold_tlambda : "tlambda"[]{'"T";"x".'"b"['"x"]} <-->
      "lambda"[]{"x".'"b"['"x"]}


define unfold_compose : "compose"[]{'"f";'"g"} <-->
      "lambda"[]{"x".('"f" ('"g" '"x"))}


define unfold_inv_funs : "inv_funs"[]{'"A";'"B";'"f";'"g"} <-->
      "and"[]{"equal"[]{"fun"[]{'"A";"".'"A"};"compose"[]{'"g";'"f"};"tidentity"[]{'"A"}};"equal"[]{"fun"[]{'"B";"".'"B"};"compose"[]{'"f";'"g"};"tidentity"[]{'"B"}}}


define unfold_one_one_corr : "one_one_corr"[]{'"A";'"B"} <-->
      "exists"[]{"fun"[]{'"A";"".'"B"};"f"."exists"[]{"fun"[]{'"B";"".'"A"};"g"."inv_funs"[]{'"A";'"B";'"f";'"g"}}}


define unfold_inject : "inject"[]{'"A";'"B";'"f"} <-->
      "all"[]{'"A";"a1"."all"[]{'"A";"a2"."implies"[]{"equal"[]{'"B";('"f" '"a1");('"f" '"a2")};"equal"[]{'"A";'"a1";'"a2"}}}}


define unfold_surject : "surject"[]{'"A";'"B";'"f"} <-->
      "all"[]{'"B";"b"."exists"[]{'"A";"a"."equal"[]{'"B";('"f" '"a");'"b"}}}


define unfold_biject : "biject"[]{'"A";'"B";'"f"} <-->
      "and"[]{"inject"[]{'"A";'"B";'"f"};"surject"[]{'"A";'"B";'"f"}}


