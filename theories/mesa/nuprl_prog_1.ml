extends Ma_num_thy_1

open Dtactic


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



(**** display forms ****)


dform nuprl_switch_df : except_mode[src] :: "switch"[]{'"t";'"b"} =
   `"" pushm[0:n] `"Switch(" slot{'"t"} `")" sbreak[""," "] `"" slot{'"b"} `""
    popm  `""


dform nuprl_switch_case_df : except_mode[src] :: "switch_case"[]{'"v";'"case";'"cont"} =
   `"Case " slot{'"v"} `" => " pushm[0:n] `"" slot{'"case"} `"" popm  `""
    sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_switch_default_df : except_mode[src] :: "switch_default"[]{'"body"} =
   `"Default => " pushm[0:n] `"" slot{'"body"} `"" popm  `"" sbreak[""," "]
    `"EndSwitch"


dform nuprl_switch_done_df : except_mode[src] :: "switch_done"[]{} =
   `"EndSwitch"


dform nuprl_case_df : except_mode[src] :: "case"[]{'"value";'"body"} =
   `"" pushm[0:n] `"Case(" slot{'"value"} `")" sbreak[""," "] `"" slot{'"body"} `""
    popm  `""


dform nuprl_case_default_df : except_mode[src] :: "case_default"[]{'"body"} =
   `"" szone `"" pushm[4:n] `"Default =>" sbreak[""," "] `"" slot{'"body"} `""
    popm  `"" ezone `""


dform nuprl_case_pair_df : except_mode[src] :: "case_pair"[]{"x", "y".'"body"} =
   `"" pushm[4:n] `"<" slot{'"x"} `"," slot{'"y"} `"> =>" sbreak[""," "] `""
    slot{'"body"} `"" popm  `""


dform nuprl_case_inl_df : except_mode[src] :: "case_inl"[]{"x".'"body";'"cont"} =
   `"" pushm[4:n] `"inl(" slot{'"x"} `") =>" sbreak[""," "] `"" slot{'"body"} `""
    popm  `"" sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_case_inr_df : except_mode[src] :: "case_inr"[]{"x".'"body";'"cont"} =
   `"" pushm[4:n] `"inr(" slot{'"x"} `") =>" sbreak[""," "] `"" slot{'"body"} `""
    popm  `"" sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_case_cons_df : except_mode[src] :: "case_cons"[]{"x", "y".'"body";'"cont"} =
   `"" pushm[4:n] `"" slot{'"x"} `"::" slot{'"y"} `" =>" sbreak[""," "] `""
    slot{'"body"} `"" popm  `"" sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_case_nil_df : except_mode[src] :: "case_nil"[]{'"body";'"cont"} =
   `"" pushm[4:n] `"[] =>" sbreak[""," "] `"" slot{'"body"} `"" popm  `""
    sbreak[""," "] `"" slot{'"cont"} `""


dform nuprl_case_it_df : except_mode[src] :: "case_it"[]{'"body"} =
   `"" pushm[4:n] `"" cdot `" =>" sbreak[""," "] `"" slot{'"body"} `"" popm  `""




