extends Ma_message__automata


define unfold_dsys : "dsys"[level:l]{} <-->
      "fun"[]{"Id"[]{};"i"."msga"[level:l]{}}


define unfold_d__eq__Loc : "d-eq-Loc"[]{'"i";'"j"} <-->
      (("eqof"[]{"id-deq"[]{}} '"i") '"j")


define unfold_d__I : "d-I"[]{'"i"} <-->
      "lambda"[]{"l"."equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"}}


define unfold_d__O : "d-O"[]{'"i"} <-->
      "lambda"[]{"l"."equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"}}


define unfold_d__m : "d-m"[]{'"D";'"i"} <-->
      ('"D" '"i")


define unfold_d__decl : "d-decl"[]{'"D";'"i"} <-->
      "w-action-dec"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};'"i"}


define unfold_d__sub : "d-sub"[level:l]{'"D1";'"D2"} <-->
      "all"[]{"Id"[]{};"i"."ma-sub"[level:l]{"d-m"[]{'"D1";'"i"};"d-m"[]{'"D2";'"i"}}}


define unfold_d__single__init : "d-single-init"[]{'"i";'"x";'"T";'"v"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-init"[]{'"x";'"T";'"v"};"ma-empty"[]{}}}


define unfold_d__single__frame : "d-single-frame"[]{'"i";'"L";'"t";'"x"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-frame"[]{'"L";'"t";'"x"};"ma-empty"[]{}}}


define unfold_d__single__sframe : "d-single-sframe"[]{'"i";'"L";'"l";'"tg"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-empty"[]{}}}


define unfold_d__single__effect : "d-single-effect"[]{'"i";'"ds";'"da";'"k";'"x";'"f"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-empty"[]{}}}


define unfold_d__single__sends : "d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-empty"[]{}}}


define unfold_d__single__pre : "d-single-pre"[]{'"i";'"ds";'"a";'"T";'"P"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-empty"[]{}}}


define unfold_d__single__pre__init : "d-single-pre-init"[]{'"i";'"ds";'"init";'"a";'"T";'"P"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-empty"[]{}}}


define unfold_d__feasible : "d-feasible"[]{'"D"} <-->
      "and"[]{"all"[]{"Id"[]{};"i"."ma-feasible"[]{"d-m"[]{'"D";'"i"}}};"and"[]{"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."subtype"[]{"ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}}}};"all"[]{"Id"[]{};"i"."finite-type"[]{"set"[]{"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"assert"[]{"ma-sends-on"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l"}}}}}}}}


define unfold_d__world__state : "d-world-state"[]{'"D";'"i"} <-->
      "prod"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};""."prod"[]{"action"[]{"d-decl"[]{'"D";'"i"}};""."list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}}}}


define unfold_stutter__state : "stutter-state"[]{'"s"} <-->
      "pair"[]{'"s";"pair"[]{"null-action"[]{};"nil"[]{}}}


define unfold_next__world__state : "next-world-state"[]{'"D";'"i";'"s";'"k";'"v"} <-->
      "pair"[]{"lambda"[]{"x"."ma-ef-val"[]{"d-m"[]{'"D";'"i"};'"k";'"x";'"s";'"v";('"s" '"x")}};"pair"[]{"doact"[]{'"k";'"v"};"filter"[]{"lambda"[]{"m"."eq_id"[]{"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"ma-send-val"[]{"d-m"[]{'"D";'"i"};'"k";'"s";'"v"}}}}


define unfold_d__partial__world : "d-partial-world"[]{'"D";'"f";'"t'";'"s"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"fst"[]{(('"f" '"t") '"i")};('"s" '"i")}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"fst"[]{"snd"[]{(('"f" '"t") '"i")}};"null-action"[]{}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"snd"[]{"snd"[]{(('"f" '"t") '"i")}};"nil"[]{}}}};"it"[]{}}}}}}}


define unfold_d__comp : "d-comp"[]{'"D";'"v";'"sched";'"dec"} <-->
      "lambda"[]{"t"."lambda"[]{"f"."let"[]{"lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(('"f" "sub"[]{'"t";"number"[1:n]{}}) '"i")}}};"s"."lambda"[]{"i"."let"[]{('"s" '"i");"si"."let"[]{"d-partial-world"[]{'"D";'"f";'"t";'"s"};"w"."let"[]{"decide"[]{('"sched" '"i");"f"."decide"[]{('"f" '"t");"l"."ifthenelse"[]{"band"[]{"d-eq-Loc"[]{"ldst"[]{'"l"};'"i"};"lt_bool"[]{"number"[0:n]{};"length"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"doact"[]{"rcv"[]{'"l";"mtag"[]{"hd"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"mval"[]{"hd"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"null-action"[]{}};"a"."ifthenelse"[]{"is_inl"[]{((('"dec" '"i") '"a") '"si")};"doact"[]{"inr"[]{'"a"};"fst"[]{"snd"[]{"outl"[]{((('"dec" '"i") '"a") '"si")}}}};"null-action"[]{}}};"x"."null-action"[]{}};"a"."let"[]{"ifthenelse"[]{"is_inl"[]{'"a"};"nil"[]{};"filter"[]{"lambda"[]{"m"."eq_id"[]{"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"ma-send-val"[]{"d-m"[]{'"D";'"i"};"fst"[]{"outr"[]{'"a"}};'"si";"snd"[]{"outr"[]{'"a"}}}}};"m"."let"[]{"ifthenelse"[]{"is_inl"[]{'"a"};'"si";"lambda"[]{"x"."ma-ef-val"[]{"d-m"[]{'"D";'"i"};"fst"[]{"outr"[]{'"a"}};'"x";'"si";"snd"[]{"outr"[]{'"a"}};('"si" '"x")}}};"s'"."pair"[]{'"s'";"pair"[]{'"a";'"m"}}}}}}}}}}}


define unfold_d__world : "d-world"[]{'"D";'"v";'"sched";'"dec"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."fst"[]{"snd"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."snd"[]{"snd"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i")}}}};"it"[]{}}}}}}}


define unfold_d__onlnk : "d-onlnk"[]{'"l";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


define unfold_d__comp__partial__world : "d-comp-partial-world"[]{'"D";'"v";'"sched";'"dec";'"t"} <-->
      "d-partial-world"[]{'"D";"CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}};'"t";"lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}}}


define unfold_d__rename : "d-rename"[]{'"rx";'"ra";'"rt";'"D"} <-->
      "lambda"[]{"i"."ma-rename"[]{'"rx";'"ra";'"rt";('"D" '"i")}}


define unfold_interface__check : "interface-check"[]{'"D";'"l";'"tg";'"T"} <-->
      "subtype"[]{'"T";"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}}


