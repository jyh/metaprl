extends Ma_decidable__equality


define unfold_event_system_typename : "event_system_typename"[]{} <-->
      "int_seg"[]{"number"[0:n]{};"number"[6:n]{}}


define unfold_strongwellfounded : "strongwellfounded"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "exists"[]{"fun"[]{'"T";""."nat"[]{}};"f"."all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{'"R"['"x";'"y"];"lt"[]{('"f" '"x");('"f" '"y")}}}}}


define unfold_rel_plus : "rel_plus"[]{'"T";'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."exists"[]{"nat_plus"[]{};"n"."infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"x";'"y"}}}}


define unfold_first : "first"[]{'"pred?";'"e"} <-->
      "bnot"[]{"is_inl"[]{('"pred?" '"e")}}


define unfold_pred : "pred"[]{'"pred?";'"e"} <-->
      "outl"[]{('"pred?" '"e")}


define unfold_ecase1 : "ecase1"[]{'"e";'"info";"i".'"f"['"i"];"l", "e'".'"g"['"l";'"e'"]} <-->
      "decide"[]{('"info" '"e");"p".'"f"["fst"[]{'"p"}];"q".'"g"["fst"[]{"fst"[]{'"q"}};"snd"[]{"fst"[]{'"q"}}]}


define unfold_loc : "loc"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i".'"i";"l", "e'"."ldst"[]{'"l"}}


define unfold_rcv__ : "rcv?"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."bfalse"[]{};"l", "e'"."btrue"[]{}}


define unfold_sender : "sender"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."it"[]{};"l", "e'".'"e'"}


define unfold_link : "link"[]{'"info";'"e"} <-->
      "ecase1"[]{'"e";'"info";"i"."it"[]{};"l", "e'".'"l"}


define unfold_pred__ : "pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"} <-->
      "or"[]{"cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}};"cand"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"equal"[]{'"E";'"e";"sender"[]{'"info";'"e'"}}}}


define unfold_cless : "cless"[]{'"E";'"pred?";'"info";'"e";'"e'"} <-->
      (("rel_plus"[]{'"E";"lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}} '"e") '"e'")


define unfold_sends__bound : "sends-bound"[]{'"p";'"e";'"l"} <-->
      "fst"[]{(('"p" '"e") '"l")}


define unfold_eventlist : "eventlist"[]{'"pred?";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"eventlist"."lambda"[]{"e"."ifthenelse"[]{"first"[]{'"pred?";'"e"};"cons"[]{'"e";"nil"[]{}};"append"[]{('"eventlist" "pred"[]{'"pred?";'"e"});"cons"[]{'"e";"nil"[]{}}}}}}) '"e")


define unfold_rcv__from__on : "rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"} <-->
      "band"[]{"rcv?"[]{'"info";'"r"};"band"[]{(("eqof"[]{'"dE"} '"e") "sender"[]{'"info";'"r"});(("eqof"[]{'"dL"} '"l") "link"[]{'"info";'"r"})}}


define unfold_receives : "receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"} <-->
      "filter"[]{"lambda"[]{"r"."rcv-from-on"[]{'"dE";'"dL";'"info";'"e";'"l";'"r"}};"eventlist"[]{'"pred?";"sends-bound"[]{'"p";'"e";'"l"}}}


define unfold_index : "index"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"r"} <-->
      "mu"[]{"lambda"[]{"i".(("eqof"[]{'"dE"} '"r") "select"[]{'"i";"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";"sender"[]{'"info";'"r"};"link"[]{'"info";'"r"}}})}}


define unfold_EOrderAxioms : "EOrderAxioms"[level:l]{'"E";'"pred?";'"info"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")};"equal"[]{'"E";'"e";'"e'"}}}}};"and"[]{"strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"equal"[]{"Id"[]{};"loc"[]{'"info";"sender"[]{'"info";'"e"}};"lsrc"[]{"link"[]{'"info";'"e"}}}}};"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"implies"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e"};"link"[]{'"info";'"e'"}};"implies"[]{"cless"[]{'"E";'"pred?";'"info";"sender"[]{'"info";'"e"};"sender"[]{'"info";'"e'"}};"cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}}}}}}}}}}


define unfold_EOrder : "EOrder"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."top"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."top"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."top"[]{}}}}}}


define unfold_EState : "EState"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."top"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."top"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."top"[]{}}}}}}}}}}


define unfold_EKind : "EKind"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"top"[]{};"unused"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."top"[]{}}}}}}}}}}}


define unfold_kind : "kind"[]{'"info";'"e"} <-->
      "decide"[]{('"info" '"e");"p"."locl"[]{"snd"[]{'"p"}};"q"."rcv"[]{"fst"[]{"fst"[]{'"q"}};"snd"[]{'"q"}}}


define unfold_rtag : "rtag"[]{'"info";'"e"} <-->
      "decide"[]{('"info" '"e");"p"."it"[]{};"q"."snd"[]{'"q"}}


define unfold_EVal : "EVal"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{'"E";""."union"[]{'"E";"unit"[]{}}};"pred?"."prod"[]{"fun"[]{'"E";""."union"[]{"prod"[]{"Id"[]{};""."Id"[]{}};"prod"[]{"prod"[]{"IdLnk"[]{};"".'"E"};""."Id"[]{}}}};"info"."prod"[]{"EOrderAxioms"[level:l]{'"E";'"pred?";'"info"};"oaxioms"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" "loc"[]{'"info";'"e"}) '"x")}};"after"."prod"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}};"saxiom"."prod"[]{"fun"[]{"Knd"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"V"."prod"[]{"fun"[]{'"E";"e".(('"V" "kind"[]{'"info";'"e"}) "loc"[]{'"info";'"e"})};"val"."top"[]{}}}}}}}}}}}}


define unfold_rmsg : "rmsg"[]{'"info";'"val";'"e"} <-->
      "msg"[]{"link"[]{'"info";'"e"};"rtag"[]{'"info";'"e"};('"val" '"e")}


define unfold_sends : "sends"[]{'"dE";'"dL";'"pred?";'"info";'"val";'"p";'"e";'"l"} <-->
      "map"[]{"lambda"[]{"r"."rmsg"[]{'"info";'"val";'"r"}};"receives"[]{'"dE";'"dL";'"pred?";'"info";'"p";'"e";'"l"}}


define unfold_SESAxioms : "SESAxioms"[level:l]{'"E";'"T";'"pred?";'"info";'"when";'"after"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."exists"[]{'"E";"e'"."all"[]{'"E";"e''"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e''"}};"implies"[]{"equal"[]{'"E";"sender"[]{'"info";'"e''"};'"e"};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e''"};'"l"};"and"[]{"or"[]{"equal"[]{'"E";'"e''";'"e'"};"cless"[]{'"E";'"pred?";'"info";'"e''";'"e'"}};"equal"[]{"Id"[]{};"loc"[]{'"info";'"e'"};"ldst"[]{'"l"}}}}}}}}}};"cand"[]{"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"union"[]{'"E";"unit"[]{}};('"pred?" '"e");('"pred?" '"e'")};"equal"[]{'"E";'"e";'"e'"}}}}};"and"[]{"strongwellfounded"[]{'"E";"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"equal"[]{"Id"[]{};"loc"[]{'"info";"pred"[]{'"pred?";'"e"}};"loc"[]{'"info";'"e"}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"equal"[]{"Id"[]{};"loc"[]{'"info";"sender"[]{'"info";'"e"}};"lsrc"[]{"link"[]{'"info";'"e"}}}}};"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"rcv?"[]{'"info";'"e"}};"implies"[]{"assert"[]{"rcv?"[]{'"info";'"e'"}};"implies"[]{"equal"[]{"IdLnk"[]{};"link"[]{'"info";'"e"};"link"[]{'"info";'"e'"}};"implies"[]{"cless"[]{'"E";'"pred?";'"info";"sender"[]{'"info";'"e"};"sender"[]{'"info";'"e'"}};"cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}}}}}}}}};"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e"}}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" "loc"[]{'"info";'"e"}) '"x");(('"when" '"x") '"e");(('"after" '"x") "pred"[]{'"pred?";'"e"})}}}}}}


define unfold_eventtype : "eventtype"[]{'"k";'"loc";'"V";'"M";'"e"} <-->
      "kindcase"[]{('"k" '"e");"a".(('"V" ('"loc" '"e")) '"a");"l", "t".(('"M" '"l") '"t")}


define unfold_ESAxioms : "ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"} <-->
      "and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e");('"loc" '"e'")};"or"[]{(('"causl" '"e") '"e'");"or"[]{"equal"[]{'"E";'"e";'"e'"};(('"causl" '"e'") '"e")}}}}};"and"[]{"all"[]{'"E";"e"."iff"[]{"assert"[]{('"first" '"e")};"all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e'");('"loc" '"e")};"not"[]{(('"causl" '"e'") '"e")}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{('"first" '"e")}};"and"[]{"and"[]{"equal"[]{"Id"[]{};('"loc" ('"pred" '"e"));('"loc" '"e")};(('"causl" ('"pred" '"e")) '"e")};"all"[]{'"E";"e'"."implies"[]{"equal"[]{"Id"[]{};('"loc" '"e'");('"loc" '"e")};"not"[]{"and"[]{(('"causl" ('"pred" '"e")) '"e'");(('"causl" '"e'") '"e")}}}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"not"[]{"assert"[]{('"first" '"e")}};"all"[]{"Id"[]{};"x"."equal"[]{(('"T" ('"loc" '"e")) '"x");(('"when" '"x") '"e");(('"after" '"x") ('"pred" '"e"))}}}};"and"[]{"trans"[]{'"E";"e", "e'".(('"causl" '"e") '"e'")};"and"[]{"strongwellfounded"[]{'"E";"e", "e'".(('"causl" '"e") '"e'")};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"equal"[]{"Msg"[]{'"M"};"select"[]{('"index" '"e");(('"sends" "lnk"[]{('"kind" '"e")}) ('"sender" '"e"))};"msg"[]{"lnk"[]{('"kind" '"e")};"tagof"[]{('"kind" '"e")};('"val" '"e")}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};(('"causl" ('"sender" '"e")) '"e")}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{(('"causl" '"e") '"e'");"or"[]{"cand"[]{"not"[]{"assert"[]{('"first" '"e'")}};"or"[]{(('"causl" '"e") ('"pred" '"e'"));"equal"[]{'"E";'"e";('"pred" '"e'")}}};"cand"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"or"[]{(('"causl" '"e") ('"sender" '"e'"));"equal"[]{'"E";'"e";('"sender" '"e'")}}}}}}};"and"[]{"all"[]{'"E";"e"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"equal"[]{"Id"[]{};('"loc" '"e");"ldst"[]{"lnk"[]{('"kind" '"e")}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."implies"[]{"not"[]{"equal"[]{"Id"[]{};('"loc" '"e");"lsrc"[]{'"l"}}};"equal"[]{"list"[]{"Msg_sub"[]{'"l";'"M"}};(('"sends" '"l") '"e");"nil"[]{}}}}};"and"[]{"all"[]{'"E";"e"."all"[]{'"E";"e'"."implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e")}};"implies"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"implies"[]{"equal"[]{"IdLnk"[]{};"lnk"[]{('"kind" '"e")};"lnk"[]{('"kind" '"e'")}};"iff"[]{(('"causl" '"e") '"e'");"or"[]{(('"causl" ('"sender" '"e")) ('"sender" '"e'"));"and"[]{"equal"[]{'"E";('"sender" '"e");('"sender" '"e'")};"lt"[]{('"index" '"e");('"index" '"e'")}}}}}}}}};"all"[]{'"E";"e"."all"[]{"IdLnk"[]{};"l"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{(('"sends" '"l") '"e")}};"n"."exists"[]{'"E";"e'"."cand"[]{"assert"[]{"isrcv"[]{('"kind" '"e'")}};"and"[]{"equal"[]{"IdLnk"[]{};"lnk"[]{('"kind" '"e'")};'"l"};"and"[]{"equal"[]{'"E";('"sender" '"e'");'"e"};"equal"[]{"int"[]{};('"index" '"e'");'"n"}}}}}}}}}}}}}}}}}}}}


define unfold_event_system : "event_system"[level:l]{} <-->
      "prod"[]{"univ"[level:l]{};"E"."prod"[]{"deq"[]{'"E"};"eq"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"V"."prod"[]{"fun"[]{"IdLnk"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"M"."prod"[]{"top"[]{};"unused"."prod"[]{"fun"[]{'"E";""."Id"[]{}};"loc"."prod"[]{"fun"[]{'"E";""."Knd"[]{}};"kind"."prod"[]{"fun"[]{'"E";"e"."eventtype"[]{'"kind";'"loc";'"V";'"M";'"e"}};"val"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" ('"loc" '"e")) '"x")}};"when"."prod"[]{"fun"[]{"Id"[]{};"x"."fun"[]{'"E";"e".(('"T" ('"loc" '"e")) '"x")}};"after"."prod"[]{"fun"[]{"IdLnk"[]{};"l"."fun"[]{'"E";""."list"[]{"Msg_sub"[]{'"l";'"M"}}}};"sends"."prod"[]{"fun"[]{"set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}};"".'"E"};"sender"."prod"[]{"fun"[]{"set"[]{'"E";"e"."assert"[]{"isrcv"[]{('"kind" '"e")}}};"e"."int_seg"[]{"number"[0:n]{};"length"[]{(('"sends" "lnk"[]{('"kind" '"e")}) ('"sender" '"e"))}}};"index"."prod"[]{"fun"[]{'"E";""."bool"[]{}};"first"."prod"[]{"fun"[]{"set"[]{'"E";"e'"."not"[]{"assert"[]{('"first" '"e'")}}};"e'".'"E"};"pred"."prod"[]{"fun"[]{'"E";""."fun"[]{'"E";""."univ"[level:l]{}}};"causl"."prod"[]{"ESAxioms"[level:l]{'"E";'"T";'"M";'"loc";'"kind";'"val";'"when";'"after";'"sends";'"sender";'"index";'"first";'"pred";'"causl"};"p"."top"[]{}}}}}}}}}}}}}}}}}}}


define unfold_mk__es : "mk-es"[]{'"E";'"eq";'"T";'"V";'"M";'"loc";'"k";'"v";'"w";'"a";'"snds";'"sndr";'"i";'"f";'"prd";'"cl";'"p"} <-->
      "pair"[]{'"E";"pair"[]{'"eq";"pair"[]{'"T";"pair"[]{'"V";"pair"[]{'"M";"pair"[]{"it"[]{};"pair"[]{'"loc";"pair"[]{'"k";"pair"[]{'"v";"pair"[]{'"w";"pair"[]{'"a";"pair"[]{'"snds";"pair"[]{'"sndr";"pair"[]{'"i";"pair"[]{'"f";"pair"[]{'"prd";"pair"[]{'"cl";"pair"[]{'"p";"it"[]{}}}}}}}}}}}}}}}}}}}


define unfold_mk__eval : "mk-eval"[]{'"E";'"eq";'"prd";'"info";'"oax";'"T";'"w";'"a";'"sax";'"V";'"v"} <-->
      "pair"[]{'"E";"pair"[]{'"eq";"pair"[]{'"prd";"pair"[]{'"info";"pair"[]{'"oax";"pair"[]{'"T";"pair"[]{'"w";"pair"[]{'"a";"pair"[]{'"sax";"pair"[]{'"V";"pair"[]{'"v";"it"[]{}}}}}}}}}}}}


define unfold_EVal_to_ES : "EVal_to_ES"[level:l]{'"e"} <-->
      "spread"[]{'"e";"E", "e1"."spread"[]{'"e1";"eq", "e2"."spread"[]{'"e2";"pred?", "e3"."spread"[]{'"e3";"info", "e4"."spread"[]{'"e4";"oaxioms", "e5"."spread"[]{'"e5";"T", "e6"."spread"[]{'"e6";"when", "e7"."spread"[]{'"e7";"after", "e8"."spread"[]{'"e8";"saxiom", "e9"."spread"[]{'"e9";"V", "e10"."spread"[]{'"e10";"val", "e11"."spread"[]{'"oaxioms";"o1", "o2"."mk-es"[]{'"E";'"eq";'"T";"lambda"[]{"i"."lambda"[]{"a".(('"V" "locl"[]{'"a"}) '"i")}};"lambda"[]{"l"."lambda"[]{"tg".(('"V" "rcv"[]{'"l";'"tg"}) "ldst"[]{'"l"})}};"lambda"[]{"e"."loc"[]{'"info";'"e"}};"lambda"[]{"e"."kind"[]{'"info";'"e"}};'"val";'"when";'"after";"lambda"[]{"l"."lambda"[]{"e"."sends"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";'"val";'"o1";'"e";'"l"}}};"lambda"[]{"e"."sender"[]{'"info";'"e"}};"lambda"[]{"e"."index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";'"o1";'"e"}};"lambda"[]{"e"."first"[]{'"pred?";'"e"}};"lambda"[]{"e"."pred"[]{'"pred?";'"e"}};"lambda"[]{"e"."lambda"[]{"e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%7"."decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) '"e") '"e'") "it"[]{});"%9"."inl"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%10"."inl"[]{'"%10"}}}}) '"e") '"e'") '"%9")};"%10"."inr"[]{"decide"[]{'"%10";"%11"."inl"[]{"it"[]{}};"%12"."inr"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%13"."inl"[]{'"%13"}}}}) '"e'") '"e") '"%12")}}}}}}};"pair"[]{"lambda"[]{"e"."pair"[]{"lambda"[]{"%"."lambda"[]{"e'"."lambda"[]{"%6"."lambda"[]{"%12"."any"[]{"any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e"."implies"[]{"cless"[]{'"E";'"pred?";'"info";'"e";'"e"};"false"[]{}}}) "lambda"[]{"j"."lambda"[]{"%"."lambda"[]{"%2"."it"[]{}}}}) '"e") "spread"[]{((((((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e'"."implies"[]{"equal"[]{"Id"[]{};"loc"[]{'"info";'"e"};"loc"[]{'"info";'"e'"}};(("rel_star"[]{'"E";"lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}} '"e") '"e'")}}) "lambda"[]{"j1"."lambda"[]{"%3"."decide"[]{("termof"[]{} "first"[]{'"pred?";'"j1"});"%5"."lambda"[]{"%6"."pair"[]{"number"[0:n]{};"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(((('"p5" '"e") '"j1") "it"[]{}) "it"[]{})}}}}}};"%6"."lambda"[]{"%7".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) '"e") "pred"[]{'"pred?";'"j1"}) '"j1") ((('"%3" "pred"[]{'"pred?";'"j1"}) "pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12"."it"[]{}}}}})) ((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "pred"[]{'"pred?";'"j1"}) '"j1") "pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}))}}}}) '"e'") "it"[]{});"n", "%14"."decide"[]{"int_eq"[]{'"n";"number"[0:n]{};"inl"[]{"it"[]{}};"inr"[]{"lambda"[]{""."it"[]{}}}};"%16".'"%12";"%17".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") "pair"[]{'"n";(((((((("termof"[]{} '"n") '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%18"."inl"[]{'"%18"}}}}) '"e") '"e'") '"%14")}) '"%12")}})}}}}}};"lambda"[]{"%"."decide"[]{("termof"[]{} "first"[]{'"pred?";'"e"});"%7".'"%7";"%8"."any"[]{((('"%" "pred"[]{'"pred?";'"e"}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(('"p9" '"e") "lambda"[]{""."it"[]{}})}}}}) ((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "pred"[]{'"pred?";'"e"}) '"e") "inl"[]{"pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}}))}}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"%"."pair"[]{"pair"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(('"p9" '"e") "lambda"[]{""."it"[]{}})}}}};((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "pred"[]{'"pred?";'"e"}) '"e") "inl"[]{"pair"[]{"lambda"[]{""."it"[]{}};"it"[]{}}})};"lambda"[]{"e'"."lambda"[]{"%10"."lambda"[]{"%11"."spread"[]{'"%11";"%12", "%13"."spread"[]{"decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) "pred"[]{'"pred?";'"e"}) '"e'") "it"[]{});"%22".'"%22";"%23"."decide"[]{'"%23";"%24"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e'") '"%12")};"%25"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e'") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e'") "pred"[]{'"pred?";'"e"}) '"e'") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"e'") "pred"[]{'"pred?";'"e"}) '"%25")) '"%12"))}}};"n", "%27"."spread"[]{"decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) '"e'") '"e") "it"[]{});"%22".'"%22";"%23"."decide"[]{'"%23";"%24"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e") '"%13")};"%25"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"e") '"e'") '"%25")) '"%13"))}}};"n1", "%28"."decide"[]{("termof"[]{} "beq_int"[]{"add"[]{'"n";'"n1"};"number"[0:n]{}});"%32"."it"[]{};"%33"."spread"[]{((((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) '"n") '"n1") "pred"[]{'"pred?";'"e"}) '"e'") '"e") '"%27") '"%28");"z", "%30"."spread"[]{'"%30";"%31", "%32"."spread"[]{'"%31";"%33", "%34"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"x"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"x";'"x"}}}) "lambda"[]{"j"."lambda"[]{"%16"."lambda"[]{"%17"."it"[]{}}}}) '"z") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%14"."inl"[]{'"%14"}}}}) '"z") '"z") "pair"[]{"sub"[]{"add"[]{'"n";'"n1"};"number"[1:n]{}};'"%32"}))}}}}}}}}}}}}}};"pair"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"saxiom"}}}};"pair"[]{(("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}});"pair"[]{((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}});"pair"[]{"lambda"[]{"e"."lambda"[]{"%"."it"[]{}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"%".((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "sender"[]{'"info";'"e"}) '"e") "inr"[]{"pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"it"[]{}}})}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."decide"[]{((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"%");"%20"."decide"[]{'"%20";"%21"."inl"[]{"pair"[]{"spread"[]{'"%21";"%22", "%23".'"%22"};"spread"[]{'"%21";"%22", "%23"."inr"[]{"it"[]{}}}}};"%22"."inr"[]{"pair"[]{"spread"[]{'"%22";"%23", "%24".("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%13"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%13"."it"[]{}}}}} '"%23")};"spread"[]{'"%22";"%23", "%24"."inr"[]{"it"[]{}}}}}};"%21"."spread"[]{'"%21";"z", "%22"."spread"[]{'"%22";"%23", "%24"."decide"[]{'"%24";"%25"."inl"[]{"pair"[]{"spread"[]{'"%25";"%26", "%27".'"%26"};"spread"[]{'"%25";"%26", "%27"."inl"[]{'"%23"}}}};"%26"."inr"[]{"pair"[]{"spread"[]{'"%26";"%27", "%28".("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%24"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%24"."it"[]{}}}}} '"%27")};"spread"[]{'"%26";"%27", "%28"."inl"[]{'"%23"}}}}}}}}}}};"pair"[]{"lambda"[]{"e"."decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"l"."lambda"[]{"%"."it"[]{}}}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."lambda"[]{"%16"."lambda"[]{"%17"."spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12"."pair"[]{"lambda"[]{"%22"."decide"[]{((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"info") '"pred?") ((((((("termof"[]{} '"E") '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "lambda"[]{"e", "e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}) "it"[]{}) "lambda"[]{"e"."lambda"[]{"e'"."lambda"[]{"%"."inl"[]{'"%"}}}}) ((("termof"[]{} '"E") "lambda"[]{"e", "e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}}))) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p9"}}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p5"}}}}) "sender"[]{'"info";'"e"}) "sender"[]{'"info";'"e'"}) "it"[]{});"%27"."inl"[]{((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%28"."inl"[]{'"%28"}}}}) "sender"[]{'"info";'"e"}) "sender"[]{'"info";'"e'"}) '"%27")};"%28"."decide"[]{'"%28";"%29"."inr"[]{"pair"[]{"it"[]{};"decide"[]{"less"[]{"index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};'"e"};"index"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};'"e'"};"inr"[]{"lambda"[]{""."lambda"[]{""."it"[]{}}}};"inl"[]{"lambda"[]{""."it"[]{}}}};"%31"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e1"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"e1";'"e1"}}}) "lambda"[]{"j"."lambda"[]{"%34"."lambda"[]{"%35"."it"[]{}}}}) '"e") "decide"[]{"decide"[]{(((((((("termof"[]{} '"E") '"eq") "receives"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) '"e'") '"e") "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e'");"%47", "%48".('"%48" "pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16");"pair"[]{"it"[]{};"it"[]{}}})}) "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e");"%47", "%48".('"%48" "pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"pair"[]{"it"[]{};"it"[]{}}})}) "lambda"[]{""."it"[]{}});"%33"."inl"[]{(((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"pred?") '"info") '"e") '"e'") "sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) "spread"[]{'"p7";"f", "%22"."pair"[]{'"f";"lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%27".((('"%22" '"x") '"y") "inl"[]{'"%27"})}}}}}) "spread"[]{("spread"[]{((((("termof"[]{} '"E") "eventlist"[]{'"pred?";"sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}}) "lambda"[]{"r"."rcv-from-on"[]{'"eq";"idlnk-deq"[]{};'"info";"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"};'"r"}}) '"e'") '"e");"%35", "%36".'"%35"} '"%33");"%37", "%38"."spread"[]{'"%38";"%39", "%40".'"%40"}})};"%34"."inr"[]{"it"[]{}}};"%34".((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") '"%22") '"%34");"%35".'"%22"})};"%32"."it"[]{}}}};"%30"."any"[]{((((((("termof"[]{} '"E") "lambda"[]{"e", "e'"."cless"[]{'"E";'"pred?";'"info";'"e";'"e'"}}) ((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".'"p7"}}}})) "lambda"[]{"e1"."not"[]{"cless"[]{'"E";'"pred?";'"info";'"e1";'"e1"}}}) "lambda"[]{"j"."lambda"[]{"%39"."lambda"[]{"%40"."it"[]{}}}}) '"e") ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) '"e") '"e'") '"e") '"%22") (((((('"p12" '"e'") '"e") ("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16")) ("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%")) "it"[]{}) ((((((("termof"[]{} '"E") "lambda"[]{"e"."lambda"[]{"e'"."cand"[]{"not"[]{"assert"[]{"first"[]{'"pred?";'"e'"}}};"equal"[]{'"E";'"e";"pred"[]{'"pred?";'"e'"}}}}}) "lambda"[]{"e"."lambda"[]{"e'"."pred!"[]{'"E";'"pred?";'"info";'"e";'"e'"}}}) "lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%31"."inl"[]{'"%31"}}}}) "sender"[]{'"info";'"e'"}) "sender"[]{'"info";'"e"}) '"%30"))))}}}};"lambda"[]{"%22"."decide"[]{'"%22";"%23".(((((('"p12" '"e") '"e'") ("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%")) ("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16")) "it"[]{}) '"%23");"%24"."spread"[]{'"%24";"%25", "%26".(((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"pred?") '"info") '"e'") '"e") "sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) "spread"[]{'"p7";"f", "%22"."pair"[]{'"f";"lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%27".((('"%22" '"x") '"y") "inl"[]{'"%27"})}}}}}) "spread"[]{("spread"[]{((((("termof"[]{} '"E") "eventlist"[]{'"pred?";"sends-bound"[]{"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}}) "lambda"[]{"r"."rcv-from-on"[]{'"eq";"idlnk-deq"[]{};'"info";"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"};'"r"}}) '"e") '"e'");"%29", "%30".'"%29"} (((((((("termof"[]{} '"E") '"eq") "receives"[]{'"eq";"idlnk-deq"[]{};'"pred?";'"info";"fst"[]{'"oaxioms"};"sender"[]{'"info";'"e"};"link"[]{'"info";'"e"}}) '"e") '"e'") "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e");"%42", "%43".('"%43" "pair"[]{("decide"[]{('"info" '"e");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%");"pair"[]{"it"[]{};"it"[]{}}})}) "spread"[]{(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{'"oaxioms"}) "sender"[]{'"info";'"e"}) "link"[]{'"info";'"e"}) '"p7") '"p9") '"p5") '"e'");"%42", "%43".('"%43" "pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%19"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%19"."it"[]{}}}}} '"%16");"pair"[]{"it"[]{};"it"[]{}}})}) "it"[]{}));"%31", "%32"."spread"[]{'"%32";"%33", "%34".'"%34"}})}}}}}}}}}}}}};"lambda"[]{"e"."lambda"[]{"l"."lambda"[]{"n"."spread"[]{"spread"[]{"snd"[]{'"oaxioms"};"p5", "p6"."spread"[]{'"p6";"p7", "p8"."spread"[]{'"p8";"p9", "p10"."spread"[]{'"p10";"p11", "p12".(((((((((((((("termof"[]{} '"E") "Id"[]{}) "Id"[]{}) '"eq") "idlnk-deq"[]{}) '"pred?") '"info") "fst"[]{"pair"[]{"fst"[]{'"oaxioms"};"pair"[]{"pair"[]{'"p5";"pair"[]{'"p7";"pair"[]{'"p9";"pair"[]{'"p11";'"p12"}}}};'"saxiom"}}}) '"p7") '"p9") '"p5") '"e") '"l") '"n")}}}};"e'", "%20"."spread"[]{'"%20";"%21", "%22"."spread"[]{'"%22";"%23", "%24"."spread"[]{'"%24";"%25", "%26"."pair"[]{'"e'";"pair"[]{("decide"[]{('"info" '"e'");"x1"."spread"[]{'"x1";"x2", "x3"."lambda"[]{"%"."it"[]{}}};"y"."spread"[]{'"y";"y1", "y2"."spread"[]{'"y1";"y3", "y4"."lambda"[]{"%"."it"[]{}}}}} '"%21");"pair"[]{"it"[]{};"pair"[]{"it"[]{};"it"[]{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}


define unfold_es__E : "es-E"[]{'"es"} <-->
      "fst"[]{'"es"}


define unfold_es__eq__E : "es-eq-E"[]{'"es";'"e";'"e'"} <-->
      (("eqof"[]{"fst"[]{"snd"[]{'"es"}}} '"e") '"e'")


define unfold_es__LnkTag__deq : "es-LnkTag-deq"[]{} <-->
      "product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}}


define unfold_es__Msg : "es-Msg"[]{'"es"} <-->
      "Msg"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}


define unfold_es__Msgl : "es-Msgl"[]{'"es";'"l"} <-->
      "set"[]{"es-Msg"[]{'"es"};"m"."haslink"[]{'"l";'"m"}}


define unfold_es__loc : "es-loc"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}} '"e")


define unfold_es__kind : "es-kind"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}} '"e")


define unfold_es__isrcv : "es-isrcv"[]{'"es";'"e"} <-->
      "isrcv"[]{"es-kind"[]{'"es";'"e"}}


define unfold_es__tag : "es-tag"[]{'"es";'"e"} <-->
      "tagof"[]{"es-kind"[]{'"es";'"e"}}


define unfold_es__lnk : "es-lnk"[]{'"es";'"e"} <-->
      "lnk"[]{"es-kind"[]{'"es";'"e"}}


define unfold_es__act : "es-act"[]{'"es";'"e"} <-->
      "actof"[]{"es-kind"[]{'"es";'"e"}}


define unfold_es__kindcase : "es-kindcase"[]{'"es";'"e";"a".'"f"['"a"];"l", "tg".'"g"['"l";'"tg"]} <-->
      "ifthenelse"[]{"es-isrcv"[]{'"es";'"e"};'"g"["es-lnk"[]{'"es";'"e"};"es-tag"[]{'"es";'"e"}];'"f"["es-act"[]{'"es";'"e"}]}


define unfold_es__msgtype : "es-msgtype"[]{'"es";'"m"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}} "mlnk"[]{'"m"}) "mtag"[]{'"m"})


define unfold_es__rcvtype : "es-rcvtype"[]{'"es";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}} "es-lnk"[]{'"es";'"e"}) "es-tag"[]{'"es";'"e"})


define unfold_es__acttype : "es-acttype"[]{'"es";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}} "es-loc"[]{'"es";'"e"}) "es-act"[]{'"es";'"e"})


define unfold_es__valtype : "es-valtype"[]{'"es";'"e"} <-->
      "ifthenelse"[]{"es-isrcv"[]{'"es";'"e"};"es-rcvtype"[]{'"es";'"e"};"es-acttype"[]{'"es";'"e"}}


define unfold_es__vartype : "es-vartype"[]{'"es";'"i";'"x"} <-->
      (("fst"[]{"snd"[]{"snd"[]{'"es"}}} '"i") '"x")


define unfold_es__val : "es-val"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}} '"e")


define unfold_es__when : "es-when"[]{'"es";'"x";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}} '"x") '"e")


define unfold_es__after : "es-after"[]{'"es";'"x";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}} '"x") '"e")


define unfold_es__sends : "es-sends"[]{'"es";'"l";'"e"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}} '"l") '"e")


define unfold_es__sender : "es-sender"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}} '"e")


define unfold_es__index : "es-index"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}} '"e")


define unfold_es__first : "es-first"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}} '"e")


define unfold_es__pred : "es-pred"[]{'"es";'"e"} <-->
      ("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}}} '"e")


define unfold_es__causl : "es-causl"[]{'"es";'"e";'"e'"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"es"}}}}}}}}}}}}}}}}} '"e") '"e'")


define unfold_es__locl : "es-locl"[]{'"es";'"e";'"e'"} <-->
      "and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"es-loc"[]{'"es";'"e'"}};"es-causl"[]{'"es";'"e";'"e'"}}


define unfold_es__le : "es-le"[]{'"es";'"e";'"e'"} <-->
      "or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}}


define unfold_es__bless : "es-bless"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


define unfold_es__ble : "es-ble"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


define unfold_es__bc : "es-bc"[level:l]{'"es";'"e";'"e'"} <-->
      "decide"[]{((("termof"[]{} '"es") '"e'") '"e");"x"."btrue"[]{};"x"."bfalse"[]{}}


define unfold_es__ek : "es-ek"[]{'"es";'"k";"e", "v".'"P"['"e";'"v"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};'"P"['"e";"es-val"[]{'"es";'"e"}]}}


define unfold_es__er : "es-er"[]{'"es";'"l";'"tg";"e", "v".'"P"['"e";'"v"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"and"[]{"equal"[]{"Id"[]{};"es-tag"[]{'"es";'"e"};'"tg"};'"P"['"e";"es-val"[]{'"es";'"e"}]}}}}


define unfold_es__mtag : "es-mtag"[]{'"es";'"m"} <-->
      "mtag"[]{'"m"}


define unfold_es__mval : "es-mval"[]{'"es";'"m"} <-->
      "mval"[]{'"m"}


define unfold_es__before : "es-before"[]{'"es";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"es-before"."lambda"[]{"e"."ifthenelse"[]{"es-first"[]{'"es";'"e"};"nil"[]{};"append"[]{('"es-before" "es-pred"[]{'"es";'"e"});"cons"[]{"es-pred"[]{'"es";'"e"};"nil"[]{}}}}}}) '"e")


define unfold_es__interval : "es-interval"[level:l]{'"es";'"e";'"e'"} <-->
      "filter"[]{"lambda"[]{"ev"."es-ble"[level:l]{'"es";'"e";'"ev"}};"append"[]{"es-before"[]{'"es";'"e'"};"cons"[]{'"e'";"nil"[]{}}}}


define unfold_es__haslnk : "es-haslnk"[]{'"es";'"l";'"e"} <-->
      "band"[]{"es-isrcv"[]{'"es";'"e"};"eq_lnk"[]{"es-lnk"[]{'"es";'"e"};'"l"}}


define unfold_es__rcvs : "es-rcvs"[]{'"es";'"l";'"e'"} <-->
      "filter"[]{"lambda"[]{"e"."es-haslnk"[]{'"es";'"l";'"e"}};"es-before"[]{'"es";'"e'"}}


define unfold_es__snds : "es-snds"[]{'"es";'"l";'"e"} <-->
      "concat"[]{"map"[]{"lambda"[]{"e"."es-sends"[]{'"es";'"l";'"e"}};"es-before"[]{'"es";'"e"}}}


define unfold_es__snds__index : "es-snds-index"[]{'"es";'"l";'"e";'"n"} <-->
      "append"[]{"es-snds"[]{'"es";'"l";'"e"};"firstn"[]{'"n";"es-sends"[]{'"es";'"l";'"e"}}}


define unfold_es__msg : "es-msg"[]{'"es";'"e"} <-->
      "msg"[]{"es-lnk"[]{'"es";'"e"};"es-tag"[]{'"es";'"e"};"es-val"[]{'"es";'"e"}}


define unfold_es__msgs : "es-msgs"[]{'"the_es";'"l";'"e'"} <-->
      "map"[]{"lambda"[]{"e"."es-msg"[]{'"the_es";'"e"}};"es-rcvs"[]{'"the_es";'"l";'"e'"}}


define unfold_es__tg__sends : "es-tg-sends"[]{'"es";'"l";'"tg";'"e"} <-->
      "filter"[]{"lambda"[]{"m"."eq_id"[]{"es-mtag"[]{'"es";'"m"};'"tg"}};"es-sends"[]{'"es";'"l";'"e"}}


define unfold_alle__at : "alle-at"[]{'"es";'"i";"e".'"P"['"e"]} <-->
      "all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};'"P"['"e"]}}


define unfold_alle__at1 : "alle-at1"[]{'"es";'"i";'"x";"x".'"P"['"x"]} <-->
      "alle-at"[]{'"es";'"i";"e".'"P"["es-when"[]{'"es";'"x";'"e"}]}


define unfold_alle__at2 : "alle-at2"[]{'"es";'"i";'"x1";'"x2";"x1", "x2".'"P"['"x1";'"x2"]} <-->
      "alle-at"[]{'"es";'"i";"e".'"P"["es-when"[]{'"es";'"x1";'"e"};"es-when"[]{'"es";'"x2";'"e"}]}


define unfold_existse__at : "existse-at"[]{'"es";'"i";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};'"P"['"e"]}}


define unfold_existse__le : "existse-le"[]{'"es";'"e'";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"es-le"[]{'"es";'"e";'"e'"};'"P"['"e"]}}


define unfold_alle__ge : "alle-ge"[]{'"es";'"e";"e'".'"P"['"e'"]} <-->
      "all"[]{"es-E"[]{'"es"};"e'"."implies"[]{"es-le"[]{'"es";'"e";'"e'"};'"P"['"e'"]}}


define unfold_alle__rcv : "alle-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} <-->
      "all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};'"P"['"e"]}}


define unfold_existse__rcv : "existse-rcv"[]{'"es";'"l";'"tg";"e".'"P"['"e"]} <-->
      "exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};'"P"['"e"]}}


define unfold_es__state : "es-state"[]{'"es";'"i"} <-->
      "fun"[]{"Id"[]{};"x"."es-vartype"[]{'"es";'"i";'"x"}}


define unfold_es__state__ap : "es-state-ap"[]{'"s";'"x"} <-->
      ('"s" '"x")


define unfold_es__state__when : "es-state-when"[]{'"es";'"e"} <-->
      "lambda"[]{"x"."es-when"[]{'"es";'"x";'"e"}}


define unfold_es__state__after : "es-state-after"[]{'"es";'"e"} <-->
      "lambda"[]{"x"."es-after"[]{'"es";'"x";'"e"}}


define unfold_es__stable : "es-stable"[]{'"es";'"i";"state".'"P"['"state"]} <-->
      "alle-at"[]{'"es";'"i";"e"."implies"[]{'"P"["es-state-when"[]{'"es";'"e"}];'"P"["es-state-after"[]{'"es";'"e"}]}}


define unfold_es__frame : "es-frame"[]{'"es";'"i";'"L";'"x";'"T"} <-->
      "cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."implies"[]{"not"[]{"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}


define unfold_es__responsive : "es-responsive"[]{'"es";'"l1";'"tg1";'"l2";'"tg2"} <-->
      "and"[]{"alle-rcv"[]{'"es";'"l1";'"tg1";"e"."existse-rcv"[]{'"es";'"l2";'"tg2";"e'"."and"[]{"es-le"[]{'"es";'"e";"es-sender"[]{'"es";'"e'"}};"and"[]{"alle-rcv"[]{'"es";'"l1";'"tg1";"e2"."implies"[]{"es-locl"[]{'"es";'"e";'"e2"};"es-locl"[]{'"es";"es-sender"[]{'"es";'"e'"};'"e2"}}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e''"."implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}}}}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e'"."existse-rcv"[]{'"es";'"l1";'"tg1";"e"."and"[]{"es-le"[]{'"es";'"e";"es-sender"[]{'"es";'"e'"}};"alle-rcv"[]{'"es";'"l2";'"tg2";"e''"."implies"[]{"es-locl"[]{'"es";"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"es-locl"[]{'"es";"es-sender"[]{'"es";'"e''"};'"e"}}}}}}}


define unfold_es__only__sender : "es-only-sender"[]{'"es";'"k";'"B";'"l";'"tg";'"T";"s", "v".'"f"['"s";'"v"]} <-->
      "and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e'"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";"es-sender"[]{'"es";'"e'"}};'"k"};"cand"[]{"subtype"[]{"es-valtype"[]{'"es";"es-sender"[]{'"es";'"e'"}};'"B"};"cand"[]{"subtype"[]{"es-valtype"[]{'"es";'"e'"};'"T"};"and"[]{"equal"[]{'"T";"es-val"[]{'"es";'"e'"};'"f"["es-state-when"[]{'"es";"es-sender"[]{'"es";'"e'"}};"es-val"[]{'"es";"es-sender"[]{'"es";'"e'"}}]};"all"[]{"es-E"[]{'"es"};"e''"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e''"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};"es-sender"[]{'"es";'"e'"}};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}}}}}}}}}


