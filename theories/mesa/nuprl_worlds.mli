extends Ma_finite__partial__functions


define unfold_action : "action"[]{'"dec"} <-->
      "union"[]{"unit"[]{};"prod"[]{"Knd"[]{};"k".('"dec" '"k")}}


define unfold_null__action : "null-action"[]{} <-->
      "inl"[]{"it"[]{}}


define unfold_doact : "doact"[]{'"k";'"v"} <-->
      "inr"[]{"pair"[]{'"k";'"v"}}


define unfold_w__action__dec : "w-action-dec"[]{'"TA";'"M";'"i"} <-->
      "lambda"[]{"k"."kindcase"[]{'"k";"a".(('"TA" '"i") '"a");"l", "tg"."ifthenelse"[]{"eq_id"[]{"ldst"[]{'"l"};'"i"};(('"M" '"l") '"tg");"void"[]{}}}}


define unfold_world : "world"[level:l]{} <-->
      "prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"TA"."prod"[]{"fun"[]{"IdLnk"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"M"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."fun"[]{"Id"[]{};"x".(('"T" '"i") '"x")}}};"s"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."action"[]{"w-action-dec"[]{'"TA";'"M";'"i"}}}};"a"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."list"[]{"set"[]{"Msg"[]{'"M"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}}}};"m"."top"[]{}}}}}}}


define unfold_w__T : "w-T"[]{'"w"} <-->
      "fst"[]{'"w"}


define unfold_w__TA : "w-TA"[]{'"w"} <-->
      "fst"[]{"snd"[]{'"w"}}


define unfold_w__M : "w-M"[]{'"w"} <-->
      "fst"[]{"snd"[]{"snd"[]{'"w"}}}


define unfold_w__vartype : "w-vartype"[]{'"w";'"i";'"x"} <-->
      (("w-T"[]{'"w"} '"i") '"x")


define unfold_w__action : "w-action"[]{'"w";'"i"} <-->
      "action"[]{"w-action-dec"[]{"w-TA"[]{'"w"};"w-M"[]{'"w"};'"i"}}


define unfold_w__isnull : "w-isnull"[]{'"w";'"a"} <-->
      "is_inl"[]{'"a"}


define unfold_w__kind : "w-kind"[]{'"w";'"a"} <-->
      "fst"[]{"outr"[]{'"a"}}


define unfold_w__valtype : "w-valtype"[]{'"w";'"i";'"a"} <-->
      "kindcase"[]{"w-kind"[]{'"w";'"a"};"a".(("w-TA"[]{'"w"} '"i") '"a");"l", "tg".(("w-M"[]{'"w"} '"l") '"tg")}


define unfold_w__val : "w-val"[]{'"w";'"a"} <-->
      "snd"[]{"outr"[]{'"a"}}


define unfold_w__isrcvl : "w-isrcvl"[]{'"w";'"l";'"a"} <-->
      "band"[]{"bnot"[]{"w-isnull"[]{'"w";'"a"}};"band"[]{"isrcv"[]{"w-kind"[]{'"w";'"a"}};"eq_lnk"[]{"lnk"[]{"w-kind"[]{'"w";'"a"}};'"l"}}}


define unfold_w__Msg : "w-Msg"[]{'"w"} <-->
      "Msg"[]{"w-M"[]{'"w"}}


define unfold_w__Msg__from : "w-Msg-from"[]{'"w";'"i"} <-->
      "set"[]{"w-Msg"[]{'"w"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}


define unfold_w__s : "w-s"[]{'"w";'"i";'"t";'"x"} <-->
      ((("fst"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}} '"i") '"t") '"x")


define unfold_w__a : "w-a"[]{'"w";'"i";'"t"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}}} '"i") '"t")


define unfold_w__m : "w-m"[]{'"w";'"i";'"t"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}}}} '"i") '"t")


define unfold_w__onlnk : "w-onlnk"[]{'"l";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


define unfold_w__withlnk : "w-withlnk"[]{'"l";'"mss"} <-->
      "mapfilter"[]{"lambda"[]{"ms"."snd"[]{'"ms"}};"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


define unfold_w__tagged : "w-tagged"[]{'"tg";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_id"[]{"mtag"[]{'"ms"};'"tg"}};'"mss"}


define unfold_w__ml : "w-ml"[]{'"w";'"l";'"t"} <-->
      "w-onlnk"[]{'"l";"w-m"[]{'"w";"lsrc"[]{'"l"};'"t"}}


define unfold_w__snds : "w-snds"[]{'"w";'"l";'"t"} <-->
      "concat"[]{"map"[]{"lambda"[]{"t1"."w-ml"[]{'"w";'"l";'"t1"}};"upto"[]{'"t"}}}


define unfold_w__rcvs : "w-rcvs"[]{'"w";'"l";'"t"} <-->
      "filter"[]{"lambda"[]{"a"."w-isrcvl"[]{'"w";'"l";'"a"}};"map"[]{"lambda"[]{"t1"."w-a"[]{'"w";"ldst"[]{'"l"};'"t1"}};"upto"[]{'"t"}}}


define unfold_w__queue : "w-queue"[]{'"w";'"l";'"t"} <-->
      "nth_tl"[]{"length"[]{"w-rcvs"[]{'"w";'"l";'"t"}};"w-snds"[]{'"w";'"l";'"t"}}


define unfold_w__msg : "w-msg"[]{'"w";'"a"} <-->
      "msg"[]{"lnk"[]{"w-kind"[]{'"w";'"a"}};"tagof"[]{"w-kind"[]{'"w";'"a"}};"w-val"[]{'"w";'"a"}}


define unfold_fair__fifo : "fair-fifo"[]{'"w"} <-->
      "and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."all"[]{"IdLnk"[]{};"l"."implies"[]{"not"[]{"equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-onlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}};"nil"[]{}}}}}};"and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."implies"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}};"and"[]{"all"[]{"Id"[]{};"x"."equal"[]{"w-vartype"[]{'"w";'"i";'"x"};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"};"w-s"[]{'"w";'"i";'"t";'"x"}}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-m"[]{'"w";'"i";'"t"};"nil"[]{}}}}}};"and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."all"[]{"IdLnk"[]{};"l"."implies"[]{"assert"[]{"w-isrcvl"[]{'"w";'"l";"w-a"[]{'"w";'"i";'"t"}}};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"cand"[]{"ge"[]{"length"[]{"w-queue"[]{'"w";'"l";'"t"}};"number"[1:n]{}};"equal"[]{"w-Msg"[]{'"w"};"hd"[]{"w-queue"[]{'"w";'"l";'"t"}};"w-msg"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}}}}}}};"all"[]{"IdLnk"[]{};"l"."all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"or"[]{"assert"[]{"w-isrcvl"[]{'"w";'"l";"w-a"[]{'"w";"ldst"[]{'"l"};'"t'"}}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-queue"[]{'"w";'"l";'"t'"};"nil"[]{}}}}}}}}}}


define unfold_w__E : "w-E"[]{'"w"} <-->
      "set"[]{"prod"[]{"Id"[]{};""."nat"[]{}};"p"."not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"fst"[]{'"p"};"snd"[]{'"p"}}}}}}


define unfold_w__eq__E : "w-eq-E"[]{'"w";'"p";'"q"} <-->
      "band"[]{"eq_id"[]{"fst"[]{'"p"};"fst"[]{'"q"}};"beq_int"[]{"snd"[]{'"p"};"snd"[]{'"q"}}}


define unfold_w__loc : "w-loc"[]{'"w";'"e"} <-->
      "fst"[]{'"e"}


define unfold_w__act : "w-act"[]{'"w";'"e"} <-->
      "w-a"[]{'"w";"fst"[]{'"e"};"snd"[]{'"e"}}


define unfold_w__ekind : "w-ekind"[]{'"w";'"e"} <-->
      "w-kind"[]{'"w";"w-act"[]{'"w";'"e"}}


define unfold_w__V : "w-V"[]{'"w";'"i";'"k"} <-->
      "kindcase"[]{'"k";"a".(("fst"[]{"snd"[]{'"w"}} '"i") '"a");"l", "tg".(("fst"[]{"snd"[]{"snd"[]{'"w"}}} '"l") '"tg")}


define unfold_w__eval : "w-eval"[]{'"w";'"e"} <-->
      "w-val"[]{'"w";"w-act"[]{'"w";'"e"}}


define unfold_w__time : "w-time"[]{'"w";'"e"} <-->
      "snd"[]{'"e"}


define unfold_w__when : "w-when"[]{'"w";'"x";'"e"} <-->
      "w-s"[]{'"w";"fst"[]{'"e"};"snd"[]{'"e"};'"x"}


define unfold_w__after : "w-after"[]{'"w";'"x";'"e"} <-->
      "w-s"[]{'"w";"fst"[]{'"e"};"add"[]{"snd"[]{'"e"};"number"[1:n]{}};'"x"}


define unfold_w__initially : "w-initially"[]{'"w";'"x";'"i"} <-->
      "w-s"[]{'"w";'"i";"number"[0:n]{};'"x"}


define unfold_w__first : "w-first"[]{'"w";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"w-first"."lambda"[]{"e"."ifthenelse"[]{"beq_int"[]{"w-time"[]{'"w";'"e"};"number"[0:n]{}};"btrue"[]{};"ifthenelse"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}};('"w-first" "pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}});"bfalse"[]{}}}}}) '"e")


define unfold_w__pred : "w-pred"[]{'"w";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"w-pred"."lambda"[]{"e"."ifthenelse"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}};('"w-pred" "pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}});"pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}}}}) '"e")


define unfold_w__locl : "w-locl"[]{'"w";'"e";'"e'"} <-->
      "and"[]{"equal"[]{"Id"[]{};"w-loc"[]{'"w";'"e"};"w-loc"[]{'"w";'"e'"}};"lt"[]{"w-time"[]{'"w";'"e"};"w-time"[]{'"w";'"e'"}}}


define unfold_w__sends : "w-sends"[]{'"w";'"l";'"e"} <-->
      "w-onlnk"[]{'"l";"w-m"[]{'"w";"w-loc"[]{'"w";'"e"};"w-time"[]{'"w";'"e"}}}


define unfold_w__match : "w-match"[]{'"w";'"l";'"t";'"t'"} <-->
      "band"[]{"le_bool"[]{"length"[]{"w-snds"[]{'"w";'"l";'"t"}};"length"[]{"w-rcvs"[]{'"w";'"l";'"t'"}}};"lt_bool"[]{"length"[]{"w-rcvs"[]{'"w";'"l";'"t'"}};"add"[]{"length"[]{"w-snds"[]{'"w";'"l";'"t"}};"length"[]{"w-onlnk"[]{'"l";"w-m"[]{'"w";"lsrc"[]{'"l"};'"t"}}}}}}


define unfold_w__sender : "w-sender"[]{'"w";'"e"} <-->
      "pair"[]{"lsrc"[]{"lnk"[]{"w-ekind"[]{'"w";'"e"}}};"mu"[]{"lambda"[]{"t"."w-match"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};'"t";"w-time"[]{'"w";'"e"}}}}}


define unfold_w__index : "w-index"[]{'"w";'"e"} <-->
      "sub"[]{"length"[]{"w-rcvs"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};"w-time"[]{'"w";'"e"}}};"length"[]{"w-snds"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};"w-time"[]{'"w";"w-sender"[]{'"w";'"e"}}}}}


define unfold_w__causl : "w-causl"[]{'"w";'"e";'"e'"} <-->
      "infix_ap"[]{"rel_plus"[]{"w-E"[]{'"w"};"lambda"[]{"e"."lambda"[]{"e'"."or"[]{"w-locl"[]{'"w";'"e";'"e'"};"cand"[]{"assert"[]{"isrcv"[]{"w-ekind"[]{'"w";'"e'"}}};"equal"[]{"w-E"[]{'"w"};'"e";"w-sender"[]{'"w";'"e'"}}}}}}};'"e";'"e'"}


define unfold_w__es : "w-es"[level:l]{'"the_w";'"p"} <-->
      "pair"[]{"w-E"[]{'"the_w"};"pair"[]{"product-deq"[]{"Id"[]{};"nat"[]{};"id-deq"[]{};"nat-deq"[]{}};"pair"[]{"lambda"[]{"i"."lambda"[]{"x"."w-vartype"[]{'"the_w";'"i";'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."w-V"[]{'"the_w";'"i";"locl"[]{'"a"}}}};"pair"[]{"w-M"[]{'"the_w"};"pair"[]{"it"[]{};"pair"[]{"lambda"[]{"e"."w-loc"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-ekind"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-eval"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"x"."lambda"[]{"e"."w-when"[]{'"the_w";'"x";'"e"}}};"pair"[]{"lambda"[]{"x"."lambda"[]{"e"."w-after"[]{'"the_w";'"x";'"e"}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"e"."w-sends"[]{'"the_w";'"l";'"e"}}};"pair"[]{"lambda"[]{"e"."w-sender"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-index"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-first"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-pred"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."w-causl"[]{'"the_w";'"e";'"e'"}}};"pair"[]{(("termof"[]{} '"the_w") '"p");"it"[]{}}}}}}}}}}}}}}}}}}}


define unfold_action__rename : "action-rename"[]{'"rainv";'"rtinv";'"a"} <-->
      "decide"[]{'"a";"x"."inl"[]{'"x"};"p"."kindcase"[]{"fst"[]{'"p"};"a"."decide"[]{('"rainv" '"a");"b"."inr"[]{"pair"[]{"locl"[]{'"b"};"snd"[]{'"p"}}};"b"."inl"[]{"it"[]{}}};"l", "tg"."decide"[]{('"rtinv" '"tg");"t"."inr"[]{"pair"[]{"rcv"[]{'"l";'"t"};"snd"[]{'"p"}}};"b"."inl"[]{"it"[]{}}}}}


define unfold_world__rename : "world-rename"[]{'"rx";'"ra";'"rt";'"rainv";'"rtinv";'"w"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."w-vartype"[]{'"w";'"i";('"rx" '"x")}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a".(("fst"[]{"snd"[]{'"w"}} '"i") ('"ra" '"a"))}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg".(("w-M"[]{'"w"} '"l") ('"rt" '"tg"))}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";('"rx" '"x")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."action-rename"[]{'"rainv";'"rtinv";"w-a"[]{'"w";'"i";'"t"}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."mapfilter"[]{"lambda"[]{"m"."msg-rename"[]{'"rtinv";'"m"}};"lambda"[]{"m"."is_inl"[]{('"rtinv" "mtag"[]{'"m"})}};"w-m"[]{'"w";'"i";'"t"}}}};"it"[]{}}}}}}}


