extends Ma_general


define unfold_Id : "Id"[]{} <-->
      "prod"[]{"atom"[]{};""."nat"[]{}}


define unfold_mkid : "mkid"[]{'"x";'"n"} <-->
      "pair"[]{'"x";'"n"}


define unfold_IdLnk : "IdLnk"[]{} <-->
      "prod"[]{"Id"[]{};""."prod"[]{"Id"[]{};""."nat"[]{}}}


define unfold_lnk__inv : "lnk-inv"[]{'"l"} <-->
      "pair"[]{"fst"[]{"snd"[]{'"l"}};"pair"[]{"fst"[]{'"l"};"snd"[]{"snd"[]{'"l"}}}}


define unfold_Msg : "Msg"[]{'"M"} <-->
      "prod"[]{"IdLnk"[]{};"l"."prod"[]{"Id"[]{};"t".(('"M" '"l") '"t")}}


define unfold_msg : "msg"[]{'"l";'"t";'"v"} <-->
      "pair"[]{'"l";"pair"[]{'"t";'"v"}}


define unfold_mlnk : "mlnk"[]{'"m"} <-->
      "fst"[]{'"m"}


define unfold_mtag : "mtag"[]{'"m"} <-->
      "fst"[]{"snd"[]{'"m"}}


define unfold_mval : "mval"[]{'"m"} <-->
      "snd"[]{"snd"[]{'"m"}}


define unfold_haslink : "haslink"[]{'"l";'"m"} <-->
      "equal"[]{"IdLnk"[]{};"mlnk"[]{'"m"};'"l"}


define unfold_Msg_sub : "Msg_sub"[]{'"l";'"M"} <-->
      "set"[]{"Msg"[]{'"M"};"m"."haslink"[]{'"l";'"m"}}


define unfold_Knd : "Knd"[]{} <-->
      "union"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"Id"[]{}}


define unfold_isrcv : "isrcv"[]{'"k"} <-->
      "is_inl"[]{'"k"}


define unfold_islocal : "islocal"[]{'"k"} <-->
      "bnot"[]{"is_inl"[]{'"k"}}


define unfold_rcv : "rcv"[]{'"l";'"tg"} <-->
      "inl"[]{"pair"[]{'"l";'"tg"}}


define unfold_locl : "locl"[]{'"a"} <-->
      "inr"[]{'"a"}


define unfold_lnk : "lnk"[]{'"k"} <-->
      "fst"[]{"outl"[]{'"k"}}


define unfold_tagof : "tagof"[]{'"k"} <-->
      "snd"[]{"outl"[]{'"k"}}


define unfold_actof : "actof"[]{'"k"} <-->
      "outr"[]{'"k"}


define unfold_kindcase : "kindcase"[]{'"k";"a".'"f"['"a"];"l", "t".'"g"['"l";'"t"]} <-->
      "ifthenelse"[]{"islocal"[]{'"k"};'"f"["actof"[]{'"k"}];'"g"["lnk"[]{'"k"};"tagof"[]{'"k"}]}


define unfold_kind__rename : "kind-rename"[]{'"ra";'"rt";'"k"} <-->
      "kindcase"[]{'"k";"a"."locl"[]{('"ra" '"a")};"l", "tg"."rcv"[]{'"l";('"rt" '"tg")}}


define unfold_msg__rename : "msg-rename"[]{'"rtinv";'"m"} <-->
      "pair"[]{"fst"[]{'"m"};"pair"[]{"outl"[]{('"rtinv" "fst"[]{"snd"[]{'"m"}})};"snd"[]{"snd"[]{'"m"}}}}


define unfold_lsrc : "lsrc"[]{'"l"} <-->
      "fst"[]{'"l"}


define unfold_ldst : "ldst"[]{'"l"} <-->
      "fst"[]{"snd"[]{'"l"}}


define unfold_lpath : "lpath"[]{'"p"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"p"};"number"[1:n]{}}};"i"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{"select"[]{'"i";'"p"}};"lsrc"[]{"select"[]{"add"[]{'"i";"number"[1:n]{}};'"p"}}};"not"[]{"equal"[]{"IdLnk"[]{};"select"[]{"add"[]{'"i";"number"[1:n]{}};'"p"};"lnk-inv"[]{"select"[]{'"i";'"p"}}}}}}


define unfold_lconnects : "lconnects"[]{'"p";'"i";'"j"} <-->
      "and"[]{"lpath"[]{'"p"};"and"[]{"implies"[]{"equal"[]{"int"[]{};"length"[]{'"p"};"number"[0:n]{}};"equal"[]{"Id"[]{};'"i";'"j"}};"implies"[]{"not"[]{"equal"[]{"int"[]{};"length"[]{'"p"};"number"[0:n]{}}};"and"[]{"equal"[]{"Id"[]{};'"i";"lsrc"[]{"hd"[]{'"p"}}};"equal"[]{"Id"[]{};'"j";"ldst"[]{"last"[]{'"p"}}}}}}}


