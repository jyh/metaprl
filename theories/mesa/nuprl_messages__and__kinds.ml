extends Ma_general

open Dtactic


define unfold_Id : "Id"[]{} <-->
      "prod"[]{"atom"[]{};""."nat"[]{}}


interactive nuprl_Id_wf {| intro[] |}   :
   sequent { <H> >- ("Id"[]{} in "univ"[level:l]{}) }

interactive nuprl_Id_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"Id"[]{}} }

interactive nuprl_Id_sq   :
   sequent { <H> >- "sq_type"[]{"Id"[]{}} }

define unfold_mkid : "mkid"[]{'"x";'"n"} <-->
      "pair"[]{'"x";'"n"}


interactive nuprl_mkid_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- ("mkid"[]{'"x";'"n"} in "Id"[]{}) }

define unfold_IdLnk : "IdLnk"[]{} <-->
      "prod"[]{"Id"[]{};""."prod"[]{"Id"[]{};""."nat"[]{}}}


interactive nuprl_IdLnk_wf {| intro[] |}   :
   sequent { <H> >- ("IdLnk"[]{} in "univ"[level:l]{}) }

interactive nuprl_IdLnk_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"IdLnk"[]{}} }

interactive nuprl_IdLnk_sq   :
   sequent { <H> >- "sq_type"[]{"IdLnk"[]{}} }

define unfold_lnk__inv : "lnk-inv"[]{'"l"} <-->
      "pair"[]{"fst"[]{"snd"[]{'"l"}};"pair"[]{"fst"[]{'"l"};"snd"[]{"snd"[]{'"l"}}}}


interactive nuprl_lnk__inv_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("lnk-inv"[]{'"l"} in "IdLnk"[]{}) }

interactive nuprl_lnk__inv__inv   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "equal"[]{"IdLnk"[]{};"lnk-inv"[]{"lnk-inv"[]{'"l"}};'"l"} }

interactive nuprl_lnk__inv__one__one   :
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"l2" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"IdLnk"[]{};"lnk-inv"[]{'"l1"};"lnk-inv"[]{'"l2"}};"equal"[]{"IdLnk"[]{};'"l1";'"l2"}} }

define unfold_Msg : "Msg"[]{'"M"} <-->
      "prod"[]{"IdLnk"[]{};"l"."prod"[]{"Id"[]{};"t".(('"M" '"l") '"t")}}


interactive nuprl_Msg_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("Msg"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_Msg_wf_type {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   sequent { <H> >- "type"{"Msg"[]{'"M"}} }

define unfold_msg : "msg"[]{'"l";'"t";'"v"} <-->
      "pair"[]{'"l";"pair"[]{'"t";'"v"}}


interactive nuprl_msg_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"v" in (('"M" '"l") '"t") }  -->
   sequent { <H> >- ("msg"[]{'"l";'"t";'"v"} in "Msg"[]{'"M"}) }

define unfold_mlnk : "mlnk"[]{'"m"} <-->
      "fst"[]{'"m"}


interactive nuprl_mlnk_wf {| intro[] |}  '"M"  :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"m" in "Msg"[]{'"M"} }  -->
   sequent { <H> >- ("mlnk"[]{'"m"} in "IdLnk"[]{}) }

define unfold_mtag : "mtag"[]{'"m"} <-->
      "fst"[]{"snd"[]{'"m"}}


interactive nuprl_mtag_wf {| intro[] |}  '"M"  :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"m" in "Msg"[]{'"M"} }  -->
   sequent { <H> >- ("mtag"[]{'"m"} in "Id"[]{}) }

define unfold_mval : "mval"[]{'"m"} <-->
      "snd"[]{"snd"[]{'"m"}}


interactive nuprl_mval_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"m" in "Msg"[]{'"M"} }  -->
   sequent { <H> >- ("mval"[]{'"m"} in (('"M" "mlnk"[]{'"m"}) "mtag"[]{'"m"})) }

define unfold_haslink : "haslink"[]{'"l";'"m"} <-->
      "equal"[]{"IdLnk"[]{};"mlnk"[]{'"m"};'"l"}


interactive nuprl_haslink_wf {| intro[] |}  '"M"  :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "Msg"[]{'"M"} }  -->
   sequent { <H> >- ("haslink"[]{'"l";'"m"} in "univ"[level:l]{}) }

define unfold_Msg_sub : "Msg_sub"[]{'"l";'"M"} <-->
      "set"[]{"Msg"[]{'"M"};"m"."haslink"[]{'"l";'"m"}}


interactive nuprl_Msg_sub_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("Msg_sub"[]{'"l";'"M"} in "univ"[level:l]{}) }

interactive nuprl_Msg_sub_wf_type {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "type"{"Msg_sub"[]{'"l";'"M"}} }

define unfold_Knd : "Knd"[]{} <-->
      "union"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"Id"[]{}}


interactive nuprl_Knd_wf {| intro[] |}   :
   sequent { <H> >- ("Knd"[]{} in "univ"[level:l]{}) }

interactive nuprl_Knd_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"Knd"[]{}} }

interactive nuprl_Knd_sq   :
   sequent { <H> >- "sq_type"[]{"Knd"[]{}} }

define unfold_isrcv : "isrcv"[]{'"k"} <-->
      "is_inl"[]{'"k"}


interactive nuprl_isrcv_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("isrcv"[]{'"k"} in "bool"[]{}) }

define unfold_islocal : "islocal"[]{'"k"} <-->
      "bnot"[]{"is_inl"[]{'"k"}}


interactive nuprl_islocal_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("islocal"[]{'"k"} in "bool"[]{}) }

interactive_rw nuprl_islocal__not__isrcv   :
   ('"k" in "Knd"[]{}) -->
   "islocal"[]{'"k"} <--> "bnot"[]{"isrcv"[]{'"k"}}

define unfold_rcv : "rcv"[]{'"l";'"tg"} <-->
      "inl"[]{"pair"[]{'"l";'"tg"}}


interactive nuprl_rcv_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("rcv"[]{'"l";'"tg"} in "Knd"[]{}) }

define unfold_locl : "locl"[]{'"a"} <-->
      "inr"[]{'"a"}


interactive nuprl_locl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- ("locl"[]{'"a"} in "Knd"[]{}) }

interactive nuprl_locl_one_one   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"locl"[]{'"a"};"locl"[]{'"b"}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};'"a";'"b"} }

interactive nuprl_rcv_one_one   :
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"l2" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg2" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"rcv"[]{'"l1";'"tg1"};"rcv"[]{'"l2";'"tg2"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"IdLnk"[]{};'"l1";'"l2"};"equal"[]{"Id"[]{};'"tg1";'"tg2"}}} }

interactive nuprl_not_rcv_locl  '"a" '"tg" '"l"  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};"locl"[]{'"a"}} }  -->
   sequent { <H> >- "false"[]{} }

interactive nuprl_not_locl_rcv  '"tg" '"l" '"a"  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};"locl"[]{'"a"};"rcv"[]{'"l";'"tg"}} }  -->
   sequent { <H> >- "false"[]{} }

define unfold_lnk : "lnk"[]{'"k"} <-->
      "fst"[]{"outl"[]{'"k"}}


interactive nuprl_lnk_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{'"k"}} }  -->
   sequent { <H> >- ("lnk"[]{'"k"} in "IdLnk"[]{}) }

define unfold_tagof : "tagof"[]{'"k"} <-->
      "snd"[]{"outl"[]{'"k"}}


interactive nuprl_tagof_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{'"k"}} }  -->
   sequent { <H> >- ("tagof"[]{'"k"} in "Id"[]{}) }

define unfold_actof : "actof"[]{'"k"} <-->
      "outr"[]{'"k"}


interactive nuprl_actof_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "assert"[]{"islocal"[]{'"k"}} }  -->
   sequent { <H> >- ("actof"[]{'"k"} in "Id"[]{}) }

interactive nuprl_local_or_rcv   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "or"[]{"assert"[]{"islocal"[]{'"k"}};"assert"[]{"isrcv"[]{'"k"}}} }

define unfold_kindcase : "kindcase"[]{'"k";"a".'"f"['"a"];"l", "t".'"g"['"l";'"t"]} <-->
      "ifthenelse"[]{"islocal"[]{'"k"};'"f"["actof"[]{'"k"}];'"g"["lnk"[]{'"k"};"tagof"[]{'"k"}]}


interactive nuprl_kindcase_wf {| intro[] |}  '"B" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x".'"f"['"x"]} '"k"  :
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"f"['"x"] in '"B" }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"g"['"x";'"x1"] in '"B" }  -->
   sequent { <H> >- ("kindcase"[]{'"k";"a".'"f"['"a"];"l", "t".'"g"['"l";'"t"]} in '"B") }

interactive_rw nuprl_kindcase__locl  '"k" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   ('"k" in "Knd"[]{}) -->
   "assert"[]{"islocal"[]{'"k"}} -->
   "kindcase"[]{'"k";"a".'"f"['"a"];"l", "t".'"g"['"l";'"t"]} <--> '"f"["actof"[]{'"k"}]

interactive_rw nuprl_kindcase__rcv  '"k" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   ('"k" in "Knd"[]{}) -->
   "not"[]{"assert"[]{"islocal"[]{'"k"}}} -->
   "kindcase"[]{'"k";"a".'"f"['"a"];"l", "t".'"g"['"l";'"t"]} <--> '"g"["lnk"[]{'"k"};"tagof"[]{'"k"}]

define unfold_kind__rename : "kind-rename"[]{'"ra";'"rt";'"k"} <-->
      "kindcase"[]{'"k";"a"."locl"[]{('"ra" '"a")};"l", "tg"."rcv"[]{'"l";('"rt" '"tg")}}


interactive nuprl_kind__rename_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("kind-rename"[]{'"ra";'"rt";'"k"} in "Knd"[]{}) }

interactive nuprl_kind__rename__inj   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"rt"} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"ra"} }  -->
   sequent { <H> >- "inject"[]{"Knd"[]{};"Knd"[]{};"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}}} }

define unfold_msg__rename : "msg-rename"[]{'"rtinv";'"m"} <-->
      "pair"[]{"fst"[]{'"m"};"pair"[]{"outl"[]{('"rtinv" "fst"[]{"snd"[]{'"m"}})};"snd"[]{"snd"[]{'"m"}}}}


interactive nuprl_msg__rename_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rtinv" '"x" in "union"[]{"Id"[]{};"unit"[]{}} }  -->
   sequent { <H> >- "inv-rel"[]{"Id"[]{};"Id"[]{};'"rt";'"rtinv"} }  -->
   [wf] sequent { <H> >- '"m" in "Msg"[]{'"M"} }  -->
   sequent { <H> >- "assert"[]{"is_inl"[]{('"rtinv" "mtag"[]{'"m"})}} }  -->
   sequent { <H> >- ("msg-rename"[]{'"rtinv";'"m"} in "Msg"[]{"lambda"[]{"l"."lambda"[]{"tg".(('"M" '"l") ('"rt" '"tg"))}}}) }

define unfold_lsrc : "lsrc"[]{'"l"} <-->
      "fst"[]{'"l"}


interactive nuprl_lsrc_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("lsrc"[]{'"l"} in "Id"[]{}) }

define unfold_ldst : "ldst"[]{'"l"} <-->
      "fst"[]{"snd"[]{'"l"}}


interactive nuprl_ldst_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("ldst"[]{'"l"} in "Id"[]{}) }

interactive nuprl_lsrc__inv   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"lsrc"[]{"lnk-inv"[]{'"l"}};"ldst"[]{'"l"}} }

interactive nuprl_ldst__inv   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"ldst"[]{"lnk-inv"[]{'"l"}};"lsrc"[]{'"l"}} }

define unfold_lpath : "lpath"[]{'"p"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"p"};"number"[1:n]{}}};"i"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{"select"[]{'"i";'"p"}};"lsrc"[]{"select"[]{"add"[]{'"i";"number"[1:n]{}};'"p"}}};"not"[]{"equal"[]{"IdLnk"[]{};"select"[]{"add"[]{'"i";"number"[1:n]{}};'"p"};"lnk-inv"[]{"select"[]{'"i";'"p"}}}}}}


interactive nuprl_lpath_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"p" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- ("lpath"[]{'"p"} in "univ"[level:l]{}) }

interactive nuprl_lpath_cons   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"p" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "iff"[]{"lpath"[]{"cons"[]{'"l";'"p"}};"and"[]{"lpath"[]{'"p"};"implies"[]{"not"[]{"equal"[]{"int"[]{};"length"[]{'"p"};"number"[0:n]{}}};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};"lsrc"[]{"hd"[]{'"p"}}};"not"[]{"equal"[]{"IdLnk"[]{};"hd"[]{'"p"};"lnk-inv"[]{'"l"}}}}}}} }

define unfold_lconnects : "lconnects"[]{'"p";'"i";'"j"} <-->
      "and"[]{"lpath"[]{'"p"};"and"[]{"implies"[]{"equal"[]{"int"[]{};"length"[]{'"p"};"number"[0:n]{}};"equal"[]{"Id"[]{};'"i";'"j"}};"implies"[]{"not"[]{"equal"[]{"int"[]{};"length"[]{'"p"};"number"[0:n]{}}};"and"[]{"equal"[]{"Id"[]{};'"i";"lsrc"[]{"hd"[]{'"p"}}};"equal"[]{"Id"[]{};'"j";"ldst"[]{"last"[]{'"p"}}}}}}}


interactive nuprl_lconnects_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"p" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   sequent { <H> >- ("lconnects"[]{'"p";'"i";'"j"} in "univ"[level:l]{}) }

interactive nuprl_lpath__members__connected   :
   [wf] sequent { <H> >- '"p" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"p"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"add"[]{'"i";"number"[1:n]{}}} }  -->
   sequent { <H> >- "lpath"[]{'"p"} }  -->
   sequent { <H> >- "lconnects"[]{"l_interval"[]{'"p";'"j";'"i"};"lsrc"[]{"select"[]{'"j";'"p"}};"lsrc"[]{"select"[]{'"i";'"p"}}} }


(**** display forms ****)


dform nuprl_Id_df : except_mode[src] :: "Id"[]{} =
   `"Id"


dform nuprl_mkid_df : except_mode[src] :: "mkid"[]{'"x";'"n"} =
   `"" slot{'"x"} `"_" slot{'"n"} `""

dform nuprl_mkid_df : except_mode[src] :: "mkid"[]{'"x";"number"[0:n]{}} =
   `"" slot{'"x"} `""


dform nuprl_IdLnk_df : except_mode[src] :: "IdLnk"[]{} =
   `"IdLnk"


dform nuprl_lnk__inv_df : except_mode[src] :: "lnk-inv"[]{'"l"} =
   `"lnk-inv(" slot{'"l"} `")"


dform nuprl_Msg_df : except_mode[src] :: "Msg"[]{'"M"} =
   `"Msg(" slot{'"M"} `")"


dform nuprl_msg_df : except_mode[src] :: "msg"[]{'"l";'"t";'"v"} =
   `"msg(" slot{'"l"} `";" slot{'"t"} `";" slot{'"v"} `")"


dform nuprl_mlnk_df : except_mode[src] :: "mlnk"[]{'"m"} =
   `"mlnk(" slot{'"m"} `")"


dform nuprl_mtag_df : except_mode[src] :: "mtag"[]{'"m"} =
   `"mtag(" slot{'"m"} `")"


dform nuprl_mval_df : except_mode[src] :: "mval"[]{'"m"} =
   `"mval(" slot{'"m"} `")"


dform nuprl_haslink_df : except_mode[src] :: "haslink"[]{'"l";'"m"} =
   `"haslink(" slot{'"l"} `";" slot{'"m"} `")"


dform nuprl_Msg_sub_df : except_mode[src] :: "Msg_sub"[]{'"l";'"M"} =
   `"Msg_sub(" slot{'"l"} `";" slot{'"M"} `")"


dform nuprl_Knd_df : except_mode[src] :: "Knd"[]{} =
   `"Knd"


dform nuprl_isrcv_df : except_mode[src] :: "isrcv"[]{'"k"} =
   `"isrcv(" slot{'"k"} `")"


dform nuprl_islocal_df : except_mode[src] :: "islocal"[]{'"k"} =
   `"islocal(" slot{'"k"} `")"


dform nuprl_rcv_df : except_mode[src] :: "rcv"[]{'"l";'"v"} =
   `"rcv(" slot{'"l"} `"," slot{'"v"} `")"


dform nuprl_locl_df : except_mode[src] :: "locl"[]{'"a"} =
   `"locl(" slot{'"a"} `")"


dform nuprl_lnk_df : except_mode[src] :: "lnk"[]{'"k"} =
   `"lnk(" slot{'"k"} `")"


dform nuprl_tagof_df : except_mode[src] :: "tagof"[]{'"k"} =
   `"tag(" slot{'"k"} `")"


dform nuprl_actof_df : except_mode[src] :: "actof"[]{'"k"} =
   `"act(" slot{'"k"} `")"


dform nuprl_kindcase_df : except_mode[src] :: "kindcase"[]{'"k";"a".'"f";"l", "t".'"g"} =
   `"kindcase(" slot{'"k"} `";" slot{'"a"} `"." slot{'"f"} `";" slot{'"l"} `","
    slot{'"t"} `"." slot{'"g"} `")"


dform nuprl_kind__rename_df : except_mode[src] :: "kind-rename"[]{'"ra";'"rt";'"k"} =
   `"kind-rename(" slot{'"ra"} `";" slot{'"rt"} `";" slot{'"k"} `")"


dform nuprl_msg__rename_df : except_mode[src] :: "msg-rename"[]{'"rt";'"m"} =
   `"msg-rename(" slot{'"rt"} `";" slot{'"m"} `")"


dform nuprl_lsrc_df : except_mode[src] :: "lsrc"[]{'"l"} =
   `"source(" slot{'"l"} `")"


dform nuprl_ldst_df : except_mode[src] :: "ldst"[]{'"l"} =
   `"destination(" slot{'"l"} `")"


dform nuprl_lpath_df : except_mode[src] :: "lpath"[]{'"p"} =
   `"lpath(" slot{'"p"} `")"


dform nuprl_lconnects_df : except_mode[src] :: "lconnects"[]{'"p";'"i";'"j"} =
   `"lconnects(" slot{'"p"} `";" slot{'"i"} `";" slot{'"j"} `")"


