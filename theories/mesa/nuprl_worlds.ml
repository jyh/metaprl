extends Ma_finite__partial__functions

open Dtactic


define unfold_action : "action"[]{'"dec"} <-->
      "union"[]{"unit"[]{};"prod"[]{"Knd"[]{};"k".('"dec" '"k")}}


interactive nuprl_action_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Knd"[]{} >- '"dec" '"x" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("action"[]{'"dec"} in "univ"[level:l]{}) }

interactive nuprl_action_wf_type {| intro[] |}   :
   [wf] sequent { <H>;"x": "Knd"[]{} >- "type"{'"dec" '"x" } }  -->
   sequent { <H> >- "type"{"action"[]{'"dec"}} }

define unfold_null__action : "null-action"[]{} <-->
      "inl"[]{"it"[]{}}


interactive nuprl_null__action_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Knd"[]{} >- "type"{'"dec" '"x" } }  -->
   sequent { <H> >- ("null-action"[]{} in "action"[]{'"dec"}) }

define unfold_doact : "doact"[]{'"k";'"v"} <-->
      "inr"[]{"pair"[]{'"k";'"v"}}


interactive nuprl_doact_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Knd"[]{} >- "type"{'"dec" '"x" } }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"v" in ('"dec" '"k") }  -->
   sequent { <H> >- ("doact"[]{'"k";'"v"} in "action"[]{'"dec"}) }

define unfold_w__action__dec : "w-action-dec"[]{'"TA";'"M";'"i"} <-->
      "lambda"[]{"k"."kindcase"[]{'"k";"a".(('"TA" '"i") '"a");"l", "tg"."ifthenelse"[]{"eq_id"[]{"ldst"[]{'"l"};'"i"};(('"M" '"l") '"tg");"void"[]{}}}}


interactive nuprl_w__action__dec_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{};"x1": "Id"[]{} >- '"TA" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- '"M" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("w-action-dec"[]{'"TA";'"M";'"i"} in "fun"[]{"Knd"[]{};""."univ"[level:l]{}}) }

define unfold_world : "world"[level:l]{} <-->
      "prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"T"."prod"[]{"fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"TA"."prod"[]{"fun"[]{"IdLnk"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}};"M"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."fun"[]{"Id"[]{};"x".(('"T" '"i") '"x")}}};"s"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."action"[]{"w-action-dec"[]{'"TA";'"M";'"i"}}}};"a"."prod"[]{"fun"[]{"Id"[]{};"i"."fun"[]{"nat"[]{};""."list"[]{"set"[]{"Msg"[]{'"M"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}}}};"m"."top"[]{}}}}}}}


interactive nuprl_world_wf {| intro[] |}   :
   sequent { <H> >- ("world"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_world_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"world"[level:l]{}} }

define unfold_w__T : "w-T"[]{'"w"} <-->
      "fst"[]{'"w"}


interactive nuprl_w__T_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("w-T"[]{'"w"} in "fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}}) }

define unfold_w__TA : "w-TA"[]{'"w"} <-->
      "fst"[]{"snd"[]{'"w"}}


interactive nuprl_w__TA_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("w-TA"[]{'"w"} in "fun"[]{"Id"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}}) }

define unfold_w__M : "w-M"[]{'"w"} <-->
      "fst"[]{"snd"[]{"snd"[]{'"w"}}}


interactive nuprl_w__M_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("w-M"[]{'"w"} in "fun"[]{"IdLnk"[]{};""."fun"[]{"Id"[]{};""."univ"[level:l]{}}}) }

define unfold_w__vartype : "w-vartype"[]{'"w";'"i";'"x"} <-->
      (("w-T"[]{'"w"} '"i") '"x")


interactive nuprl_w__vartype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("w-vartype"[]{'"the_w";'"i";'"x"} in "univ"[level:l]{}) }

interactive nuprl_w__vartype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"w-vartype"[]{'"the_w";'"i";'"x"}} }

define unfold_w__action : "w-action"[]{'"w";'"i"} <-->
      "action"[]{"w-action-dec"[]{"w-TA"[]{'"w"};"w-M"[]{'"w"};'"i"}}


interactive nuprl_w__action_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("w-action"[]{'"the_w";'"i"} in "univ"[level:l]{}) }

interactive nuprl_w__action_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"w-action"[]{'"the_w";'"i"}} }

define unfold_w__isnull : "w-isnull"[]{'"w";'"a"} <-->
      "is_inl"[]{'"a"}


interactive nuprl_w__isnull_wf {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- ("w-isnull"[]{'"the_w";'"a"} in "bool"[]{}) }

define unfold_w__kind : "w-kind"[]{'"w";'"a"} <-->
      "fst"[]{"outr"[]{'"a"}}


interactive nuprl_w__kind_wf {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}} }  -->
   sequent { <H> >- ("w-kind"[]{'"the_w";'"a"} in "Knd"[]{}) }

define unfold_w__valtype : "w-valtype"[]{'"w";'"i";'"a"} <-->
      "kindcase"[]{"w-kind"[]{'"w";'"a"};"a".(("w-TA"[]{'"w"} '"i") '"a");"l", "tg".(("w-M"[]{'"w"} '"l") '"tg")}


interactive nuprl_w__valtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}} }  -->
   sequent { <H> >- ("w-valtype"[]{'"the_w";'"i";'"a"} in "univ"[level:l]{}) }

interactive nuprl_w__valtype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}} }  -->
   sequent { <H> >- "type"{"w-valtype"[]{'"the_w";'"i";'"a"}} }

define unfold_w__val : "w-val"[]{'"w";'"a"} <-->
      "snd"[]{"outr"[]{'"a"}}


interactive nuprl_w__val_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}} }  -->
   sequent { <H> >- ("w-val"[]{'"the_w";'"a"} in "w-valtype"[]{'"the_w";'"i";'"a"}) }

define unfold_w__isrcvl : "w-isrcvl"[]{'"w";'"l";'"a"} <-->
      "band"[]{"bnot"[]{"w-isnull"[]{'"w";'"a"}};"band"[]{"isrcv"[]{"w-kind"[]{'"w";'"a"}};"eq_lnk"[]{"lnk"[]{"w-kind"[]{'"w";'"a"}};'"l"}}}


interactive nuprl_w__isrcvl_wf {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- ("w-isrcvl"[]{'"the_w";'"l";'"a"} in "bool"[]{}) }

interactive nuprl_assert__w__isrcvl univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   sequent { <H> >- "assert"[]{"w-isrcvl"[]{'"the_w";'"l";'"a"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}};"and"[]{"assert"[]{"isrcv"[]{"w-kind"[]{'"the_w";'"a"}}};"equal"[]{"IdLnk"[]{};"lnk"[]{"w-kind"[]{'"the_w";'"a"}};'"l"}}}} }

define unfold_w__Msg : "w-Msg"[]{'"w"} <-->
      "Msg"[]{"w-M"[]{'"w"}}


interactive nuprl_w__Msg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("w-Msg"[]{'"the_w"} in "univ"[level:l]{}) }

interactive nuprl_w__Msg_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- "type"{"w-Msg"[]{'"the_w"}} }

define unfold_w__Msg__from : "w-Msg-from"[]{'"w";'"i"} <-->
      "set"[]{"w-Msg"[]{'"w"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}


interactive nuprl_w__Msg__from_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("w-Msg-from"[]{'"the_w";'"i"} in "univ"[level:l]{}) }

interactive nuprl_w__Msg__from_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"w-Msg-from"[]{'"the_w";'"i"}} }

define unfold_w__s : "w-s"[]{'"w";'"i";'"t";'"x"} <-->
      ((("fst"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}} '"i") '"t") '"x")


interactive nuprl_w__s_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("w-s"[]{'"the_w";'"i";'"t";'"x"} in "w-vartype"[]{'"the_w";'"i";'"x"}) }

define unfold_w__a : "w-a"[]{'"w";'"i";'"t"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}}} '"i") '"t")


interactive nuprl_w__a_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-a"[]{'"the_w";'"i";'"t"} in "w-action"[]{'"the_w";'"i"}) }

define unfold_w__m : "w-m"[]{'"w";'"i";'"t"} <-->
      (("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"w"}}}}}} '"i") '"t")


interactive nuprl_w__m_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-m"[]{'"the_w";'"i";'"t"} in "list"[]{"set"[]{"Msg"[]{"w-M"[]{'"the_w"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}}) }

interactive nuprl_better__w__m__wf univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-m"[]{'"the_w";'"i";'"t"} in "list"[]{"w-Msg-from"[]{'"the_w";'"i"}}) }

define unfold_w__onlnk : "w-onlnk"[]{'"l";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


interactive nuprl_w__onlnk_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"mss" in "list"[]{"w-Msg"[]{'"the_w"}} }  -->
   sequent { <H> >- ("w-onlnk"[]{'"l";'"mss"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

interactive nuprl_w__onlnk__m univ[level:l]  :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("length"[]{"w-onlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}}} in "int"[]{}) }

define unfold_w__withlnk : "w-withlnk"[]{'"l";'"mss"} <-->
      "mapfilter"[]{"lambda"[]{"ms"."snd"[]{'"ms"}};"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


interactive nuprl_w__withlnk_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"mss" in "list"[]{"w-Msg"[]{'"the_w"}} }  -->
   sequent { <H> >- ("w-withlnk"[]{'"l";'"mss"} in "list"[]{"prod"[]{"Id"[]{};"t".(("w-M"[]{'"the_w"} '"l") '"t")}}) }

define unfold_w__tagged : "w-tagged"[]{'"tg";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_id"[]{"mtag"[]{'"ms"};'"tg"}};'"mss"}


interactive nuprl_w__tagged_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"mss" in "list"[]{"w-Msg"[]{'"the_w"}} }  -->
   sequent { <H> >- ("w-tagged"[]{'"tg";'"mss"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

define unfold_w__ml : "w-ml"[]{'"w";'"l";'"t"} <-->
      "w-onlnk"[]{'"l";"w-m"[]{'"w";"lsrc"[]{'"l"};'"t"}}


interactive nuprl_w__ml_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-ml"[]{'"the_w";'"l";'"t"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

define unfold_w__snds : "w-snds"[]{'"w";'"l";'"t"} <-->
      "concat"[]{"map"[]{"lambda"[]{"t1"."w-ml"[]{'"w";'"l";'"t1"}};"upto"[]{'"t"}}}


interactive nuprl_w__snds_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-snds"[]{'"the_w";'"l";'"t"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

define unfold_w__rcvs : "w-rcvs"[]{'"w";'"l";'"t"} <-->
      "filter"[]{"lambda"[]{"a"."w-isrcvl"[]{'"w";'"l";'"a"}};"map"[]{"lambda"[]{"t1"."w-a"[]{'"w";"ldst"[]{'"l"};'"t1"}};"upto"[]{'"t"}}}


interactive nuprl_w__rcvs_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-rcvs"[]{'"the_w";'"l";'"t"} in "list"[]{"w-action"[]{'"the_w";"ldst"[]{'"l"}}}) }

define unfold_w__queue : "w-queue"[]{'"w";'"l";'"t"} <-->
      "nth_tl"[]{"length"[]{"w-rcvs"[]{'"w";'"l";'"t"}};"w-snds"[]{'"w";'"l";'"t"}}


interactive nuprl_w__queue_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-queue"[]{'"the_w";'"l";'"t"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

interactive nuprl_w__queue__wf2 univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-queue"[]{'"the_w";'"l";'"t"} in "list"[]{"set"[]{"w-Msg"[]{'"the_w"};"m"."equal"[]{"IdLnk"[]{};"mlnk"[]{'"m"};'"l"}}}) }

define unfold_w__msg : "w-msg"[]{'"w";'"a"} <-->
      "msg"[]{"lnk"[]{"w-kind"[]{'"w";'"a"}};"tagof"[]{"w-kind"[]{'"w";'"a"}};"w-val"[]{'"w";'"a"}}


interactive nuprl_w__msg_wf {| intro[] |} univ[level:l] '"i" '"l"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "w-action"[]{'"the_w";'"i"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "assert"[]{"w-isrcvl"[]{'"the_w";'"l";'"a"}} }  -->
   sequent { <H> >- ("w-msg"[]{'"the_w";'"a"} in "w-Msg"[]{'"the_w"}) }

define unfold_fair__fifo : "fair-fifo"[]{'"w"} <-->
      "and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."all"[]{"IdLnk"[]{};"l"."implies"[]{"not"[]{"equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-onlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}};"nil"[]{}}}}}};"and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."implies"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}};"and"[]{"all"[]{"Id"[]{};"x"."equal"[]{"w-vartype"[]{'"w";'"i";'"x"};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"};"w-s"[]{'"w";'"i";'"t";'"x"}}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-m"[]{'"w";'"i";'"t"};"nil"[]{}}}}}};"and"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."all"[]{"IdLnk"[]{};"l"."implies"[]{"assert"[]{"w-isrcvl"[]{'"w";'"l";"w-a"[]{'"w";'"i";'"t"}}};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"cand"[]{"ge"[]{"length"[]{"w-queue"[]{'"w";'"l";'"t"}};"number"[1:n]{}};"equal"[]{"w-Msg"[]{'"w"};"hd"[]{"w-queue"[]{'"w";'"l";'"t"}};"w-msg"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}}}}}}};"all"[]{"IdLnk"[]{};"l"."all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"or"[]{"assert"[]{"w-isrcvl"[]{'"w";'"l";"w-a"[]{'"w";"ldst"[]{'"l"};'"t'"}}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-queue"[]{'"w";'"l";'"t'"};"nil"[]{}}}}}}}}}}


interactive nuprl_fair__fifo_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("fair-fifo"[]{'"the_w"} in "univ"[level:l]{}) }

define unfold_w__E : "w-E"[]{'"w"} <-->
      "set"[]{"prod"[]{"Id"[]{};""."nat"[]{}};"p"."not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"fst"[]{'"p"};"snd"[]{'"p"}}}}}}


interactive nuprl_w__E_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("w-E"[]{'"the_w"} in "univ"[level:l]{}) }

interactive nuprl_w__E_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- "type"{"w-E"[]{'"the_w"}} }

define unfold_w__eq__E : "w-eq-E"[]{'"w";'"p";'"q"} <-->
      "band"[]{"eq_id"[]{"fst"[]{'"p"};"fst"[]{'"q"}};"beq_int"[]{"snd"[]{'"p"};"snd"[]{'"q"}}}


interactive nuprl_w__eq__E_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-eq-E"[]{'"the_w";'"e";'"e'"} in "bool"[]{}) }

interactive nuprl_assert__w__eq__E univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"w-eq-E"[]{'"the_w";'"e";'"e'"}} }  -->
   sequent { <H> >- "equal"[]{"w-E"[]{'"the_w"};'"e";'"e'"} }

interactive nuprl_assert__w__eq__E__iff univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"w-eq-E"[]{'"the_w";'"e";'"e'"}};"equal"[]{"w-E"[]{'"the_w"};'"e";'"e'"}} }

define unfold_w__loc : "w-loc"[]{'"w";'"e"} <-->
      "fst"[]{'"e"}


interactive nuprl_w__loc_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-loc"[]{'"the_w";'"e"} in "Id"[]{}) }

define unfold_w__act : "w-act"[]{'"w";'"e"} <-->
      "w-a"[]{'"w";"fst"[]{'"e"};"snd"[]{'"e"}}


interactive nuprl_w__act_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-act"[]{'"the_w";'"e"} in "set"[]{"w-action"[]{'"the_w";"w-loc"[]{'"the_w";'"e"}};"a"."not"[]{"assert"[]{"w-isnull"[]{'"the_w";'"a"}}}}) }

interactive nuprl_w__act__not__null univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-isnull"[]{'"the_w";"w-act"[]{'"the_w";'"e"}}}} }

define unfold_w__ekind : "w-ekind"[]{'"w";'"e"} <-->
      "w-kind"[]{'"w";"w-act"[]{'"w";'"e"}}


interactive nuprl_w__ekind_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-ekind"[]{'"the_w";'"e"} in "Knd"[]{}) }

define unfold_w__V : "w-V"[]{'"w";'"i";'"k"} <-->
      "kindcase"[]{'"k";"a".(("fst"[]{"snd"[]{'"w"}} '"i") '"a");"l", "tg".(("fst"[]{"snd"[]{"snd"[]{'"w"}}} '"l") '"tg")}


interactive nuprl_w__V_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("w-V"[]{'"the_w";'"i";'"k"} in "univ"[level:l]{}) }

interactive nuprl_w__V_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "type"{"w-V"[]{'"the_w";'"i";'"k"}} }

define unfold_w__eval : "w-eval"[]{'"w";'"e"} <-->
      "w-val"[]{'"w";"w-act"[]{'"w";'"e"}}


interactive nuprl_w__eval_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-eval"[]{'"the_w";'"e"} in "w-V"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};"w-ekind"[]{'"the_w";'"e"}}) }

define unfold_w__time : "w-time"[]{'"w";'"e"} <-->
      "snd"[]{'"e"}


interactive nuprl_w__time_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-time"[]{'"the_w";'"e"} in "nat"[]{}) }

define unfold_w__when : "w-when"[]{'"w";'"x";'"e"} <-->
      "w-s"[]{'"w";"fst"[]{'"e"};"snd"[]{'"e"};'"x"}


interactive nuprl_w__when_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-when"[]{'"the_w";'"x";'"e"} in "w-vartype"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};'"x"}) }

define unfold_w__after : "w-after"[]{'"w";'"x";'"e"} <-->
      "w-s"[]{'"w";"fst"[]{'"e"};"add"[]{"snd"[]{'"e"};"number"[1:n]{}};'"x"}


interactive nuprl_w__after_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-after"[]{'"the_w";'"x";'"e"} in "w-vartype"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};'"x"}) }

define unfold_w__initially : "w-initially"[]{'"w";'"x";'"i"} <-->
      "w-s"[]{'"w";'"i";"number"[0:n]{};'"x"}


interactive nuprl_w__initially_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("w-initially"[]{'"the_w";'"x";'"i"} in "w-vartype"[]{'"the_w";'"i";'"x"}) }

define unfold_w__first : "w-first"[]{'"w";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"w-first"."lambda"[]{"e"."ifthenelse"[]{"beq_int"[]{"w-time"[]{'"w";'"e"};"number"[0:n]{}};"btrue"[]{};"ifthenelse"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}};('"w-first" "pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}});"bfalse"[]{}}}}}) '"e")


interactive nuprl_w__first__aux univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- ("w-first"[]{'"the_w";"pair"[]{'"i";'"t"}} in "bool"[]{}) }

interactive nuprl_w__first_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-first"[]{'"the_w";'"e"} in "bool"[]{}) }

interactive nuprl_assert__w__first univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"w-first"[]{'"the_w";'"e"}};"all"[]{"nat"[]{};"t'"."implies"[]{"lt"[]{'"t'";"w-time"[]{'"the_w";'"e"}};"assert"[]{"w-isnull"[]{'"the_w";"w-a"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};'"t'"}}}}}} }

interactive_rw nuprl_w__loc__time univ[level:l]  :
   ('"the_w" in "world"[level:l]{}) -->
   ('"e" in "w-E"[]{'"the_w"}) -->
   "pair"[]{"w-loc"[]{'"the_w";'"e"};"w-time"[]{'"the_w";'"e"}} <--> '"e"

define unfold_w__pred : "w-pred"[]{'"w";'"e"} <-->
      (("ycomb"[]{} "lambda"[]{"w-pred"."lambda"[]{"e"."ifthenelse"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}};('"w-pred" "pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}});"pair"[]{"w-loc"[]{'"w";'"e"};"sub"[]{"w-time"[]{'"w";'"e"};"number"[1:n]{}}}}}}) '"e")


interactive nuprl_w__pred__aux univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-first"[]{'"the_w";"pair"[]{'"i";'"t"}}}} }  -->
   sequent { <H> >- ("w-pred"[]{'"the_w";"pair"[]{'"i";'"t"}} in "w-E"[]{'"the_w"}) }

interactive nuprl_w__pred_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"w-first"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- ("w-pred"[]{'"the_w";'"e"} in "w-E"[]{'"the_w"}) }

define unfold_w__locl : "w-locl"[]{'"w";'"e";'"e'"} <-->
      "and"[]{"equal"[]{"Id"[]{};"w-loc"[]{'"w";'"e"};"w-loc"[]{'"w";'"e'"}};"lt"[]{"w-time"[]{'"w";'"e"};"w-time"[]{'"w";'"e'"}}}


interactive nuprl_w__locl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-locl"[]{'"the_w";'"e";'"e'"} in "univ"[level:l]{}) }

define unfold_w__sends : "w-sends"[]{'"w";'"l";'"e"} <-->
      "w-onlnk"[]{'"l";"w-m"[]{'"w";"w-loc"[]{'"w";'"e"};"w-time"[]{'"w";'"e"}}}


interactive nuprl_w__sends_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-sends"[]{'"the_w";'"l";'"e"} in "list"[]{"w-Msg"[]{'"the_w"}}) }

interactive nuprl_better__w__sends__wf univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-sends"[]{'"the_w";'"l";'"e"} in "list"[]{"Msg_sub"[]{'"l";"w-M"[]{'"the_w"}}}) }

define unfold_w__match : "w-match"[]{'"w";'"l";'"t";'"t'"} <-->
      "band"[]{"le_bool"[]{"length"[]{"w-snds"[]{'"w";'"l";'"t"}};"length"[]{"w-rcvs"[]{'"w";'"l";'"t'"}}};"lt_bool"[]{"length"[]{"w-rcvs"[]{'"w";'"l";'"t'"}};"add"[]{"length"[]{"w-snds"[]{'"w";'"l";'"t"}};"length"[]{"w-onlnk"[]{'"l";"w-m"[]{'"w";"lsrc"[]{'"l"};'"t"}}}}}}


interactive nuprl_w__match_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   sequent { <H> >- ("w-match"[]{'"the_w";'"l";'"t";'"t'"} in "bool"[]{}) }

interactive nuprl_assert__w__match univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"w-match"[]{'"the_w";'"l";'"t";'"t'"}};"and"[]{"le"[]{"length"[]{"w-snds"[]{'"the_w";'"l";'"t"}};"length"[]{"w-rcvs"[]{'"the_w";'"l";'"t'"}}};"lt"[]{"length"[]{"w-rcvs"[]{'"the_w";'"l";'"t'"}};"add"[]{"length"[]{"w-snds"[]{'"the_w";'"l";'"t"}};"length"[]{"w-onlnk"[]{'"l";"w-m"[]{'"the_w";"lsrc"[]{'"l"};'"t"}}}}}}} }

interactive nuprl_w__match__exists univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};"w-time"[]{'"the_w";'"e"}};"t"."assert"[]{"w-match"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t";"w-time"[]{'"the_w";'"e"}}}} }

interactive nuprl_better__w__match__exists univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};"w-time"[]{'"the_w";'"e"}};"t"."and"[]{"assert"[]{"w-match"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t";"w-time"[]{'"the_w";'"e"}}};"equal"[]{"w-Msg"[]{'"the_w"};"select"[]{"sub"[]{"length"[]{"w-rcvs"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};"w-time"[]{'"the_w";'"e"}}};"length"[]{"w-snds"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t"}}};"w-onlnk"[]{"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};"w-m"[]{'"the_w";"lsrc"[]{"lnk"[]{"w-ekind"[]{'"the_w";'"e"}}};'"t"}}};"w-msg"[]{'"the_w";"w-a"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};"w-time"[]{'"the_w";'"e"}}}}}} }

interactive nuprl_w__match__unique univ[level:l] '"the_w" '"e"  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "assert"[]{"w-match"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t";"w-time"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "assert"[]{"w-match"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t'";"w-time"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"t";'"t'"} }

interactive nuprl_w__match__property univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "assert"[]{"w-match"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t";"w-time"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- "equal"[]{"w-Msg"[]{'"the_w"};"select"[]{"sub"[]{"length"[]{"w-rcvs"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};"w-time"[]{'"the_w";'"e"}}};"length"[]{"w-snds"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};'"t"}}};"w-onlnk"[]{"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};"w-m"[]{'"the_w";"lsrc"[]{"lnk"[]{"w-ekind"[]{'"the_w";'"e"}}};'"t"}}};"w-msg"[]{'"the_w";"w-a"[]{'"the_w";"w-loc"[]{'"the_w";'"e"};"w-time"[]{'"the_w";'"e"}}}} }

define unfold_w__sender : "w-sender"[]{'"w";'"e"} <-->
      "pair"[]{"lsrc"[]{"lnk"[]{"w-ekind"[]{'"w";'"e"}}};"mu"[]{"lambda"[]{"t"."w-match"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};'"t";"w-time"[]{'"w";'"e"}}}}}


interactive nuprl_w__sender_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- ("w-sender"[]{'"the_w";'"e"} in "w-E"[]{'"the_w"}) }

define unfold_w__index : "w-index"[]{'"w";'"e"} <-->
      "sub"[]{"length"[]{"w-rcvs"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};"w-time"[]{'"w";'"e"}}};"length"[]{"w-snds"[]{'"w";"lnk"[]{"w-ekind"[]{'"w";'"e"}};"w-time"[]{'"w";"w-sender"[]{'"w";'"e"}}}}}


interactive nuprl_w__index_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{"w-ekind"[]{'"the_w";'"e"}}} }  -->
   sequent { <H> >- ("w-index"[]{'"the_w";'"e"} in "int_seg"[]{"number"[0:n]{};"length"[]{"w-sends"[]{'"the_w";"lnk"[]{"w-ekind"[]{'"the_w";'"e"}};"w-sender"[]{'"the_w";'"e"}}}}) }

define unfold_w__causl : "w-causl"[]{'"w";'"e";'"e'"} <-->
      "infix_ap"[]{"rel_plus"[]{"w-E"[]{'"w"};"lambda"[]{"e"."lambda"[]{"e'"."or"[]{"w-locl"[]{'"w";'"e";'"e'"};"cand"[]{"assert"[]{"isrcv"[]{"w-ekind"[]{'"w";'"e'"}}};"equal"[]{"w-E"[]{'"w"};'"e";"w-sender"[]{'"w";'"e'"}}}}}}};'"e";'"e'"}


interactive nuprl_w__causl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- ("w-causl"[]{'"the_w";'"e";'"e'"} in "univ"[level:l]{}) }

interactive nuprl_w__causl__time univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "w-causl"[]{'"the_w";'"e";'"e'"} }  -->
   sequent { <H> >- "lt"[]{"w-time"[]{'"the_w";'"e"};"w-time"[]{'"the_w";'"e'"}} }

interactive nuprl_w__locl__iff univ[level:l]  :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "w-E"[]{'"the_w"} }  -->
   [wf] sequent { <H> >- '"e'" in "w-E"[]{'"the_w"} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "iff"[]{"w-locl"[]{'"the_w";'"e";'"e'"};"and"[]{"equal"[]{"Id"[]{};"w-loc"[]{'"the_w";'"e"};"w-loc"[]{'"the_w";'"e'"}};"w-causl"[]{'"the_w";'"e";'"e'"}}} }

interactive nuprl_world__event__system   :
   [wf] sequent { <H> >- '"the_w" in "world"[level:l]{} }  -->
   sequent { <H> >- "fair-fifo"[]{'"the_w"} }  -->
   sequent { <H> >- "ESAxioms"[level:l]{"w-E"[]{'"the_w"};"lambda"[]{"i"."lambda"[]{"x"."w-vartype"[]{'"the_w";'"i";'"x"}}};"w-M"[]{'"the_w"};"lambda"[]{"e"."w-loc"[]{'"the_w";'"e"}};"lambda"[]{"e"."w-ekind"[]{'"the_w";'"e"}};"lambda"[]{"e"."w-eval"[]{'"the_w";'"e"}};"lambda"[]{"x"."lambda"[]{"e"."w-when"[]{'"the_w";'"x";'"e"}}};"lambda"[]{"x"."lambda"[]{"e"."w-after"[]{'"the_w";'"x";'"e"}}};"lambda"[]{"l"."lambda"[]{"e"."w-sends"[]{'"the_w";'"l";'"e"}}};"lambda"[]{"e"."w-sender"[]{'"the_w";'"e"}};"lambda"[]{"e"."w-index"[]{'"the_w";'"e"}};"lambda"[]{"e"."w-first"[]{'"the_w";'"e"}};"lambda"[]{"e"."w-pred"[]{'"the_w";'"e"}};"lambda"[]{"e"."lambda"[]{"e'"."w-causl"[]{'"the_w";'"e";'"e'"}}}} }

define unfold_w__es : "w-es"[level:l]{'"the_w";'"p"} <-->
      "pair"[]{"w-E"[]{'"the_w"};"pair"[]{"product-deq"[]{"Id"[]{};"nat"[]{};"id-deq"[]{};"nat-deq"[]{}};"pair"[]{"lambda"[]{"i"."lambda"[]{"x"."w-vartype"[]{'"the_w";'"i";'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."w-V"[]{'"the_w";'"i";"locl"[]{'"a"}}}};"pair"[]{"w-M"[]{'"the_w"};"pair"[]{"it"[]{};"pair"[]{"lambda"[]{"e"."w-loc"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-ekind"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-eval"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"x"."lambda"[]{"e"."w-when"[]{'"the_w";'"x";'"e"}}};"pair"[]{"lambda"[]{"x"."lambda"[]{"e"."w-after"[]{'"the_w";'"x";'"e"}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"e"."w-sends"[]{'"the_w";'"l";'"e"}}};"pair"[]{"lambda"[]{"e"."w-sender"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-index"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-first"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."w-pred"[]{'"the_w";'"e"}};"pair"[]{"lambda"[]{"e"."lambda"[]{"e'"."w-causl"[]{'"the_w";'"e";'"e'"}}};"pair"[]{(("termof"[]{} '"the_w") '"p");"it"[]{}}}}}}}}}}}}}}}}}}}


interactive nuprl_w__es_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"p" in "fair-fifo"[]{'"w"} }  -->
   sequent { <H> >- ("w-es"[level:l]{'"w";'"p"} in "event_system"[level:l]{}) }

interactive nuprl_mlnk__hd__w__queue univ[level:l]  :
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ln" in "IdLnk"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{"w-queue"[]{'"w";'"ln";'"t"}}} }  -->
   sequent { <H> >- "equal"[]{"IdLnk"[]{};"mlnk"[]{"hd"[]{"w-queue"[]{'"w";'"ln";'"t"}}};'"ln"} }

interactive nuprl_decl__rename__cap   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"r" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"z" in "univ"[level:l]{} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"r"} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};"fpf-cap"[]{"fpf-rename"[]{"id-deq"[]{};'"r";'"f"};"id-deq"[]{};('"r" '"a");'"z"};"fpf-cap"[]{'"f";"id-deq"[]{};'"a";'"z"}} }

define unfold_action__rename : "action-rename"[]{'"rainv";'"rtinv";'"a"} <-->
      "decide"[]{'"a";"x"."inl"[]{'"x"};"p"."kindcase"[]{"fst"[]{'"p"};"a"."decide"[]{('"rainv" '"a");"b"."inr"[]{"pair"[]{"locl"[]{'"b"};"snd"[]{'"p"}}};"b"."inl"[]{"it"[]{}}};"l", "tg"."decide"[]{('"rtinv" '"tg");"t"."inr"[]{"pair"[]{"rcv"[]{'"l";'"t"};"snd"[]{'"p"}}};"b"."inl"[]{"it"[]{}}}}}


interactive nuprl_action__rename_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Knd"[]{} >- "type"{'"dec" '"x" } }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rainv" '"x" in "union"[]{"Id"[]{};"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rtinv" '"x" in "union"[]{"Id"[]{};"unit"[]{}} }  -->
   sequent { <H>; "tg1": "Id"[]{} ; "tg2": "Id"[]{} ; "equal"[]{"union"[]{"Id"[]{};"unit"[]{}};('"rtinv" '"tg2");"inl"[]{'"tg1"}}  >- "equal"[]{"Id"[]{};'"tg2";('"rt" '"tg1")} }  -->
   sequent { <H>; "a1": "Id"[]{} ; "a2": "Id"[]{} ; "equal"[]{"union"[]{"Id"[]{};"unit"[]{}};('"rainv" '"a2");"inl"[]{'"a1"}}  >- "equal"[]{"Id"[]{};'"a2";('"ra" '"a1")} }  -->
   [wf] sequent { <H> >- '"a" in "action"[]{'"dec"} }  -->
   sequent { <H> >- ("action-rename"[]{'"rainv";'"rtinv";'"a"} in "action"[]{"lambda"[]{"k".('"dec" "kind-rename"[]{'"ra";'"rt";'"k"})}}) }

define unfold_world__rename : "world-rename"[]{'"rx";'"ra";'"rt";'"rainv";'"rtinv";'"w"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."w-vartype"[]{'"w";'"i";('"rx" '"x")}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a".(("fst"[]{"snd"[]{'"w"}} '"i") ('"ra" '"a"))}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg".(("w-M"[]{'"w"} '"l") ('"rt" '"tg"))}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";('"rx" '"x")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."action-rename"[]{'"rainv";'"rtinv";"w-a"[]{'"w";'"i";'"t"}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."mapfilter"[]{"lambda"[]{"m"."msg-rename"[]{'"rtinv";'"m"}};"lambda"[]{"m"."is_inl"[]{('"rtinv" "mtag"[]{'"m"})}};"w-m"[]{'"w";'"i";'"t"}}}};"it"[]{}}}}}}}


interactive nuprl_world__rename_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rx" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rainv" '"x" in "union"[]{"Id"[]{};"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rtinv" '"x" in "union"[]{"Id"[]{};"unit"[]{}} }  -->
   sequent { <H> >- "inv-rel"[]{"Id"[]{};"Id"[]{};'"ra";'"rainv"} }  -->
   sequent { <H> >- "inv-rel"[]{"Id"[]{};"Id"[]{};'"rt";'"rtinv"} }  -->
   sequent { <H> >- ("world-rename"[]{'"rx";'"ra";'"rt";'"rainv";'"rtinv";'"w"} in "world"[level:l]{}) }

interactive_rw nuprl_es__valtype__w__valtype   :
   ('"i" in "Id"[]{}) -->
   ('"w" in "world"[level:l]{}) -->
   ('"p" in "fair-fifo"[]{'"w"}) -->
   ('"t" in "nat"[]{}) -->
   "not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}} -->
   "es-valtype"[]{"w-es"[level:l]{'"w";'"p"};"pair"[]{'"i";'"t"}} <--> "w-valtype"[]{'"w";'"i";"w-a"[]{'"w";'"i";'"t"}}


(**** display forms ****)


dform nuprl_action_df : except_mode[src] :: "action"[]{'"dec"} =
   `"Action(" slot{'"dec"} `")"


dform nuprl_null__action_df : except_mode[src] :: "null-action"[]{} =
   `"null"


dform nuprl_doact_df : except_mode[src] :: "doact"[]{'"k";'"v"} =
   `"doact(" slot{'"k"} `";" slot{'"v"} `")"


dform nuprl_w__action__dec_df : except_mode[src] :: "w-action-dec"[]{'"TA";'"M";'"i"} =
   `"w-action-dec(" slot{'"TA"} `";" slot{'"M"} `";" slot{'"i"} `")"


dform nuprl_world_df : except_mode[src] :: "world"[level:l]{} =
   `"World"


dform nuprl_w__T_df : except_mode[src] :: "w-T"[]{'"w"} =
   `"" slot{'"w"} `".T"


dform nuprl_w__TA_df : except_mode[src] :: "w-TA"[]{'"w"} =
   `"" slot{'"w"} `".TA"



dform nuprl_w__M_df : except_mode[src] :: "w-M"[]{'"w"} =
   `"" slot{'"w"} `".M"


dform nuprl_w__vartype_df : except_mode[src] :: "w-vartype"[]{'"w";'"i";'"x"} =
   `"vartype(" slot{'"i"} `";" slot{'"x"} `")"


dform nuprl_w__action_df : except_mode[src] :: "w-action"[]{'"w";'"i"} =
   `"Action(" slot{'"i"} `")"


dform nuprl_w__isnull_df : except_mode[src] :: "w-isnull"[]{'"w";'"a"} =
   `"isnull(" slot{'"a"} `")"


dform nuprl_w__kind_df : except_mode[src] :: "w-kind"[]{'"w";'"a"} =
   `"kind(" slot{'"a"} `")"


dform nuprl_w__valtype_df : except_mode[src] :: "w-valtype"[]{'"w";'"i";'"a"} =
   `"valtype(" slot{'"i"} `";" slot{'"a"} `")"


dform nuprl_w__val_df : except_mode[src] :: "w-val"[]{'"w";'"a"} =
   `"val(" slot{'"a"} `")"


dform nuprl_w__isrcvl_df : except_mode[src] :: "w-isrcvl"[]{'"w";'"l";'"a"} =
   `"isrcv(" slot{'"l"} `";" slot{'"a"} `")"


dform nuprl_w__Msg_df : except_mode[src] :: "w-Msg"[]{'"w"} =
   `"Msg"


dform nuprl_w__Msg__from_df : except_mode[src] :: "w-Msg-from"[]{'"w";'"i"} =
   `"MsgFrom(" slot{'"i"} `")"


dform nuprl_w__s_df : except_mode[src] :: "w-s"[]{'"w";'"i";'"t";'"x"} =
   `"s(" slot{'"i"} `";" slot{'"t"} `")." slot{'"x"} `""


dform nuprl_w__a_df : except_mode[src] :: "w-a"[]{'"w";'"i";'"t"} =
   `"a(" slot{'"i"} `";" slot{'"t"} `")"


dform nuprl_w__m_df : except_mode[src] :: "w-m"[]{'"w";'"i";'"t"} =
   `"m(" slot{'"i"} `";" slot{'"t"} `")"


dform nuprl_w__onlnk_df : except_mode[src] :: "w-onlnk"[]{'"l";'"mss"} =
   `"onlnk(" slot{'"l"} `";" slot{'"mss"} `")"


dform nuprl_w__withlnk_df : except_mode[src] :: "w-withlnk"[]{'"l";'"mss"} =
   `"withlnk(" slot{'"l"} `";" slot{'"mss"} `")"


dform nuprl_w__tagged_df : except_mode[src] :: "w-tagged"[]{'"tg";'"mss"} =
   `"w-tagged(" slot{'"tg"} `";" slot{'"mss"} `")"


dform nuprl_w__ml_df : except_mode[src] :: "w-ml"[]{'"w";'"l";'"t"} =
   `"m(" slot{'"l"} `";" slot{'"t"} `")"


dform nuprl_w__snds_df : except_mode[src] :: "w-snds"[]{'"w";'"l";'"t"} =
   `"snds(" slot{'"l"} `";" slot{'"t"} `")"


dform nuprl_w__rcvs_df : except_mode[src] :: "w-rcvs"[]{'"w";'"l";'"t"} =
   `"rcvs(" slot{'"l"} `";" slot{'"t"} `")"


dform nuprl_w__queue_df : except_mode[src] :: "w-queue"[]{'"w";'"l";'"t"} =
   `"queue(" slot{'"l"} `";" slot{'"t"} `")"


dform nuprl_w__msg_df : except_mode[src] :: "w-msg"[]{'"w";'"a"} =
   `"msg(" slot{'"a"} `")"


dform nuprl_fair__fifo_df : except_mode[src] :: "fair-fifo"[]{'"w"} =
   `"FairFifo"


dform nuprl_w__E_df : except_mode[src] :: "w-E"[]{'"w"} =
   `"E"


dform nuprl_w__eq__E_df : except_mode[src] :: "w-eq-E"[]{'"w";'"p";'"q"} =
   `"" slot{'"p"} `" = " slot{'"q"} `""


dform nuprl_w__loc_df : except_mode[src] :: "w-loc"[]{'"w";'"e"} =
   `"loc(" slot{'"e"} `")"


dform nuprl_w__act_df : except_mode[src] :: "w-act"[]{'"w";'"e"} =
   `"act(" slot{'"e"} `")"


dform nuprl_w__ekind_df : except_mode[src] :: "w-ekind"[]{'"w";'"e"} =
   `"kind(" slot{'"e"} `")"


dform nuprl_w__V_df : except_mode[src] :: "w-V"[]{'"w";'"i";'"k"} =
   `"V(" slot{'"i"} `";" slot{'"k"} `")"


dform nuprl_w__eval_df : except_mode[src] :: "w-eval"[]{'"w";'"e"} =
   `"val(" slot{'"e"} `")"


dform nuprl_w__time_df : except_mode[src] :: "w-time"[]{'"w";'"e"} =
   `"time(" slot{'"e"} `")"


dform nuprl_w__when_df : except_mode[src] :: "w-when"[]{'"w";'"x";'"e"} =
   `"(" slot{'"x"} `" when " slot{'"e"} `")"


dform nuprl_w__after_df : except_mode[src] :: "w-after"[]{'"w";'"x";'"e"} =
   `"(" slot{'"x"} `" after " slot{'"e"} `")"


dform nuprl_w__initially_df : except_mode[src] :: "w-initially"[]{'"w";'"x";'"i"} =
   `"(" slot{'"x"} `" initially " slot{'"i"} `")"


dform nuprl_w__first_df : except_mode[src] :: "w-first"[]{'"w";'"e"} =
   `"first(" slot{'"e"} `")"


dform nuprl_w__pred_df : except_mode[src] :: "w-pred"[]{'"w";'"e"} =
   `"pred(" slot{'"e"} `")"


dform nuprl_w__locl_df : except_mode[src] :: "w-locl"[]{'"w";'"e";'"e'"} =
   `"" slot{'"e"} `" <loc " slot{'"e'"} `""


dform nuprl_w__sends_df : except_mode[src] :: "w-sends"[]{'"w";'"l";'"e"} =
   `"sends(" slot{'"l"} `";" slot{'"e"} `")"


dform nuprl_w__match_df : except_mode[src] :: "w-match"[]{'"w";'"l";'"t";'"t'"} =
   `"match(" slot{'"l"} `";" slot{'"t"} `";" slot{'"t'"} `")"


dform nuprl_w__sender_df : except_mode[src] :: "w-sender"[]{'"w";'"e"} =
   `"sender(" slot{'"e"} `")"


dform nuprl_w__index_df : except_mode[src] :: "w-index"[]{'"w";'"e"} =
   `"index(" slot{'"e"} `")"


dform nuprl_w__causl_df : except_mode[src] :: "w-causl"[]{'"w";'"e";'"e'"} =
   `"" slot{'"e"} `" <c " slot{'"e'"} `""


dform nuprl_w__es_df : except_mode[src] :: "w-es"[level:l]{'"the_w";'"p"} =
   `"ES(" slot{'"the_w"} `";" slot{'"p"} `")"

dform nuprl_w__es_df : except_mode[src] :: "w-es"[level:l]{'"the_w";'"p"} =
   `"ES(" slot{'"the_w"} `")"


dform nuprl_action__rename_df : except_mode[src] :: "action-rename"[]{'"ra";'"rt";'"a"} =
   `"action-rename(" slot{'"ra"} `";" slot{'"rt"} `";" slot{'"a"} `")"

dform nuprl_world__rename_df : except_mode[src] :: "world-rename"[]{'"rx";'"ra";'"rt";'"rainv";'"rtinv";'"w"} =
   `"world-rename(" slot{'"rx"} `";" slot{'"ra"} `";" slot{'"rt"} `";"
    slot{'"rainv"} `";" slot{'"rtinv"} `";" slot{'"w"} `")"




