extends Ma_worlds

open Dtactic


define unfold_ma__state : "ma-state"[]{'"ds"} <-->
      "fun"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}


interactive nuprl_ma__state_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"z"."univ"[level:l]{}} }  -->
   sequent { <H> >- ("ma-state"[]{'"ds"} in "univ"[level:l]{}) }

interactive nuprl_ma__state_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"z"."univ"[level:l]{}} }  -->
   sequent { <H> >- "type"{"ma-state"[]{'"ds"}} }

define unfold_ma__kind : "ma-kind"[]{'"da"} <-->
      "set"[]{"Knd"[]{};"k"."assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"k";'"da"}}}


interactive nuprl_ma__kind_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"z"."univ"[level:l]{}} }  -->
   sequent { <H> >- ("ma-kind"[]{'"da"} in "univ"[level:l]{}) }

interactive nuprl_ma__kind_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"z"."univ"[level:l]{}} }  -->
   sequent { <H> >- "type"{"ma-kind"[]{'"da"}} }

define unfold_ma__valtype : "ma-valtype"[]{'"da";'"k"} <-->
      "fpf-cap"[]{'"da";"Kind-deq"[]{};'"k";"top"[]{}}


interactive nuprl_ma__valtype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"z"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("ma-valtype"[]{'"da";'"k"} in "univ"[level:l]{}) }

interactive nuprl_ma__valtype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"z"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "type"{"ma-valtype"[]{'"da";'"k"}} }

define unfold_ma__Msg : "ma-Msg"[]{'"da"} <-->
      "Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}


interactive nuprl_ma__Msg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   sequent { <H> >- ("ma-Msg"[]{'"da"} in "univ"[level:l]{}) }

interactive nuprl_ma__Msg_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   sequent { <H> >- "type"{"ma-Msg"[]{'"da"}} }

define unfold_msga : "msga"[level:l]{} <-->
      "prod"[]{"fpf"[]{"Id"[]{};"x"."univ"[level:l]{}};"ds"."prod"[]{"fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}};"da"."prod"[]{"fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}};"init"."prod"[]{"fpf"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"locl"[]{'"a"}};""."univ"[level:l]{}}}};"pre"."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kx"}};""."fpf-cap"[]{'"ds";"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}}};"ef"."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}}};"send"."prod"[]{"fpf"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}}};"frame"."prod"[]{"fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}}};"sframe"."top"[]{}}}}}}}}}


interactive nuprl_msga_wf {| intro[] |}   :
   sequent { <H> >- ("msga"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_msga_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"msga"[level:l]{}} }

interactive nuprl_msga__subtype   :
   sequent { <H> >- "true"[]{} }

define unfold_ma__X : "ma-X"[]{'"M"} <-->
      "set"[]{"Id"[]{};"x"."assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";"fst"[]{'"M"}}}}


interactive nuprl_ma__X_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-X"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_ma__X_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-X"[]{'"M"}} }

define unfold_ma__A : "ma-A"[]{'"M"} <-->
      "set"[]{"Knd"[]{};"a"."assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"a";"fst"[]{"snd"[]{'"M"}}}}}


interactive nuprl_ma__A_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-A"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_ma__A_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-A"[]{'"M"}} }

define unfold_ma__ds : "ma-ds"[]{'"M";'"x"} <-->
      "fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};'"x";"top"[]{}}


interactive nuprl_ma__ds_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-ds"[]{'"M";'"x"} in "univ"[level:l]{}) }

interactive nuprl_ma__ds_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"ma-ds"[]{'"M";'"x"}} }

define unfold_ma__da : "ma-da"[]{'"M";'"a"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};'"a";"top"[]{}}


define unfold_ma__declx : "ma-declx"[]{'"M";'"x"} <-->
      "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";"fst"[]{'"M"}}}


interactive nuprl_ma__declx_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-declx"[]{'"M";'"x"} in "univ"[level:l]{}) }

interactive nuprl_decidable__ma__declx univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "decidable"[]{"ma-declx"[]{'"M";'"x"}} }

interactive nuprl_not__ma__declx__implies   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"ma-declx"[]{'"M";'"x"}} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};"ma-ds"[]{'"M";'"x"};"top"[]{}} }

define unfold_ma__declk : "ma-declk"[]{'"M";'"k"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"k";"fst"[]{"snd"[]{'"M"}}}}


interactive nuprl_ma__declk_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("ma-declk"[]{'"M";'"k"} in "univ"[level:l]{}) }

interactive nuprl_not__ma__declk__implies   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "not"[]{"ma-declk"[]{'"M";'"k"}} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};"ma-da"[]{'"M";'"k"};"top"[]{}} }

define unfold_ma__decla : "ma-decla"[]{'"M";'"a"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};"locl"[]{'"a"};"fst"[]{"snd"[]{'"M"}}}}


interactive nuprl_ma__decla_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-decla"[]{'"M";'"a"} in "univ"[level:l]{}) }

interactive nuprl_decidable__ma__declk univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "decidable"[]{"ma-declk"[]{'"M";'"k"}} }

define unfold_ma__declm : "ma-declm"[]{'"M";'"l";'"tg"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"fst"[]{"snd"[]{'"M"}}}}


interactive nuprl_ma__declm_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-declm"[]{'"M";'"l";'"tg"} in "univ"[level:l]{}) }

interactive nuprl_decidable__ma__declm univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "decidable"[]{"ma-declm"[]{'"M";'"l";'"tg"}} }

define unfold_da__outlink__f : "da-outlink-f"[]{'"da";'"k"} <-->
      "pair"[]{"lnk"[]{'"k"};"pair"[]{"tagof"[]{'"k"};"fpf-ap"[]{'"da";"Kind-deq"[]{};'"k"}}}


interactive nuprl_da__outlink__f_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"k" in "set"[]{"Knd"[]{};"k"."and"[]{"assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"k";'"da"}};"assert"[]{"isrcv"[]{'"k"}}}} }  -->
   sequent { <H> >- ("da-outlink-f"[]{'"da";'"k"} in "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}) }

define unfold_da__outlinks : "da-outlinks"[]{'"da";'"i"} <-->
      "mapfilter"[]{"lambda"[]{"k"."da-outlink-f"[]{'"da";'"k"}};"lambda"[]{"k"."has-src"[]{'"i";'"k"}};"fpf-dom-list"[]{'"da"}}


interactive nuprl_da__outlinks_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("da-outlinks"[]{'"da";'"i"} in "list"[]{"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}}) }

interactive nuprl_da__outlinks__empty univ[level:l] '"i" '"ltg"  :
   [wf] sequent { <H> >- '"ltg" in "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "mem"[]{'"ltg";"da-outlinks"[]{"fpf-empty"[]{};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}} }  -->
   sequent { <H> >- "false"[]{} }

interactive nuprl_da__outlinks__single   :
   [wf] sequent { <H> >- '"ltg" in "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "mem"[]{'"ltg";"da-outlinks"[]{"fpf-single"[]{'"k";'"T"};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"and"[]{"assert"[]{"isrcv"[]{'"k"}};"equal"[]{"Id"[]{};"lsrc"[]{"lnk"[]{'"k"}};'"i"}};"and"[]{"rewrite"[]{"fst"[]{'"ltg"};"lnk"[]{'"k"}};"and"[]{"rewrite"[]{"fst"[]{"snd"[]{'"ltg"}};"tagof"[]{'"k"}};"equal"[]{"univ"[level:l]{};"snd"[]{"snd"[]{'"ltg"}};'"T"}}}}} }

interactive nuprl_da__outlinks__join   :
   [wf] sequent { <H> >- '"ltg" in "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"da1" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da2" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   sequent { <H> >- "mem"[]{'"ltg";"da-outlinks"[]{"fpf-join"[]{"Kind-deq"[]{};'"da1";'"da2"};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}} }  -->
   sequent { <H> >- "or"[]{"mem"[]{'"ltg";"da-outlinks"[]{'"da1";'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}};"mem"[]{'"ltg";"da-outlinks"[]{'"da2";'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}}} }

define unfold_ma__outlinks : "ma-outlinks"[]{'"M";'"i"} <-->
      "da-outlinks"[]{"fst"[]{"snd"[]{'"M"}};'"i"}


interactive nuprl_ma__outlinks_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-outlinks"[]{'"M";'"i"} in "list"[]{"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}}) }

interactive nuprl_ma__da_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   sequent { <H> >- ("ma-da"[]{'"M";'"a"} in "univ"[level:l]{}) }

interactive nuprl_ma__da_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   sequent { <H> >- "type"{"ma-da"[]{'"M";'"a"}} }

define unfold_ma__din : "ma-din"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"top"[]{}}


interactive nuprl_ma__din_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-din"[]{'"M";'"l";'"tg"} in "univ"[level:l]{}) }

interactive nuprl_ma__din_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"ma-din"[]{'"M";'"l";'"tg"}} }

interactive_rw nuprl_din__not__declared univ[level:l]  :
   ('"M" in "msga"[level:l]{}) -->
   ('"l" in "IdLnk"[]{}) -->
   ('"tg" in "Id"[]{}) -->
   "not"[]{"ma-declm"[]{'"M";'"l";'"tg"}} -->
   "ma-din"[]{'"M";'"l";'"tg"} <--> "top"[]{}

define unfold_ma__tag__type : "ma-tag-type"[level:l]{'"M";'"tg";'"T"} <-->
      "all"[]{"IdLnk"[]{};"l"."implies"[]{"ma-declm"[]{'"M";'"l";'"tg"};"equal"[]{"univ"[level:l]{};"ma-din"[]{'"M";'"l";'"tg"};'"T"}}}


interactive nuprl_ma__tag__type_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-tag-type"[level:l]{'"M";'"tg";'"T"} in "univ"[level':l]{}) }

define unfold_ma__dout : "ma-dout"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}


interactive nuprl_ma__dout_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-dout"[]{'"M";'"l";'"tg"} in "univ"[level:l]{}) }

interactive nuprl_ma__dout_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"ma-dout"[]{'"M";'"l";'"tg"}} }

define unfold_ma__init : "ma-init"[]{'"M";'"x";'"v"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M"}}};'"x";"a", "x0"."equal"[]{"fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};'"x";"void"[]{}};'"v";'"x0"}}


interactive nuprl_ma__init_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "ma-ds"[]{'"M";'"x"} }  -->
   sequent { <H> >- ("ma-init"[]{'"M";'"x";'"v"} in "univ"[level:l]{}) }

define unfold_ma__init__val : "ma-init-val"[]{'"M";'"x";'"v"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{"snd"[]{'"M"}}};"id-deq"[]{};'"x";'"v"}


interactive nuprl_ma__init__val_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "ma-ds"[]{'"M";'"x"} }  -->
   sequent { <H> >- ("ma-init-val"[]{'"M";'"x";'"v"} in "ma-ds"[]{'"M";'"x"}) }

define unfold_ma__st : "ma-st"[]{'"M"} <-->
      "ma-state"[]{"fst"[]{'"M"}}


interactive nuprl_ma__st_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-st"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_ma__st_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-st"[]{'"M"}} }

define unfold_ma__msg : "ma-msg"[]{'"M"} <-->
      "ma-Msg"[]{"fst"[]{"snd"[]{'"M"}}}


interactive nuprl_ma__msg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-msg"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_ma__msg_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-msg"[]{'"M"}} }

define unfold_ma__k : "ma-k"[]{'"M"} <-->
      "ma-kind"[]{"fst"[]{"snd"[]{'"M"}}}


interactive nuprl_ma__k_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-k"[]{'"M"} in "univ"[level:l]{}) }

interactive nuprl_ma__k_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-k"[]{'"M"}} }

define unfold_ma__v : "ma-v"[]{'"M";'"k"} <-->
      "ma-valtype"[]{"fst"[]{"snd"[]{'"M"}};'"k"}


interactive nuprl_ma__v_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("ma-v"[]{'"M";'"k"} in "univ"[level:l]{}) }

interactive nuprl_ma__v_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "type"{"ma-v"[]{'"M";'"k"}} }

define unfold_ma__npre : "ma-npre"[]{'"M";'"a";'"s"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};'"a";"a", "P"."all"[]{"ma-da"[]{'"M";"locl"[]{'"a"}};"v"."not"[]{(('"P" '"s") '"v")}}}


interactive nuprl_ma__npre_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   sequent { <H> >- ("ma-npre"[]{'"M";'"a";'"s"} in "univ"[level:l]{}) }

define unfold_ma__pre : "ma-pre"[]{'"M";'"a";'"s";'"v"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};'"a";"a", "P".(('"P" '"s") '"v")}


interactive nuprl_ma__pre_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M";"locl"[]{'"a"}} }  -->
   sequent { <H> >- ("ma-pre"[]{'"M";'"a";'"s";'"v"} in "univ"[level:l]{}) }

define unfold_ma__has__pre : "ma-has-pre"[]{'"M";'"a"} <-->
      "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"a";"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}


interactive nuprl_ma__has__pre_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-has-pre"[]{'"M";'"a"} in "univ"[level:l]{}) }

interactive nuprl_decidable__ma__has__pre univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- "decidable"[]{"ma-has-pre"[]{'"M";'"a"}} }

define unfold_ma__ef : "ma-ef"[]{'"M";'"k";'"x";'"s";'"v";'"w"} <-->
      "fpf-val"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"pair"[]{'"k";'"x"};"kx", "E"."equal"[]{"ma-ds"[]{'"M";'"x"};'"w";(('"E" '"s") '"v")}}


interactive nuprl_ma__ef_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M";'"k"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"w" in "ma-ds"[]{'"M";'"x"} }  -->
   sequent { <H> >- ("ma-ef"[]{'"M";'"k";'"x";'"s";'"v";'"w"} in "univ"[level:l]{}) }

define unfold_ma__ef__val : "ma-ef-val"[]{'"M";'"k";'"x";'"s";'"v";'"w"} <-->
      (("fpf-cap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"pair"[]{'"k";'"x"};"lambda"[]{"s"."lambda"[]{"v".'"w"}}} '"s") '"v")


interactive nuprl_ma__ef__val_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M";'"k"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"w" in "ma-ds"[]{'"M";'"x"} }  -->
   sequent { <H> >- ("ma-ef-val"[]{'"M";'"k";'"x";'"s";'"v";'"w"} in "ma-ds"[]{'"M";'"x"}) }

define unfold_tagged__list__messages : "tagged-list-messages"[]{'"s";'"v";'"L"} <-->
      "concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"s") '"v")}};'"L"}}


interactive nuprl_tagged__list__messages_wf {| intro[] |}  '"S" '"V" "lambda"[]{"x".'"M"['"x"]} '"L" '"v" '"s"  :
   [wf] sequent { <H> >- "type"{'"S" } }  -->
   [wf] sequent { <H> >- "type"{'"V" } }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- "type"{'"M"['"x"] } }  -->
   [wf] sequent { <H> >- '"s" in '"S" }  -->
   [wf] sequent { <H> >- '"v" in '"V" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"prod"[]{"Id"[]{};"t"."fun"[]{'"S";""."fun"[]{'"V";""."list"[]{'"M"['"t"]}}}}} }  -->
   sequent { <H> >- ("tagged-list-messages"[]{'"s";'"v";'"L"} in "list"[]{"prod"[]{"Id"[]{};"t".'"M"['"t"]}}) }

define unfold_tagged__messages : "tagged-messages"[]{'"l";'"s";'"v";'"L"} <-->
      "map"[]{"lambda"[]{"x"."pair"[]{'"l";'"x"}};"tagged-list-messages"[]{'"s";'"v";'"L"}}


interactive nuprl_tagged__messages_wf {| intro[] |}  '"S" '"V" '"l" "lambda"[]{"x1", "x".'"M"['"x1";'"x"]} '"L" '"v" '"s"  :
   [wf] sequent { <H> >- "type"{'"S" } }  -->
   [wf] sequent { <H> >- "type"{'"V" } }  -->
   [wf] sequent { <H>;"x": "IdLnk"[]{};"x1": "Id"[]{} >- "type"{'"M"['"x";'"x1"] } }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"s" in '"S" }  -->
   [wf] sequent { <H> >- '"v" in '"V" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"prod"[]{"Id"[]{};"t"."fun"[]{'"S";""."fun"[]{'"V";""."list"[]{'"M"['"l";'"t"]}}}}} }  -->
   sequent { <H> >- ("tagged-messages"[]{'"l";'"s";'"v";'"L"} in "list"[]{"set"[]{"Msg"[]{"lambda"[]{"x1"."lambda"[]{"x".'"M"['"x1";'"x"]}}};"m"."equal"[]{"IdLnk"[]{};"mlnk"[]{'"m"};'"l"}}}) }

define unfold_ma__send : "ma-send"[]{'"M";'"k";'"l";'"s";'"v";'"ms";'"i"} <-->
      "fpf-val"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"pair"[]{'"k";'"l"};"k", "L"."equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg"."ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"ma-da"[]{'"M";"rcv"[]{'"l";'"tg"}};"top"[]{}}}};'"ms";"ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"s") '"v")}};'"L"}};"nil"[]{}}}}


interactive nuprl_ma__send_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-v"[]{'"M";'"k"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ms" in "list"[]{"prod"[]{"Id"[]{};"tg"."ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"ma-da"[]{'"M";"rcv"[]{'"l";'"tg"}};"top"[]{}}}} }  -->
   sequent { <H> >- ("ma-send"[]{'"M";'"k";'"l";'"s";'"v";'"ms";'"i"} in "univ"[level:l]{}) }

define unfold_ma__send__val : "ma-send-val"[]{'"M";'"k";'"s";'"v"} <-->
      "concat"[]{"map"[]{"lambda"[]{"pL"."tagged-messages"[]{"snd"[]{"fst"[]{'"pL"}};'"s";'"v";"snd"[]{'"pL"}}};"fpf-vals"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"lambda"[]{"p".(("eqof"[]{"Kind-deq"[]{}} "fst"[]{'"p"}) '"k")};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}


interactive nuprl_ma__send__val_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M";'"k"} }  -->
   sequent { <H> >- ("ma-send-val"[]{'"M";'"k";'"s";'"v"} in "list"[]{"ma-msg"[]{'"M"}}) }

define unfold_ma__sends__on : "ma-sends-on"[]{'"M";'"l"} <-->
      "deq-member"[]{"idlnk-deq"[]{};'"l";"map"[]{"lambda"[]{"p"."snd"[]{'"p"}};"fst"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}


interactive nuprl_ma__sends__on_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("ma-sends-on"[]{'"M";'"l"} in "bool"[]{}) }

define unfold_sends__on__pair : "sends-on-pair"[]{'"s";'"l";'"tg"} <-->
      "reduce"[]{"lambda"[]{"kl"."lambda"[]{"x"."bor"[]{"band"[]{(("eqof"[]{"idlnk-deq"[]{}} "snd"[]{'"kl"}) '"l");"deq-member"[]{"id-deq"[]{};'"tg";"map"[]{"lambda"[]{"z"."fst"[]{'"z"}};("snd"[]{'"s"} '"kl")}}};'"x"}}};"bfalse"[]{};"fst"[]{'"s"}}


interactive nuprl_sends__on__pair_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"s" in "fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("sends-on-pair"[]{'"s";'"l";'"tg"} in "bool"[]{}) }

interactive nuprl_assert__sends__on__pair   :
   [wf] sequent { <H> >- '"s" in "fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"sends-on-pair"[]{'"s";'"l";'"tg"}};"exists"[]{"Knd"[]{};"k"."cand"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"pair"[]{'"k";'"l"};'"s"}};"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};"fpf-ap"[]{'"s";"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"pair"[]{'"k";'"l"}}};"Id"[]{}}}}} }

define unfold_ma__dout2 : "ma-dout2"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}


interactive nuprl_ma__dout2_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-dout2"[]{'"M";'"l";'"tg"} in "univ"[level:l]{}) }

interactive nuprl_ma__dout2_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"ma-dout2"[]{'"M";'"l";'"tg"}} }

interactive nuprl_ma__dout2__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "subtype"[]{"ma-dout2"[]{'"M";'"l";'"tg"};"ma-dout"[]{'"M";'"l";'"tg"}} }

define unfold_ma__frame : "ma-frame"[]{'"M";'"k";'"x"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};'"x";"x", "L"."assert"[]{"deq-member"[]{"Kind-deq"[]{};'"k";'"L"}}}


interactive nuprl_ma__frame_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-frame"[]{'"M";'"k";'"x"} in "univ"[level:l]{}) }

define unfold_ma__sframe : "ma-sframe"[]{'"M";'"k";'"l";'"tg"} <-->
      "fpf-val"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"pair"[]{'"l";'"tg"};"x", "L"."assert"[]{"deq-member"[]{"Kind-deq"[]{};'"k";'"L"}}}


interactive nuprl_ma__sframe_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-sframe"[]{'"M";'"k";'"l";'"tg"} in "univ"[level:l]{}) }

define unfold_ma__sub : "ma-sub"[level:l]{'"M1";'"M2"} <-->
      "cand"[]{"and"[]{"fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-sub"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"x"."fpf-cap"[]{"fst"[]{'"M2"};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M2"}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};""."univ"[level:l]{}}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"and"[]{"fpf-sub"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M2"}};"fst"[]{'"kx"}};""."fpf-cap"[]{"fst"[]{'"M2"};"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"and"[]{"fpf-sub"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M2"}};"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M2"}};"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-sub"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}}}}}}


interactive nuprl_ma__sub_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-sub"[level:l]{'"M1";'"M2"} in "univ"[level':l]{}) }

interactive nuprl_ma__sub_transitivity  '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M3" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M2";'"M3"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M3"} }

interactive nuprl_ma__sub_weakening   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"msga"[level:l]{};'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }

define unfold_mk__ma : "mk-ma"[]{'"ds";'"da";'"init";'"pre";'"ef";'"send";'"frame";'"sframe"} <-->
      "pair"[]{'"ds";"pair"[]{'"da";"pair"[]{'"init";"pair"[]{'"pre";"pair"[]{'"ef";"pair"[]{'"send";"pair"[]{'"frame";"pair"[]{'"sframe";"it"[]{}}}}}}}}}


interactive nuprl_mk__ma_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent { <H> >- '"pre" in "fpf"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"locl"[]{'"a"}};""."univ"[level:l]{}}}} }  -->
   [wf] sequent { <H> >- '"ef" in "fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kx"}};""."fpf-cap"[]{'"ds";"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}}} }  -->
   [wf] sequent { <H> >- '"send" in "fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}}} }  -->
   [wf] sequent { <H> >- '"frame" in "fpf"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}}} }  -->
   [wf] sequent { <H> >- '"sframe" in "fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}}} }  -->
   sequent { <H> >- ("mk-ma"[]{'"ds";'"da";'"init";'"pre";'"ef";'"send";'"frame";'"sframe"} in "msga"[level:l]{}) }

define unfold_ma__empty : "ma-empty"[]{} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__empty_wf {| intro[] |}   :
   sequent { <H> >- ("ma-empty"[]{} in "msga"[level:l]{}) }

define unfold_ma__is__empty : "ma-is-empty"[]{'"M"} <-->
      "band"[]{"fpf-is-empty"[]{"fst"[]{'"M"}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{'"M"}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{'"M"}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}}}}}}}}


interactive nuprl_ma__is__empty_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-is-empty"[]{'"M"} in "bool"[]{}) }

interactive nuprl_assert__ma__is__empty   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"ma-is-empty"[]{'"M"}};"equal"[]{"msga"[level:l]{};'"M";"ma-empty"[]{}}} }

interactive nuprl_ma__empty__is__empty   :
   sequent { <H> >- "assert"[]{"ma-is-empty"[]{"ma-empty"[]{}}} }

interactive nuprl_ma__empty__sub   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{"ma-empty"[]{};'"M"} }

interactive nuprl_ma__is__empty__sub   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "assert"[]{"ma-is-empty"[]{'"A"}} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"A";'"B"} }

interactive nuprl_ma__empty__tag__type   :
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "ma-tag-type"[level:l]{"ma-empty"[]{};'"tg";'"T"} }

define unfold_ma__compatible__decls : "ma-compatible-decls"[level:l]{'"M1";'"M2"} <-->
      "and"[]{"fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}}}


interactive nuprl_ma__compatible__decls_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-compatible-decls"[level:l]{'"M1";'"M2"} in "univ"[level':l]{}) }

define unfold_ma__join : "ma-join"[]{'"M1";'"M2"} <-->
      "mk-ma"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"fpf-join"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"fpf-join"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-join"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}


interactive nuprl_ma__join_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- ("ma-join"[]{'"M1";'"M2"} in "msga"[level:l]{}) }

interactive nuprl_ma__comp__decls__join   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"C";"ma-join"[]{'"A";'"B"}} }

interactive nuprl_ma__join__assoc   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "ma-compatible-decls"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "equal"[]{"msga"[level:l]{};"ma-join"[]{'"A";"ma-join"[]{'"B";'"C"}};"ma-join"[]{"ma-join"[]{'"A";'"B"};'"C"}} }

interactive nuprl_ma__join__sends__on univ[level:l]  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"ma-sends-on"[]{"ma-join"[]{'"M1";'"M2"};'"l"}};"or"[]{"assert"[]{"ma-sends-on"[]{'"M1";'"l"}};"assert"[]{"ma-sends-on"[]{'"M2";'"l"}}}} }

interactive nuprl_ma__sub__join__left   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";"ma-join"[]{'"M1";'"M2"}} }

interactive nuprl_ma__valtype__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da'" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-sub"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"da'"} }  -->
   sequent { <H> >- "subtype"[]{"ma-valtype"[]{'"da'";'"k"};"ma-valtype"[]{'"da";'"k"}} }

interactive nuprl_ma__state__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"ltg"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds'" in "fpf"[]{"Id"[]{};"ltg"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"ds'"} }  -->
   sequent { <H> >- "subtype"[]{"ma-state"[]{'"ds'"};"ma-state"[]{'"ds"}} }

interactive nuprl_ma__state__subtype2 univ[level:l]  :
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"ltg"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds'" in "fpf"[]{"Id"[]{};"ltg"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"ds'"} }  -->
   sequent { <H> >- "subtype"[]{"ma-state"[]{'"ds'"};"ma-state"[]{'"ds"}} }

define unfold_ma__compatible : "ma-compatible"[level:l]{'"M1";'"M2"} <-->
      "and"[]{"ma-compatible-decls"[level:l]{'"M1";'"M2"};"and"[]{"fpf-compatible"[]{"Id"[]{};"x"."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-compatible"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"fpf-cap"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};""."univ"[level:l]{}}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"and"[]{"fpf-compatible"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"ma-valtype"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fst"[]{'"kx"}};""."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"and"[]{"fpf-compatible"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"ma-valtype"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"and"[]{"fpf-compatible"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-compatible"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"lt"."list"[]{"Knd"[]{}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}}}}}}


interactive nuprl_ma__compatible_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-compatible"[level:l]{'"M1";'"M2"} in "univ"[level':l]{}) }

interactive nuprl_ma__compatible__symmetry   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M2";'"M1"} }

interactive nuprl_ma__compatible__self   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M";'"M"} }

interactive nuprl_ma__sub__join__right   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M2";"ma-join"[]{'"M1";'"M2"}} }

interactive nuprl_ma__empty__compatible__left   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma__empty__compatible__right   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"A";"ma-empty"[]{}} }

define unfold_ma__single__init : "ma-single-init"[]{'"x";'"t";'"v"} <-->
      "mk-ma"[]{"fpf-single"[]{'"x";'"t"};"fpf-empty"[]{};"fpf-single"[]{'"x";'"v"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__init_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- ("ma-single-init"[]{'"x";'"t";'"v"} in "msga"[level:l]{}) }

define unfold_ma__single__frame : "ma-single-frame"[]{'"L";'"t";'"x"} <-->
      "mk-ma"[]{"fpf-single"[]{'"x";'"t"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{'"x";'"L"};"fpf-empty"[]{}}


interactive nuprl_ma__single__frame_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ma-single-frame"[]{'"L";'"t";'"x"} in "msga"[level:l]{}) }

define unfold_ma__single__sframe : "ma-single-sframe"[]{'"L";'"l";'"tg"} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"l";'"tg"};'"L"}}


interactive nuprl_ma__single__sframe_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- ("ma-single-sframe"[]{'"L";'"l";'"tg"} in "msga"[level:l]{}) }

define unfold_ma__single__effect : "ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"} <-->
      "mk-ma"[]{'"ds";'"da";"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"k";'"x"};'"f"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__effect_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": "ma-valtype"[]{'"da";'"k"} >- '"f" '"x" '"x1" in "fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}} }  -->
   sequent { <H> >- ("ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"} in "msga"[level:l]{}) }

define unfold_ma__single__effect0 : "ma-single-effect0"[]{'"x";'"A";'"k";'"T";'"f"} <-->
      "ma-single-effect"[]{"fpf-single"[]{'"x";'"A"};"fpf-single"[]{'"k";'"T"};'"k";'"x";"lambda"[]{"s"."lambda"[]{"v".(('"f" ('"s" '"x")) '"v")}}}


interactive nuprl_ma__single__effect0_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"f" '"x" '"x1" in '"A" }  -->
   sequent { <H> >- ("ma-single-effect0"[]{'"x";'"A";'"k";'"T";'"f"} in "msga"[level:l]{}) }

define unfold_ma__single__effect1 : "ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"} <-->
      "ma-single-effect"[]{"fpf-join"[]{"id-deq"[]{};"fpf-single"[]{'"x";'"A"};"fpf-single"[]{'"y";'"B"}};"fpf-single"[]{'"k";'"T"};'"k";'"x";"lambda"[]{"s"."lambda"[]{"v".((('"f" ('"s" '"x")) ('"s" '"y")) '"v")}}}


interactive nuprl_ma__single__effect1_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B";"x2": '"T" >- '"f" '"x" '"x1" '"x2" in '"A" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"y";'"x"}} }  -->
   sequent { <H> >- ("ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"} in "msga"[level:l]{}) }

define unfold_ma__single__sends : "ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"} <-->
      "mk-ma"[]{'"ds";'"da";"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"k";'"l"};'"f"};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__sends_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- ("ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"} in "msga"[level:l]{}) }

define unfold_ma__single__sends0 : "ma-single-sends0"[]{'"B";'"T";'"a";'"l";'"tg";'"f"} <-->
      "ma-single-sends"[]{"fpf-empty"[]{};"fpf-join"[]{"Kind-deq"[]{};"fpf-single"[]{'"a";'"B"};"fpf-single"[]{"rcv"[]{'"l";'"tg"};'"T"}};'"a";'"l";"cons"[]{"pair"[]{'"tg";"lambda"[]{"s"."lambda"[]{"v".('"f" '"v")}}};"nil"[]{}}}


interactive nuprl_ma__single__sends0_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in "list"[]{'"T"} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};'"a";"rcv"[]{'"l";'"tg"}}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   sequent { <H> >- ("ma-single-sends0"[]{'"B";'"T";'"a";'"l";'"tg";'"f"} in "msga"[level:l]{}) }

define unfold_ma__single__sends1 : "ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"a";'"l";'"tg";'"f"} <-->
      "ma-single-sends"[]{"fpf-single"[]{'"x";'"A"};"fpf-join"[]{"Kind-deq"[]{};"fpf-single"[]{'"a";'"B"};"fpf-single"[]{"rcv"[]{'"l";'"tg"};'"T"}};'"a";'"l";"cons"[]{"pair"[]{'"tg";"lambda"[]{"s"."lambda"[]{"v".(('"f" ('"s" '"x")) '"v")}}};"nil"[]{}}}


define unfold_ma__single__pre : "ma-single-pre"[]{'"ds";'"a";'"T";'"P"} <-->
      "mk-ma"[]{'"ds";"fpf-single"[]{"locl"[]{'"a"};'"T"};"fpf-empty"[]{};"fpf-single"[]{'"a";'"P"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__pre_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ma-single-pre"[]{'"ds";'"a";'"T";'"P"} in "msga"[level:l]{}) }

define unfold_ma__single__pre1 : "ma-single-pre1"[]{'"x";'"A";'"a";'"T";"y", "v".'"P"['"y";'"v"]} <-->
      "ma-single-pre"[]{"fpf-single"[]{'"x";'"A"};'"a";'"T";"lambda"[]{"s", "v".'"P"[('"s" '"x");'"v"]}}


interactive nuprl_ma__single__pre1_wf {| intro[] |}  '"T" '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"x"  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ma-single-pre1"[]{'"x";'"A";'"a";'"T";"x", "v".'"P"['"x";'"v"]} in "msga"[level:l]{}) }

define unfold_ma__single__pre__true : "ma-single-pre-true"[]{'"a"} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{'"a";"lambda"[]{"s"."lambda"[]{"v"."true"[]{}}}};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__pre__true_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-single-pre-true"[]{'"a"} in "msga"[level:l]{}) }

define unfold_ma__single__pre__init : "ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"} <-->
      "mk-ma"[]{'"ds";"fpf-single"[]{"locl"[]{'"a"};'"T"};'"init";"fpf-single"[]{'"a";'"P"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


interactive nuprl_ma__single__pre__init_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent { <H> >- ("ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"} in "msga"[level:l]{}) }

define unfold_ma__single__pre__init1 : "ma-single-pre-init1"[]{'"x";'"T";'"c";'"a";'"T'";"y", "v".'"P"['"y";'"v"]} <-->
      "ma-single-pre-init"[]{"fpf-single"[]{'"x";'"T"};"fpf-single"[]{'"x";'"c"};'"a";'"T'";"lambda"[]{"s"."lambda"[]{"v".'"P"[('"s" '"x");'"v"]}}}


interactive nuprl_ma__single__pre__init1_wf {| intro[] |}  '"T" '"T'" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"c" '"x"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T'" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T'" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ma-single-pre-init1"[]{'"x";'"T";'"c";'"a";'"T'";"x", "v".'"P"['"x";'"v"]} in "msga"[level:l]{}) }

define unfold_ma__feasible : "ma-feasible"[]{'"M"} <-->
      "and"[]{"fpf-all"[]{"Id"[]{};"id-deq"[]{};"fst"[]{'"M"};"x", "T".'"T"};"and"[]{"fpf-all"[]{"Knd"[]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M"}};"k", "T"."decidable"[]{'"T"}};"and"[]{"fpf-all"[]{"Id"[]{};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};"a", "p"."all"[]{"ma-state"[]{"fst"[]{'"M"}};"s"."decidable"[]{"exists"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};"v".(('"p" '"s") '"v")}}}};"and"[]{"fpf-all"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"kx", "ef"."ma-frame"[]{'"M";"fst"[]{'"kx"};"snd"[]{'"kx"}}};"fpf-all"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"kl", "snd"."all"[]{"Id"[]{};"tg"."implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"snd"};"Id"[]{}};"ma-sframe"[]{'"M";"fst"[]{'"kl"};"snd"[]{'"kl"};'"tg"}}}}}}}}


interactive nuprl_ma__feasible_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-feasible"[]{'"M"} in "univ"[level':l]{}) }

interactive nuprl_ma__empty__feasible   :
   sequent { <H> >- "ma-feasible"[]{"ma-empty"[]{}} }

define unfold_ma__frame__compatible : "ma-frame-compatible"[]{'"A";'"B"} <-->
      "all"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."and"[]{"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};'"kx";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kx"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}};"id-deq"[]{};"snd"[]{'"kx"}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};'"kx";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kx"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}};"id-deq"[]{};"snd"[]{'"kx"}}}}}}}}}


interactive nuprl_ma__frame__compatible_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-frame-compatible"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_ma__frame__compatible__self univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";'"A"} }

define unfold_ma__sframe__compatible : "ma-sframe-compatible"[]{'"A";'"B"} <-->
      "all"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."all"[]{"Id"[]{};"tg"."and"[]{"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}};"implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl"}};"Id"[]{}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kl"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}};"implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl"}};"Id"[]{}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kl"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"}}}}}}}}}}}


interactive nuprl_ma__sframe__compatible_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-sframe-compatible"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_ma__sframe__compatible__self univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";'"A"} }

interactive nuprl_ma__empty__frame__compatible__left univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma__empty__sframe__compatible__right univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";"ma-empty"[]{}} }

interactive nuprl_ma__empty__frame__compatible__right univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";"ma-empty"[]{}} }

interactive nuprl_ma__empty__sframe__compatible__left univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma__compatible__join   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"C";'"B"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"C";'"B"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"ma-compatible"[level:l]{'"C";"ma-join"[]{'"A";'"B"}};"and"[]{"ma-frame-compatible"[]{'"C";"ma-join"[]{'"A";'"B"}};"ma-sframe-compatible"[]{'"C";"ma-join"[]{'"A";'"B"}}}}} }

define unfold_ma__compat : "ma-compat"[level:l]{'"A";'"B"} <-->
      "and"[]{"ma-compatible"[level:l]{'"A";'"B"};"and"[]{"ma-frame-compatible"[]{'"A";'"B"};"ma-sframe-compatible"[]{'"A";'"B"}}}


interactive nuprl_ma__compat_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("ma-compat"[level:l]{'"A";'"B"} in "univ"[level':l]{}) }

interactive nuprl_ma__compat__self   :
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"B";'"B"} }

interactive nuprl_ma__compat__symmetry   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"B";'"A"} }

interactive nuprl_ma__empty__compat__left   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma__empty__compat__right   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"A";"ma-empty"[]{}} }

define unfold_ma__join__list : "ma-join-list"[]{'"L"} <-->
      "reduce"[]{"lambda"[]{"A"."lambda"[]{"B"."ma-join"[]{'"A";'"B"}}};"ma-empty"[]{};'"L"}


interactive nuprl_ma__join__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-feasible"[]{'"A"} }  -->
   sequent { <H> >- "ma-feasible"[]{'"B"} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-join"[]{'"A";'"B"}} }

interactive nuprl_ma__compat__join   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"C";"ma-join"[]{'"A";'"B"}} }

interactive nuprl_ma__compat__join2   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"A";'"C"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"B";'"C"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-join"[]{'"A";'"B"};'"C"} }

interactive nuprl_ma__join__list__property   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "and"[]{("ma-join-list"[]{'"L"} in "msga"[level:l]{});"all"[]{"msga"[level:l]{};"M"."implies"[]{"l_all"[]{'"L";"msga"[level:l]{};"B"."ma-compat"[level:l]{'"M";'"B"}};"ma-compat"[level:l]{'"M";"ma-join-list"[]{'"L"}}}}} }

interactive nuprl_ma__join__list_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- ("ma-join-list"[]{'"L"} in "msga"[level:l]{}) }

interactive nuprl_ma__sub__join__list   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "mem"[]{'"M";'"L";"msga"[level:l]{}} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M";"ma-join-list"[]{'"L"}} }

interactive nuprl_ma__join__list__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"A"."ma-feasible"[]{'"A"}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-join-list"[]{'"L"}} }

interactive nuprl_ma__join__list__compat   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"B"."ma-compat"[level:l]{'"M";'"B"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{'"M";"ma-join-list"[]{'"L"}} }

interactive nuprl_ma__join__list__compat2   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"B"."ma-compat"[level:l]{'"B";'"M"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-join-list"[]{'"L"};'"M"} }

interactive nuprl_ma__join__declm univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"ma-declm"[]{"ma-join"[]{'"A";'"B"};'"l";'"tg"};"or"[]{"ma-declm"[]{'"A";'"l";'"tg"};"ma-declm"[]{'"B";'"l";'"tg"}}} }

interactive nuprl_ma__join__list__declm   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "iff"[]{"ma-declm"[]{"ma-join-list"[]{'"L"};'"l";'"tg"};"l_exists"[]{'"L";"msga"[level:l]{};"M"."ma-declm"[]{'"M";'"l";'"tg"}}} }

interactive nuprl_ma__join__list__declm2 univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "iff"[]{"ma-declm"[]{"ma-join-list"[]{'"L"};'"l";'"tg"};"assert"[]{"reduce"[]{"lambda"[]{"M"."lambda"[]{"x"."bor"[]{"fpf-dom"[]{"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"fst"[]{"snd"[]{'"M"}}};'"x"}}};"bfalse"[]{};'"L"}}} }

interactive_rw nuprl_ma__join__list__din univ[level:l]  :
   ('"tg" in "Id"[]{}) -->
   ('"l" in "IdLnk"[]{}) -->
   ('"L" in "list"[]{"msga"[level:l]{}}) -->
   "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} -->
   "ma-din"[]{"ma-join-list"[]{'"L"};'"l";'"tg"} <--> "reduce"[]{"lambda"[]{"M"."lambda"[]{"x"."ifthenelse"[]{"fpf-dom"[]{"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"fst"[]{"snd"[]{'"M"}}};"ma-din"[]{'"M";'"l";'"tg"};'"x"}}};"top"[]{};'"L"}

interactive_rw nuprl_ma__join__list__dout univ[level:l]  :
   ('"tg" in "Id"[]{}) -->
   ('"l" in "IdLnk"[]{}) -->
   ('"L" in "list"[]{"msga"[level:l]{}}) -->
   "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"} -->
   "ma-dout"[]{"ma-join-list"[]{'"L"};'"l";'"tg"} <--> "reduce"[]{"lambda"[]{"M"."lambda"[]{"x"."ifthenelse"[]{"fpf-dom"[]{"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"fst"[]{"snd"[]{'"M"}}};"ma-dout"[]{'"M";'"l";'"tg"};'"x"}}};"void"[]{};'"L"}

define unfold_msg__form : "msg-form"[level:l]{} <-->
      "prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Knd"[]{};"x"."univ"[level:l]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"x"."top"[]{}};""."top"[]{}}}}}}}}}


interactive nuprl_msg__form_wf {| intro[] |}   :
   sequent { <H> >- ("msg-form"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_msg__form_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"msg-form"[level:l]{}} }

interactive nuprl_msga__sub__msg__form   :
   sequent { <H> >- "subtype"[]{"msga"[level:l]{};"msg-form"[level:l]{}} }

interactive nuprl_ma__outlinks__wf2   :
   [wf] sequent { <H> >- '"M" in "msg-form"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-outlinks"[]{'"M";'"i"} in "list"[]{"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}}) }

interactive nuprl_msg__form__join   :
   [wf] sequent { <H> >- '"A" in "msg-form"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msg-form"[level:l]{} }  -->
   sequent { <H> >- ("ma-join"[]{'"A";'"B"} in "msg-form"[level:l]{}) }

interactive nuprl_msg__form__join__list   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- ("ma-join-list"[]{'"L"} in "msg-form"[level:l]{}) }

interactive nuprl_ma__is__empty_wf_join {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- ("ma-is-empty"[]{"ma-join-list"[]{'"L"}} in "bool"[]{}) }

interactive_rw nuprl_ma__join__list__is__empty univ[level:l]  :
   ('"L" in "list"[]{"msga"[level:l]{}}) -->
   "ma-is-empty"[]{"ma-join-list"[]{'"L"}} <--> "reduce"[]{"lambda"[]{"M"."lambda"[]{"x"."band"[]{"ma-is-empty"[]{'"M"};'"x"}}};"btrue"[]{};'"L"}

interactive nuprl_assert__ma__join__list__is__empty univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"ma-is-empty"[]{"ma-join-list"[]{'"L"}}};"reduce"[]{"lambda"[]{"M"."lambda"[]{"x"."and"[]{"assert"[]{"ma-is-empty"[]{'"M"}};'"x"}}};"true"[]{};'"L"}} }

interactive nuprl_ma__outlinks__join   :
   [wf] sequent { <H> >- '"A" in "msg-form"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msg-form"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ltg" in "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "mem"[]{'"ltg";"ma-outlinks"[]{"ma-join"[]{'"A";'"B"};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}} }  -->
   sequent { <H> >- "or"[]{"mem"[]{'"ltg";"ma-outlinks"[]{'"A";'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}};"mem"[]{'"ltg";"ma-outlinks"[]{'"B";'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}}}} }

interactive nuprl_ma__outlinks__join__list  "lambda"[]{"x".'"P"['"x"]} '"i" '"L"  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"M"."l_all"[]{"ma-outlinks"[]{'"M";'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}};"ltg".'"P"['"ltg"]}} }  -->
   sequent { <H> >- "l_all"[]{"ma-outlinks"[]{"ma-join-list"[]{'"L"};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}};"ltg".'"P"['"ltg"]} }

interactive nuprl_sub__join__list__din univ[level:l]  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"M"."subtype"[]{'"T";"ma-din"[]{'"M";'"l";'"tg"}}} }  -->
   sequent { <H> >- "subtype"[]{'"T";"ma-din"[]{"ma-join-list"[]{'"L"};'"l";'"tg"}} }

interactive nuprl_ma__join__list__tag__type   :
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msga"[level:l]{};"A"."ma-tag-type"[level:l]{'"A";'"tg";'"T"}} }  -->
   sequent { <H> >- "ma-tag-type"[level:l]{"ma-join-list"[]{'"L"};'"tg";'"T"} }

interactive nuprl_ma__send__send__val univ[level:l]  :
   [wf] sequent { <H> >- '"MA" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"MA"} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"vaal" in "ma-v"[]{'"MA";'"k"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"} }  -->
   sequent { <H> >- "ma-send"[]{'"MA";'"k";'"l";'"s";'"vaal";"map"[]{"lambda"[]{"x"."snd"[]{'"x"}};"filter"[]{"lambda"[]{"ms".(("eqof"[]{"idlnk-deq"[]{}} "mlnk"[]{'"ms"}) '"l")};"ma-send-val"[]{'"MA";'"k";'"s";'"vaal"}}};'"i"} }

interactive_rw nuprl_ma__send__val__nil univ[level:l]  :
   ('"MA" in "msga"[level:l]{}) -->
   ('"s" in "ma-st"[]{'"MA"}) -->
   ('"k" in "Knd"[]{}) -->
   ('"l" in "IdLnk"[]{}) -->
   ('"vaal" in "ma-v"[]{'"MA";'"k"}) -->
   "not"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"pair"[]{'"k";'"l"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"MA"}}}}}}}}} -->
   "filter"[]{"lambda"[]{"ms".(("eqof"[]{"idlnk-deq"[]{}} "mlnk"[]{'"ms"}) '"l")};"ma-send-val"[]{'"MA";'"k";'"s";'"vaal"}} <--> "nil"[]{}

interactive_rw nuprl_ma__send__val__nil2 univ[level:l]  :
   ('"MA" in "msga"[level:l]{}) -->
   ('"s" in "ma-st"[]{'"MA"}) -->
   ('"k" in "Knd"[]{}) -->
   ('"l" in "IdLnk"[]{}) -->
   ('"vaal" in "ma-v"[]{'"MA";'"k"}) -->
   "not"[]{"assert"[]{"ma-sends-on"[]{'"MA";'"l"}}} -->
   "filter"[]{"lambda"[]{"ms".(("eqof"[]{"idlnk-deq"[]{}} "mlnk"[]{'"ms"}) '"l")};"ma-send-val"[]{'"MA";'"k";'"s";'"vaal"}} <--> "nil"[]{}

define unfold_ma__rename : "ma-rename"[]{'"rx";'"ra";'"rt";'"M"} <-->
      "mk-ma"[]{"fpf-rename"[]{"id-deq"[]{};'"rx";"fst"[]{'"M"}};"fpf-rename"[]{"Kind-deq"[]{};"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};"fst"[]{"snd"[]{'"M"}}};"fpf-rename"[]{"id-deq"[]{};'"rx";"fst"[]{"snd"[]{"snd"[]{'"M"}}}};"fpf-rename"[]{"id-deq"[]{};'"ra";"fpf-compose"[]{"lambda"[]{"f"."lambda"[]{"s"."lambda"[]{"v".(('"f" "compose"[]{'"s";'"rx"}) '"v")}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"fpf-rename"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"lambda"[]{"p"."pair"[]{"kind-rename"[]{'"ra";'"rt";"fst"[]{'"p"}};('"rx" "snd"[]{'"p"})}};"fpf-compose"[]{"lambda"[]{"f"."lambda"[]{"s"."lambda"[]{"v".(('"f" "compose"[]{'"s";'"rx"}) '"v")}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};"fpf-rename"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"lambda"[]{"p"."pair"[]{"kind-rename"[]{'"ra";'"rt";"fst"[]{'"p"}};"snd"[]{'"p"}}};"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"p"."pair"[]{('"rt" "fst"[]{'"p"});"lambda"[]{"s"."lambda"[]{"v".(("snd"[]{'"p"} "compose"[]{'"s";'"rx"}) '"v")}}}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"fpf-rename"[]{"id-deq"[]{};'"rx";"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}};"fpf-rename"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"lambda"[]{"p"."pair"[]{"fst"[]{'"p"};('"rt" "snd"[]{'"p"})}};"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}}}


interactive nuprl_ma__rename_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rx" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"rx"} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"ra"} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"rt"} }  -->
   sequent { <H> >- ("ma-rename"[]{'"rx";'"ra";'"rt";'"M"} in "msga"[level:l]{}) }

interactive nuprl_w__withlnk_wf_ma {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"mss" in "list"[]{"ma-msg"[]{'"M"}} }  -->
   sequent { <H> >- ("w-withlnk"[]{'"l";'"mss"} in "list"[]{"prod"[]{"Id"[]{};"tg"."ma-dout"[]{'"M";'"l";'"tg"}}}) }

interactive nuprl_msga__at__sub__left   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M";'"M1"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M";"ma-join"[]{'"M1";'"M2"}} }

interactive nuprl_msga__at__sub__right   :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M";'"M2"} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M";"ma-join"[]{'"M1";'"M2"}} }

interactive nuprl_ma__single__init__feasible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"t" } }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma__single__frame__feasible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- '"t" }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma__single__sframe__feasible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__pre__init1__feasible  '"T" '"T'" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"c" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"c" in '"T" }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T'" >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H> >- '"T'" }  -->
   sequent { <H>; "u": '"T"  >- "decidable"[]{"exists"[]{'"T'";"v".'"P"['"u";'"v"]}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-pre-init1"[]{'"x";'"T";'"c";'"a";'"T'";"x", "v".'"P"['"x";'"v"]}} }

interactive nuprl_ma__single__pre__init__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "fpf-all"[]{"Id"[]{};"id-deq"[]{};'"ds";"x", "A".'"A"} }  -->
   sequent { <H>; "s": "ma-state"[]{'"ds"}  >- "decidable"[]{"exists"[]{'"T";"v".(('"P" '"s") '"v")}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__effect__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": "ma-valtype"[]{'"da";'"k"} >- '"f" '"x" '"x1" in "fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}} }  -->
   sequent { <H> >- "fpf-all"[]{"Id"[]{};"id-deq"[]{};'"ds";"x", "A".'"A"} }  -->
   sequent { <H> >- "fpf-all"[]{"Knd"[]{};"Kind-deq"[]{};'"da";"k", "A".'"A"} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__effect0__feasible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"f" '"x" '"x1" in '"A" }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-effect0"[]{'"x";'"A";'"k";'"T";'"f"}} }

interactive nuprl_ma__single__pre__true__feasible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-pre-true"[]{'"a"}} }

interactive nuprl_ma__single__pre__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- "fpf-all"[]{"Id"[]{};"id-deq"[]{};'"ds";"x", "A".'"A"} }  -->
   sequent { <H>; "s": "ma-state"[]{'"ds"}  >- "decidable"[]{"exists"[]{'"T";"v".(('"P" '"s") '"v")}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre1__feasible  '"T" '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"x"  :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H> >- '"T" }  -->
   sequent { <H> >- '"A" }  -->
   sequent { <H>; "a": '"A"  >- "decidable"[]{"exists"[]{'"T";"v".'"P"['"a";'"v"]}} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-pre1"[]{'"x";'"A";'"a";'"T";"x", "v".'"P"['"x";'"v"]}} }

interactive nuprl_ma__single__sends__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- "fpf-all"[]{"Id"[]{};"id-deq"[]{};'"ds";"x", "A".'"A"} }  -->
   sequent { <H> >- "fpf-all"[]{"Knd"[]{};"Kind-deq"[]{};'"da";"k", "A".'"A"} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }


(**** display forms ****)


dform nuprl_ma__state_df : except_mode[src] :: "ma-state"[]{'"ds"} =
   `"State(" slot{'"ds"} `")"


dform nuprl_ma__kind_df : except_mode[src] :: "ma-kind"[]{'"da"} =
   `"Kind(" slot{'"da"} `")"


dform nuprl_ma__valtype_df : except_mode[src] :: "ma-valtype"[]{'"da";'"k"} =
   `"Valtype(" slot{'"da"} `";" slot{'"k"} `")"


dform nuprl_ma__Msg_df : except_mode[src] :: "ma-Msg"[]{'"dout"} =
   `"Msg(" slot{'"dout"} `")"


dform nuprl_msga_df : except_mode[src] :: "msga"[level:l]{} =
   `"MsgA"


dform nuprl_ma__X_df : except_mode[src] :: "ma-X"[]{'"M"} =
   `"" slot{'"M"} `".X"


dform nuprl_ma__A_df : except_mode[src] :: "ma-A"[]{'"M"} =
   `"" slot{'"M"} `".A"


dform nuprl_ma__ds_df : except_mode[src] :: "ma-ds"[]{'"M";'"x"} =
   `"" slot{'"M"} `".ds(" slot{'"x"} `")"


dform nuprl_ma__da_df : except_mode[src] :: "ma-da"[]{'"M";'"a"} =
   `"" slot{'"M"} `".da(" slot{'"a"} `")"


dform nuprl_ma__declx_df : except_mode[src] :: "ma-declx"[]{'"M";'"x"} =
   `"" slot{'"x"} `" declared in " slot{'"M"} `""


dform nuprl_ma__declk_df : except_mode[src] :: "ma-declk"[]{'"M";'"k"} =
   `"" slot{'"k"} `" declared in " slot{'"M"} `""


dform nuprl_ma__decla_df : except_mode[src] :: "ma-decla"[]{'"M";'"a"} =
   `"" slot{'"a"} `" declared in " slot{'"M"} `""


dform nuprl_ma__declm_df : except_mode[src] :: "ma-declm"[]{'"M";'"l";'"tg"} =
   `"rcv(" slot{'"l"} `"," slot{'"tg"} `") declared in " slot{'"M"} `""


dform nuprl_da__outlink__f_df : except_mode[src] :: "da-outlink-f"[]{'"da";'"k"} =
   `"da-outlink-f(" slot{'"da"} `";" slot{'"k"} `")"


dform nuprl_da__outlinks_df : except_mode[src] :: "da-outlinks"[]{'"da";'"i"} =
   `"da-outlinks(" slot{'"da"} `";" slot{'"i"} `")"


dform nuprl_ma__outlinks_df : except_mode[src] :: "ma-outlinks"[]{'"M";'"i"} =
   `"ma-outlinks(" slot{'"M"} `";" slot{'"i"} `")"


dform nuprl_ma__din_df : except_mode[src] :: "ma-din"[]{'"M";'"l";'"tg"} =
   `"" slot{'"M"} `".din(" slot{'"l"} `"," slot{'"tg"} `")"


dform nuprl_ma__tag__type_df : except_mode[src] :: "ma-tag-type"[level:l]{'"M";'"tg";'"T"} =
   `"tag " slot{'"tg"} `" always has type " slot{'"T"} `" in " slot{'"M"} `""


dform nuprl_ma__dout_df : except_mode[src] :: "ma-dout"[]{'"M";'"l";'"tg"} =
   `"" slot{'"M"} `".dout(" slot{'"l"} `"," slot{'"tg"} `")"


dform nuprl_ma__init_df : except_mode[src] :: "ma-init"[]{'"M";'"x";'"v"} =
   `"" slot{'"M"} `".init(" slot{'"x"} `"," slot{'"v"} `")"


dform nuprl_ma__init__val_df : except_mode[src] :: "ma-init-val"[]{'"M";'"x";'"v"} =
   `"" slot{'"M"} `".init(" slot{'"x"} `")?" slot{'"v"} `""


dform nuprl_ma__st_df : except_mode[src] :: "ma-st"[]{'"M"} =
   `"" slot{'"M"} `".state"


dform nuprl_ma__msg_df : except_mode[src] :: "ma-msg"[]{'"M"} =
   `"" slot{'"M"} `".Msg"


dform nuprl_ma__k_df : except_mode[src] :: "ma-k"[]{'"M"} =
   `"" slot{'"M"} `".kind"


dform nuprl_ma__v_df : except_mode[src] :: "ma-v"[]{'"M";'"k"} =
   `"" slot{'"M"} `".V(" slot{'"k"} `")"


dform nuprl_ma__npre_df : except_mode[src] :: "ma-npre"[]{'"M";'"a";'"s"} =
   `"unsolvable " slot{'"M"} `".pre(" slot{'"a"} `"," slot{'"s"} `")"


dform nuprl_ma__pre_df : except_mode[src] :: "ma-pre"[]{'"M";'"a";'"s";'"v"} =
   `"" slot{'"M"} `".pre(" slot{'"a"} `"," szone sbreak["",""] ezone `"" slot{'"s"}
    `"," szone sbreak["",""] ezone `"" slot{'"v"} `")"


dform nuprl_ma__has__pre_df : except_mode[src] :: "ma-has-pre"[]{'"M";'"a"} =
   `"" slot{'"a"} `" in dom(" slot{'"M"} `".pre)"


dform nuprl_ma__ef_df : except_mode[src] :: "ma-ef"[]{'"M";'"k";'"x";'"s";'"v";'"w"} =
   `"" slot{'"M"} `".ef(" slot{'"k"} `"," szone sbreak["",""] ezone `"" slot{'"x"}
    `"," szone sbreak["",""] ezone `"" slot{'"s"} `"," szone sbreak["",""] ezone
    `"" slot{'"v"} `"," szone sbreak["",""] ezone `"" slot{'"w"} `")"


dform nuprl_ma__ef__val_df : except_mode[src] :: "ma-ef-val"[]{'"M";'"k";'"x";'"s";'"v";'"w"} =
   `"" slot{'"M"} `".ef(" slot{'"k"} `"," slot{'"x"} `"," slot{'"s"} `","
    slot{'"v"} `")?" slot{'"w"} `""


dform nuprl_tagged__list__messages_df : except_mode[src] :: "tagged-list-messages"[]{'"s";'"v";'"L"} =
   `"tagged-list-messages(" slot{'"s"} `";" slot{'"v"} `";" slot{'"L"} `")"


dform nuprl_tagged__messages_df : except_mode[src] :: "tagged-messages"[]{'"l";'"s";'"v";'"L"} =
   `"tagged-messages(" slot{'"l"} `";" slot{'"s"} `";" slot{'"v"} `";" slot{'"L"}
    `")"


dform nuprl_ma__send_df : except_mode[src] :: "ma-send"[]{'"M";'"k";'"l";'"s";'"v";'"ms";'"i"} =
   `"" slot{'"M"} `".send(" slot{'"k"} `";" szone sbreak["",""] ezone `""
    slot{'"l"} `";" szone sbreak["",""] ezone `"" slot{'"s"} `";" szone
    sbreak["",""] ezone `"" slot{'"v"} `";" szone sbreak["",""] ezone `""
    slot{'"ms"} `";" szone sbreak["",""] ezone `"" slot{'"i"} `")"


dform nuprl_ma__send__val_df : except_mode[src] :: "ma-send-val"[]{'"M";'"k";'"s";'"v"} =
   `"" slot{'"M"} `".sends(" slot{'"k"} `"," slot{'"s"} `"," slot{'"v"} `")"


dform nuprl_ma__sends__on_df : except_mode[src] :: "ma-sends-on"[]{'"M";'"l"} =
   `"" slot{'"M"} `" sends on link " slot{'"l"} `""


dform nuprl_sends__on__pair_df : except_mode[src] :: "sends-on-pair"[]{'"s";'"l";'"tg"} =
   `"sends-on-pair(" slot{'"s"} `";" slot{'"l"} `";" slot{'"tg"} `")"


dform nuprl_ma__dout2_df : except_mode[src] :: "ma-dout2"[]{'"M";'"l";'"tg"} =
   `"" slot{'"M"} `".dout2(" slot{'"l"} `";" slot{'"tg"} `")"


dform nuprl_ma__frame_df : except_mode[src] :: "ma-frame"[]{'"M";'"k";'"x"} =
   `"" slot{'"M"} `".frame(" szone sbreak["",""] ezone `"" slot{'"k"} `" affects"
    szone sbreak["",""] ezone `" " slot{'"x"} `")"


dform nuprl_ma__sframe_df : except_mode[src] :: "ma-sframe"[]{'"M";'"k";'"l";'"tg"} =
   `"" slot{'"M"} `".sframe(" szone sbreak["",""] ezone `"" slot{'"k"} `" sends"
    szone sbreak["",""] ezone `" <" slot{'"l"} `"," slot{'"tg"} `">)"


dform nuprl_ma__sub_df : except_mode[src] :: "ma-sub"[level:l]{'"M1";'"M2"} =
   `"ma-sub{i:l}(" slot{'"M1"} `";" slot{'"M2"} `")"

dform nuprl_ma__sub_df : except_mode[src] :: "ma-sub"[level:l]{'"M1";'"M2"} =
   `"" slot{'"M1"} `" " sqsubseteq `" " slot{'"M2"} `""


dform nuprl_mk__ma_df : except_mode[src] :: "mk-ma"[]{'"ds";'"da";'"init";'"pre";'"ef";'"send";'"frame";'"sframe"} =
   `"mk-ma(" slot{'"ds"} `";" sbreak["",""] `"" slot{'"da"} `";" sbreak["",""] `""
    slot{'"init"} `";" sbreak["",""] `"" slot{'"pre"} `";" sbreak["",""] `""
    slot{'"ef"} `";" sbreak["",""] `"" slot{'"send"} `";" sbreak["",""] `""
    slot{'"frame"} `";" sbreak["",""] `"" slot{'"sframe"} `")"


dform nuprl_ma__empty_df : except_mode[src] :: "ma-empty"[]{} =
   `""


dform nuprl_ma__is__empty_df : except_mode[src] :: "ma-is-empty"[]{'"M"} =
   `"ma-is-empty(" slot{'"M"} `")"


dform nuprl_ma__compatible__decls_df : except_mode[src] :: "ma-compatible-decls"[level:l]{'"M1";'"M2"} =
   `"" slot{'"M1"} `" ||decl " slot{'"M2"} `""


dform nuprl_ma__join_df : except_mode[src] :: "ma-join"[]{'"M1";'"M2"} =
   `"" slot{'"M1"} `" " szone sbreak["",""] ezone `"" oplus `" " slot{'"M2"} `""


dform nuprl_ma__compatible_df : except_mode[src] :: "ma-compatible"[level:l]{'"M1";'"M2"} =
   `"" slot{'"M1"} `" || " slot{'"M2"} `""


dform nuprl_ma__single__init_df : except_mode[src] :: "ma-single-init"[]{'"x";'"t";'"v"} =
   `"" slot{'"x"} `" : " slot{'"t"} `" initially " slot{'"x"} `" = " slot{'"v"} `""



dform nuprl_ma__single__frame_df : except_mode[src] :: "ma-single-frame"[]{'"L";'"t";'"x"} =
   `"only members of " slot{'"L"} `" affect " slot{'"x"} `" :" slot{'"t"} `""


dform nuprl_ma__single__sframe_df : except_mode[src] :: "ma-single-sframe"[]{'"L";'"l";'"tg"} =
   `"only " slot{'"L"} `" sends on (" slot{'"l"} `" with " slot{'"tg"} `")"


dform nuprl_ma__single__effect_df : except_mode[src] :: "ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"} =
   `"with declarations " sbreak["",""] `"ds:" slot{'"ds"} `"" sbreak["",""] `"da:"
    slot{'"da"} `"" sbreak["",""] `"effect of " slot{'"k"} `"(v) is " slot{'"x"}
    `" := " slot{'"f"} `" s v"


dform nuprl_ma__single__effect0_df : except_mode[src] :: "ma-single-effect0"[]{'"x";'"A";'"a";'"T";'"f"} =
   `"ma-single-effect0(" slot{'"x"} `";" slot{'"A"} `";" slot{'"a"} `";" slot{'"T"}
    `";" slot{'"f"} `")"


dform nuprl_ma__single__effect1_df : except_mode[src] :: "ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"} =
   `"ma-single-effect1(" slot{'"x"} `";" slot{'"A"} `";" slot{'"y"} `";" slot{'"B"}
    `";" slot{'"k"} `";" slot{'"T"} `";" slot{'"f"} `")"


dform nuprl_ma__single__sends_df : except_mode[src] :: "ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"} =
   `"with declarations " sbreak["",""] `"ds:" slot{'"ds"} `"" sbreak["",""] `"da:"
    slot{'"da"} `"" sbreak["",""] `"" slot{'"k"} `"(v) sends " slot{'"f"}
    `" s v on link " slot{'"l"} `""


dform nuprl_ma__single__sends0_df : except_mode[src] :: "ma-single-sends0"[]{'"B";'"T";'"a";'"l";'"tg";'"f"} =
   `"ma-single-sends0(" slot{'"B"} `";" slot{'"T"} `";" slot{'"a"} `";" slot{'"l"}
    `";" slot{'"tg"} `";" slot{'"f"} `")"


dform nuprl_ma__single__sends1_df : except_mode[src] :: "ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"a";'"l";'"tg";'"f"} =
   `"" slot{'"x"} `": " slot{'"A"} `"" sbreak["",""] `"" slot{'"a"} `": "
    slot{'"B"} `"" sbreak["",""] `"rcv(" slot{'"l"} `"," slot{'"tg"} `") : "
    slot{'"T"} `"" sbreak["",""] `"" slot{'"a"} `"(v) sends [" slot{'"tg"} `", "
    `"
   " `"" slot{'"f"} `"(" slot{'"x"} `", v)] on link " slot{'"l"} `"" `"
   " `""



dform nuprl_ma__single__pre_df : except_mode[src] :: "ma-single-pre"[]{'"ds";'"a";'"T";'"P"} =
   `"(with ds: " slot{'"ds"} `"" sbreak["",""] `" action " slot{'"a"} `":"
    slot{'"T"} `"" sbreak["",""] `" precondition " slot{'"a"} `"(v) is"
    sbreak["",""] `" " slot{'"P"} `" s v)"


dform nuprl_ma__single__pre1_df : except_mode[src] :: "ma-single-pre1"[]{'"x";'"A";'"a";'"T";"y", "v".'"P"} =
   `"ma-single-pre1(" slot{'"x"} `";" slot{'"A"} `";" slot{'"a"} `";" slot{'"T"}
    `";" slot{'"y"} `"," slot{'"v"} `"." slot{'"P"} `")"


dform nuprl_ma__single__pre__true_df : except_mode[src] :: "ma-single-pre-true"[]{'"a"} =
   `"precondition " slot{'"a"} `": True"


dform nuprl_ma__single__pre__init_df : except_mode[src] :: "ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"} =
   `"(with ds: " slot{'"ds"} `"" sbreak["",""] `" init: " slot{'"init"} `""
    sbreak["",""] `"action " slot{'"a"} `":" slot{'"T"} `"" sbreak["",""]
    `" precondition " slot{'"a"} `"(v) is" sbreak["",""] `" " slot{'"P"} `")"


dform nuprl_ma__single__pre__init1_df : except_mode[src] :: "ma-single-pre-init1"[]{'"x";'"T";'"c";'"a";'"T'";"y", "v".'"P"} =
   `"ma-single-pre-init1(" slot{'"x"} `";" slot{'"T"} `";" slot{'"c"} `";"
    slot{'"a"} `";" slot{'"T'"} `";" slot{'"y"} `"," slot{'"v"} `"." slot{'"P"}
    `")"


dform nuprl_ma__feasible_df : except_mode[src] :: "ma-feasible"[]{'"M"} =
   `"Feasible(" slot{'"M"} `")"


dform nuprl_ma__frame__compatible_df : except_mode[src] :: "ma-frame-compatible"[]{'"A";'"B"} =
   `"ma-frame-compatible(" slot{'"A"} `";" slot{'"B"} `")"


dform nuprl_ma__sframe__compatible_df : except_mode[src] :: "ma-sframe-compatible"[]{'"A";'"B"} =
   `"ma-sframe-compatible(" slot{'"A"} `";" slot{'"B"} `")"


dform nuprl_ma__compat_df : except_mode[src] :: "ma-compat"[level:l]{'"A";'"B"} =
   `"" slot{'"A"} `" ||+ " slot{'"B"} `""


dform nuprl_ma__join__list_df : except_mode[src] :: "ma-join-list"[]{'"L"} =
   `"" oplus `"(" slot{'"L"} `")"


dform nuprl_msg__form_df : except_mode[src] :: "msg-form"[level:l]{} =
   `"MsgAForm"


dform nuprl_ma__rename_df : except_mode[src] :: "ma-rename"[]{'"rx";'"ra";'"rt";'"M"} =
   `"ma-rename(" slot{'"rx"} `";" slot{'"ra"} `";" slot{'"rt"} `";" slot{'"M"} `")"



