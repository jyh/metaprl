extends Ma_message__automata

open Dtactic


define unfold_dsys : "dsys"[level:l]{} <-->
      "fun"[]{"Id"[]{};"i"."msga"[level:l]{}}


interactive nuprl_dsys_wf {| intro[] |}   :
   sequent { <H> >- ("dsys"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_dsys_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"dsys"[level:l]{}} }

define unfold_d__eq__Loc : "d-eq-Loc"[]{'"i";'"j"} <-->
      (("eqof"[]{"id-deq"[]{}} '"i") '"j")


interactive nuprl_d__eq__Loc_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   sequent { <H> >- ("d-eq-Loc"[]{'"i";'"j"} in "bool"[]{}) }

interactive nuprl_assert__d__eq__Loc   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"Id"[]{};'"i";'"j"};"assert"[]{"d-eq-Loc"[]{'"i";'"j"}}} }

define unfold_d__I : "d-I"[]{'"i"} <-->
      "lambda"[]{"l"."equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"}}


interactive nuprl_d__I_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("d-I"[]{'"i"} in "fun"[]{"IdLnk"[]{};""."univ"[level:l]{}}) }

define unfold_d__O : "d-O"[]{'"i"} <-->
      "lambda"[]{"l"."equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"}}


interactive nuprl_d__O_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("d-O"[]{'"i"} in "fun"[]{"IdLnk"[]{};""."univ"[level:l]{}}) }

define unfold_d__m : "d-m"[]{'"D";'"i"} <-->
      ('"D" '"i")


interactive nuprl_d__m_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("d-m"[]{'"D";'"i"} in "msga"[level:l]{}) }

define unfold_d__decl : "d-decl"[]{'"D";'"i"} <-->
      "w-action-dec"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};'"i"}


interactive nuprl_d__decl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("d-decl"[]{'"D";'"i"} in "fun"[]{"Knd"[]{};""."univ"[level:l]{}}) }

interactive nuprl_d__decl__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H>; "l": "IdLnk"[]{} ; "tg": "Id"[]{}  >- "subtype"[]{"ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}} }  -->
   sequent { <H> >- "subtype"[]{("d-decl"[]{'"D";'"i"} '"k");"ma-da"[]{"d-m"[]{'"D";'"i"};'"k"}} }

interactive nuprl_mlnk_wf_d {| intro[] |} univ[level:l] '"i" '"D"  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "ma-msg"[]{"d-m"[]{'"D";'"i"}} }  -->
   sequent { <H> >- ("mlnk"[]{'"m"} in "IdLnk"[]{}) }

define unfold_d__sub : "d-sub"[level:l]{'"D1";'"D2"} <-->
      "all"[]{"Id"[]{};"i"."ma-sub"[level:l]{"d-m"[]{'"D1";'"i"};"d-m"[]{'"D2";'"i"}}}


interactive nuprl_d__sub_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D1" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"D2" in "dsys"[level:l]{} }  -->
   sequent { <H> >- ("d-sub"[level:l]{'"D1";'"D2"} in "univ"[level':l]{}) }

interactive nuprl_d__sub__self   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D";'"D"} }

interactive nuprl_d__sub_transitivity  '"D2"  :
   [wf] sequent { <H> >- '"D1" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"D2" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"D3" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D1";'"D2"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D2";'"D3"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D1";'"D3"} }

define unfold_d__single__init : "d-single-init"[]{'"i";'"x";'"T";'"v"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-init"[]{'"x";'"T";'"v"};"ma-empty"[]{}}}


interactive nuprl_d__single__init_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("d-single-init"[]{'"i";'"x";'"T";'"v"} in "dsys"[level:l]{}) }

define unfold_d__single__frame : "d-single-frame"[]{'"i";'"L";'"t";'"x"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-frame"[]{'"L";'"t";'"x"};"ma-empty"[]{}}}


interactive nuprl_d__single__frame_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("d-single-frame"[]{'"i";'"L";'"t";'"x"} in "dsys"[level:l]{}) }

define unfold_d__single__sframe : "d-single-sframe"[]{'"i";'"L";'"l";'"tg"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-empty"[]{}}}


interactive nuprl_d__single__sframe_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("d-single-sframe"[]{'"i";'"L";'"l";'"tg"} in "dsys"[level:l]{}) }

define unfold_d__single__effect : "d-single-effect"[]{'"i";'"ds";'"da";'"k";'"x";'"f"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-empty"[]{}}}


interactive nuprl_d__single__effect_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": "ma-valtype"[]{'"da";'"k"} >- '"f" '"x" '"x1" in "fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}} }  -->
   sequent { <H> >- ("d-single-effect"[]{'"i";'"ds";'"da";'"k";'"x";'"f"} in "dsys"[level:l]{}) }

define unfold_d__single__sends : "d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-empty"[]{}}}


interactive nuprl_d__single__sends_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"ltg"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- ("d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"} in "dsys"[level:l]{}) }

define unfold_d__single__pre : "d-single-pre"[]{'"i";'"ds";'"a";'"T";'"P"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-empty"[]{}}}


interactive nuprl_d__single__pre_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("d-single-pre"[]{'"i";'"ds";'"a";'"T";'"P"} in "dsys"[level:l]{}) }

define unfold_d__single__pre__init : "d-single-pre-init"[]{'"i";'"ds";'"init";'"a";'"T";'"P"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-empty"[]{}}}


interactive nuprl_d__single__pre__init_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("d-single-pre-init"[]{'"i";'"ds";'"init";'"a";'"T";'"P"} in "dsys"[level:l]{}) }

interactive nuprl_ma__decla_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- ("ma-decla"[]{"d-m"[]{'"A";'"i"};'"a"} in "univ"[level:l]{}) }

interactive nuprl_decidable__ma__decla univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- "decidable"[]{"ma-decla"[]{"d-m"[]{'"A";'"i"};'"a"}} }

define unfold_d__feasible : "d-feasible"[]{'"D"} <-->
      "and"[]{"all"[]{"Id"[]{};"i"."ma-feasible"[]{"d-m"[]{'"D";'"i"}}};"and"[]{"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."subtype"[]{"ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}}}};"all"[]{"Id"[]{};"i"."finite-type"[]{"set"[]{"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"assert"[]{"ma-sends-on"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l"}}}}}}}}


interactive nuprl_d__feasible_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- ("d-feasible"[]{'"D"} in "univ"[level':l]{}) }

interactive nuprl_d__feasible__types univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "subtype"[]{"ifthenelse"[]{"eq_id"[]{"ldst"[]{'"l"};'"i"};"ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"void"[]{}};"ma-da"[]{"d-m"[]{'"D";'"i"};"rcv"[]{'"l";'"tg"}}} }

interactive nuprl_d__feasible__types2 univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "subtype"[]{"ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}} }

interactive nuprl_d__feasible__state univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "fun"[]{"Id"[]{};"i"."ma-st"[]{"d-m"[]{'"D";'"i"}}} }

interactive nuprl_d__feasible__dec univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "fun"[]{"Id"[]{};"j"."fun"[]{"Id"[]{};"b"."fun"[]{"ma-st"[]{"d-m"[]{'"D";'"j"}};"s"."decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"j"};'"b"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"j"};"locl"[]{'"b"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"j"};'"b";'"s";'"v"}}}}}}} }

interactive nuprl_round__robin   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"nat"[]{};"".'"T"};"f"."all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"L";'"T"};"all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"equal"[]{'"T";('"f" '"t'");'"x"}}}}}}} }

interactive nuprl_d__feasible__sched univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"Id"[]{};"i"."union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}}};"sched"."all"[]{"Id"[]{};"i"."and"[]{"all"[]{"IdLnk"[]{};"l"."implies"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"implies"[]{"assert"[]{"ma-sends-on"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l"}};"cand"[]{"assert"[]{"is_inl"[]{('"sched" '"i")}};"all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"cand"[]{"assert"[]{"is_inl"[]{("outl"[]{('"sched" '"i")} '"t'")}};"equal"[]{"IdLnk"[]{};"outl"[]{("outl"[]{('"sched" '"i")} '"t'")};'"l"}}}}}}}}};"all"[]{"Id"[]{};"a"."implies"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"cand"[]{"assert"[]{"is_inl"[]{('"sched" '"i")}};"all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"cand"[]{"assert"[]{"bnot"[]{"is_inl"[]{("outl"[]{('"sched" '"i")} '"t'")}}};"equal"[]{"Id"[]{};"outr"[]{("outl"[]{('"sched" '"i")} '"t'")};'"a"}}}}}}}}}}} }

define unfold_d__world__state : "d-world-state"[]{'"D";'"i"} <-->
      "prod"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};""."prod"[]{"action"[]{"d-decl"[]{'"D";'"i"}};""."list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}}}}


interactive nuprl_d__world__state_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("d-world-state"[]{'"D";'"i"} in "univ"[level:l]{}) }

interactive nuprl_d__world__state_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"d-world-state"[]{'"D";'"i"}} }

define unfold_stutter__state : "stutter-state"[]{'"s"} <-->
      "pair"[]{'"s";"pair"[]{"null-action"[]{};"nil"[]{}}}


interactive nuprl_stutter__state_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   sequent { <H> >- ("stutter-state"[]{'"s"} in "d-world-state"[]{'"D";'"i"}) }

define unfold_next__world__state : "next-world-state"[]{'"D";'"i";'"s";'"k";'"v"} <-->
      "pair"[]{"lambda"[]{"x"."ma-ef-val"[]{"d-m"[]{'"D";'"i"};'"k";'"x";'"s";'"v";('"s" '"x")}};"pair"[]{"doact"[]{'"k";'"v"};"filter"[]{"lambda"[]{"m"."eq_id"[]{"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"ma-send-val"[]{"d-m"[]{'"D";'"i"};'"k";'"s";'"v"}}}}


interactive nuprl_next__world__state_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"v" in ("d-decl"[]{'"D";'"i"} '"k") }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- ("next-world-state"[]{'"D";'"i";'"s";'"k";'"v"} in "d-world-state"[]{'"D";'"i"}) }

interactive nuprl_equal__d__world__states univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s1" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"s2" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"k2" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"v1" in ("d-decl"[]{'"D";'"i"} '"k1") }  -->
   [wf] sequent { <H> >- '"v2" in ("d-decl"[]{'"D";'"i"} '"k2") }  -->
   [wf] sequent { <H> >- '"m1" in "list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}} }  -->
   [wf] sequent { <H> >- '"m2" in "list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}} }  -->
   sequent { <H> >- "equal"[]{"d-world-state"[]{'"D";'"i"};"pair"[]{'"s1";"pair"[]{"doact"[]{'"k1";'"v1"};'"m1"}};"pair"[]{'"s2";"pair"[]{"doact"[]{'"k2";'"v2"};'"m2"}}} }  -->
   sequent { <H> >- "and"[]{"equal"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};'"s1";'"s2"};"and"[]{"equal"[]{"Knd"[]{};'"k1";'"k2"};"and"[]{"equal"[]{("d-decl"[]{'"D";'"i"} '"k1");'"v1";'"v2"};"equal"[]{"list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}};'"m1";'"m2"}}}} }

interactive nuprl_equal__next__world univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s1" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"s2" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"k2" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"v1" in ("d-decl"[]{'"D";'"i"} '"k1") }  -->
   [wf] sequent { <H> >- '"v2" in ("d-decl"[]{'"D";'"i"} '"k2") }  -->
   [wf] sequent { <H> >- '"m1" in "list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "equal"[]{"d-world-state"[]{'"D";'"i"};"pair"[]{'"s1";"pair"[]{"doact"[]{'"k1";'"v1"};'"m1"}};"next-world-state"[]{'"D";'"i";'"s2";'"k2";'"v2"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};'"s1";"lambda"[]{"x"."ma-ef-val"[]{"d-m"[]{'"D";'"i"};'"k2";'"x";'"s2";'"v2";('"s2" '"x")}}};"and"[]{"equal"[]{"Knd"[]{};'"k1";'"k2"};"and"[]{"equal"[]{("d-decl"[]{'"D";'"i"} '"k2");'"v1";'"v2"};"equal"[]{"list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}};'"m1";"filter"[]{"lambda"[]{"m"."eq_id"[]{"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"ma-send-val"[]{"d-m"[]{'"D";'"i"};'"k2";'"s2";'"v2"}}}}}}} }

define unfold_d__partial__world : "d-partial-world"[]{'"D";'"f";'"t'";'"s"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"fst"[]{(('"f" '"t") '"i")};('"s" '"i")}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"fst"[]{"snd"[]{(('"f" '"t") '"i")}};"null-action"[]{}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"lt_bool"[]{'"t";'"t'"};"snd"[]{"snd"[]{(('"f" '"t") '"i")}};"nil"[]{}}}};"it"[]{}}}}}}}


interactive nuprl_d__partial__world_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"s" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"t"};"i": "Id"[]{} >- '"f" '"x" '"i" in "d-world-state"[]{'"D";'"i"} }  -->
   sequent { <H> >- ("d-partial-world"[]{'"D";'"f";'"t";'"s"} in "world"[level:l]{}) }

define unfold_d__comp : "d-comp"[]{'"D";'"v";'"sched";'"dec"} <-->
      "lambda"[]{"t"."lambda"[]{"f"."let"[]{"lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(('"f" "sub"[]{'"t";"number"[1:n]{}}) '"i")}}};"s"."lambda"[]{"i"."let"[]{('"s" '"i");"si"."let"[]{"d-partial-world"[]{'"D";'"f";'"t";'"s"};"w"."let"[]{"decide"[]{('"sched" '"i");"f"."decide"[]{('"f" '"t");"l"."ifthenelse"[]{"band"[]{"d-eq-Loc"[]{"ldst"[]{'"l"};'"i"};"lt_bool"[]{"number"[0:n]{};"length"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"doact"[]{"rcv"[]{'"l";"mtag"[]{"hd"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"mval"[]{"hd"[]{"w-queue"[]{'"w";'"l";'"t"}}}};"null-action"[]{}};"a"."ifthenelse"[]{"is_inl"[]{((('"dec" '"i") '"a") '"si")};"doact"[]{"inr"[]{'"a"};"fst"[]{"snd"[]{"outl"[]{((('"dec" '"i") '"a") '"si")}}}};"null-action"[]{}}};"x"."null-action"[]{}};"a"."let"[]{"ifthenelse"[]{"is_inl"[]{'"a"};"nil"[]{};"filter"[]{"lambda"[]{"m"."eq_id"[]{"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"ma-send-val"[]{"d-m"[]{'"D";'"i"};"fst"[]{"outr"[]{'"a"}};'"si";"snd"[]{"outr"[]{'"a"}}}}};"m"."let"[]{"ifthenelse"[]{"is_inl"[]{'"a"};'"si";"lambda"[]{"x"."ma-ef-val"[]{"d-m"[]{'"D";'"i"};"fst"[]{"outr"[]{'"a"}};'"x";'"si";"snd"[]{"outr"[]{'"a"}};('"si" '"x")}}};"s'"."pair"[]{'"s'";"pair"[]{'"a";'"m"}}}}}}}}}}}


interactive nuprl_d__comp_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H>; "l": "IdLnk"[]{} ; "tg": "Id"[]{}  >- "subtype"[]{"ma-dout2"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"};"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"sched" '"x" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- ("d-comp"[]{'"D";'"v";'"sched";'"dec"} in "fun"[]{"nat"[]{};"t"."fun"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"t"};""."fun"[]{"Id"[]{};"i"."d-world-state"[]{'"D";'"i"}}};""."fun"[]{"Id"[]{};"i"."d-world-state"[]{'"D";'"i"}}}}) }

interactive nuprl_d__comp_wf2 {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"sched" '"x" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- ("d-comp"[]{'"D";'"v";'"sched";'"dec"} in "fun"[]{"nat"[]{};"t"."fun"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"t"};""."fun"[]{"Id"[]{};"i"."d-world-state"[]{'"D";'"i"}}};""."fun"[]{"Id"[]{};"i"."d-world-state"[]{'"D";'"i"}}}}) }

define unfold_d__world : "d-world"[]{'"D";'"v";'"sched";'"dec"} <-->
      "pair"[]{"lambda"[]{"i"."lambda"[]{"x"."ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"a"."ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}}}};"pair"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."fst"[]{"snd"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i")}}}};"pair"[]{"lambda"[]{"i"."lambda"[]{"t"."snd"[]{"snd"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i")}}}};"it"[]{}}}}}}}


interactive nuprl_d__world_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- ("d-world"[]{'"D";'"v";'"sched";'"dec"} in "world"[level:l]{}) }

interactive nuprl_d__comp__step univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "exists"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};"s"."and"[]{"equal"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};'"s";"ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}};"or"[]{"equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"stutter-state"[]{'"s"}};"exists"[]{"Knd"[]{};"k"."exists"[]{("d-decl"[]{'"D";'"i"} '"k");"val"."equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"next-world-state"[]{'"D";'"i";'"s";'"k";'"val"}}}}}}} }

define unfold_d__onlnk : "d-onlnk"[]{'"l";'"mss"} <-->
      "filter"[]{"lambda"[]{"ms"."eq_lnk"[]{"mlnk"[]{'"ms"};'"l"}};'"mss"}


interactive nuprl_d__onlnk_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"mss" in "list"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}}} }  -->
   sequent { <H> >- ("d-onlnk"[]{'"l";'"mss"} in "list"[]{"set"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"x"."assert"[]{"eq_lnk"[]{"mlnk"[]{'"x"};'"l"}}}}) }

define unfold_d__comp__partial__world : "d-comp-partial-world"[]{'"D";'"v";'"sched";'"dec";'"t"} <-->
      "d-partial-world"[]{'"D";"CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}};'"t";"lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}}}


interactive nuprl_d__comp__partial__world_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- ("d-comp-partial-world"[]{'"D";'"v";'"sched";'"dec";'"t"} in "world"[level:l]{}) }

interactive nuprl_w__queue__partial univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout2"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}}}};"w-queue"[]{"d-world"[]{'"D";'"v";'"sched";'"dec"};'"l";'"t'"};"w-queue"[]{"d-comp-partial-world"[]{'"D";'"v";'"sched";'"dec";'"t'"};'"l";'"t'"}} }

interactive nuprl_better__d__comp__step univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "exists"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};"s"."and"[]{"equal"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};'"s";"ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}};"or"[]{"equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"stutter-state"[]{'"s"}};"exists"[]{"Knd"[]{};"k"."exists"[]{("d-decl"[]{'"D";'"i"} '"k");"val"."and"[]{"equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"next-world-state"[]{'"D";'"i";'"s";'"k";'"val"}};"or"[]{"cand"[]{"assert"[]{"isrcv"[]{'"k"}};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{"lnk"[]{'"k"}};'"i"};"cand"[]{"ge"[]{"length"[]{"w-queue"[]{"d-world"[]{'"D";'"v";'"sched";'"dec"};"lnk"[]{'"k"};'"t"}};"number"[1:n]{}};"equal"[]{"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}}};"hd"[]{"w-queue"[]{"d-world"[]{'"D";'"v";'"sched";'"dec"};"lnk"[]{'"k"};'"t"}};"msg"[]{"lnk"[]{'"k"};"tagof"[]{'"k"};'"val"}}}}};"assert"[]{"islocal"[]{'"k"}}}}}}}}} }

interactive nuprl_d__comp__step2 univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "exists"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};"s"."and"[]{"equal"[]{"ma-st"[]{"d-m"[]{'"D";'"i"}};'"s";"ifthenelse"[]{"beq_int"[]{'"t";"number"[0:n]{}};"lambda"[]{"x"."ma-init-val"[]{"d-m"[]{'"D";'"i"};'"x";(('"v" '"i") '"x")}};"fst"[]{(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} "sub"[]{'"t";"number"[1:n]{}}) '"i")}}};"or"[]{"equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"stutter-state"[]{'"s"}};"exists"[]{"Knd"[]{};"k"."exists"[]{("d-decl"[]{'"D";'"i"} '"k");"val"."and"[]{"equal"[]{"d-world-state"[]{'"D";'"i"};(("CV"[]{"d-comp"[]{'"D";'"v";'"sched";'"dec"}} '"t") '"i");"next-world-state"[]{'"D";'"i";'"s";'"k";'"val"}};"or"[]{"assert"[]{"isrcv"[]{'"k"}};"cand"[]{"assert"[]{"islocal"[]{'"k"}};"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};"actof"[]{'"k"}};"ma-pre"[]{"d-m"[]{'"D";'"i"};"actof"[]{'"k"};'"s";'"val"}}}}}}}}}} }

interactive nuprl_w__queue__nil univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"sched" '"i" in "union"[]{"fun"[]{"nat"[]{};""."union"[]{"IdLnk"[]{};"Id"[]{}}};"unit"[]{}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"v" '"i" in "ma-st"[]{"d-m"[]{'"D";'"i"}} }  -->
   [wf] sequent { <H>;"i": "Id"[]{};"a": "Id"[]{};"s": "ma-st"[]{"d-m"[]{'"D";'"i"}} >- '"dec" '"i" '"a" '"s" in "decidable"[]{"cand"[]{"ma-has-pre"[]{"d-m"[]{'"D";'"i"};'"a"};"exists"[]{"ma-da"[]{"d-m"[]{'"D";'"i"};"locl"[]{'"a"}};"v"."ma-pre"[]{"d-m"[]{'"D";'"i"};'"a";'"s";'"v"}}}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"ma-sends-on"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l"}}} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout2"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}}}};"w-queue"[]{"d-world"[]{'"D";'"v";'"sched";'"dec"};'"l";'"t"};"nil"[]{}} }

define unfold_d__rename : "d-rename"[]{'"rx";'"ra";'"rt";'"D"} <-->
      "lambda"[]{"i"."ma-rename"[]{'"rx";'"ra";'"rt";('"D" '"i")}}


interactive nuprl_d__rename_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rx" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"ra" '"x" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"rt" '"x" in "Id"[]{} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"rx"} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"ra"} }  -->
   sequent { <H> >- "inject"[]{"Id"[]{};"Id"[]{};'"rt"} }  -->
   sequent { <H> >- ("d-rename"[]{'"rx";'"ra";'"rt";'"D"} in "dsys"[level:l]{}) }

interactive nuprl_d__msg__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "subtype"[]{"set"[]{"ma-msg"[]{"d-m"[]{'"D";'"i"}};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."ma-dout"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};'"l";'"tg"}}}}} }

interactive nuprl_d__decl__subtype2 univ[level:l]  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "subtype"[]{("d-decl"[]{'"D";'"i"} '"k");"ma-da"[]{"d-m"[]{'"D";'"i"};'"k"}} }

define unfold_interface__check : "interface-check"[]{'"D";'"l";'"tg";'"T"} <-->
      "subtype"[]{'"T";"ma-din"[]{"d-m"[]{'"D";"ldst"[]{'"l"}};'"l";'"tg"}}


interactive nuprl_interface__check_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("interface-check"[]{'"D";'"l";'"tg";'"T"} in "univ"[level:l]{}) }

interactive nuprl_interface__check__tag__type univ[level:l] '"T"  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"l2" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "ma-tag-type"[level:l]{'"A";'"tg";'"T"} }  -->
   sequent { <H> >- "ma-tag-type"[level:l]{'"B";'"tg";'"T"} }  -->
   sequent { <H> >- "subtype"[]{"ma-dout"[]{'"A";'"l1";'"tg"};"ma-din"[]{'"B";'"l2";'"tg"}} }

interactive nuprl_finite__support__feasible univ[level:l] '"L"  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Id"[]{}} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "or"[]{"mem"[]{'"i";'"L";"Id"[]{}};"assert"[]{"ma-is-empty"[]{"d-m"[]{'"D";'"i"}}}} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "ma-feasible"[]{"d-m"[]{'"D";'"i"}} }  -->
   sequent { <H> >- "l_all"[]{'"L";"Id"[]{};"i"."l_all"[]{"ma-outlinks"[]{"d-m"[]{'"D";'"i"};'"i"};"prod"[]{"IdLnk"[]{};""."prod"[]{"Id"[]{};""."univ"[level:l]{}}};"ltg"."implies"[]{"mem"[]{"ldst"[]{"fst"[]{'"ltg"}};'"L";"Id"[]{}};"interface-check"[]{'"D";"fst"[]{'"ltg"};"fst"[]{"snd"[]{'"ltg"}};"snd"[]{"snd"[]{'"ltg"}}}}}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }

interactive nuprl_finite__support__interface__feasible univ[level:l] '"L" '"f"  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Id"[]{}} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"f" '"x" in "univ"[level:l]{} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "or"[]{"mem"[]{'"i";'"L";"Id"[]{}};"equal"[]{"msga"[level:l]{};"d-m"[]{'"D";'"i"};"ma-empty"[]{}}} }  -->
   sequent { <H> >- "l_all"[]{'"L";"Id"[]{};"i"."all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."implies"[]{"ma-declm"[]{"d-m"[]{'"D";'"i"};'"l";'"tg"};"equal"[]{"univ"[level:l]{};"ma-da"[]{"d-m"[]{'"D";'"i"};"rcv"[]{'"l";'"tg"}};('"f" '"tg")}}}}} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "ma-feasible"[]{"d-m"[]{'"D";'"i"}} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }


(**** display forms ****)


dform nuprl_dsys_df : except_mode[src] :: "dsys"[level:l]{} =
   `"Dsys"


dform nuprl_d__eq__Loc_df : except_mode[src] :: "d-eq-Loc"[]{'"i";'"j"} =
   `"" slot{'"i"} `" = " slot{'"j"} `""


dform nuprl_d__I_df : except_mode[src] :: "d-I"[]{'"i"} =
   `"Inlnk(" slot{'"i"} `")"


dform nuprl_d__O_df : except_mode[src] :: "d-O"[]{'"i"} =
   `"Outlnk(" slot{'"i"} `")"


dform nuprl_d__m_df : except_mode[src] :: "d-m"[]{'"D";'"i"} =
   `"M(" slot{'"i"} `")"


dform nuprl_d__decl_df : except_mode[src] :: "d-decl"[]{'"D";'"i"} =
   `"d-decl(" slot{'"D"} `";" slot{'"i"} `")"


dform nuprl_d__sub_df : except_mode[src] :: "d-sub"[level:l]{'"D1";'"D2"} =
   `"" slot{'"D1"} `" " sqsubseteq `" " slot{'"D2"} `""


dform nuprl_d__single__init_df : except_mode[src] :: "d-single-init"[]{'"i";'"x";'"T";'"v"} =
   `"@" slot{'"i"} `": " pushm[0:n] `"" slot{'"x"} `":" slot{'"T"} `""
    sbreak["",""] `" initially " slot{'"x"} `" = " slot{'"v"} `"" popm  `""


dform nuprl_d__single__frame_df : except_mode[src] :: "d-single-frame"[]{'"i";'"L";'"t";'"x"} =
   `"@" slot{'"i"} `": only " slot{'"L"} `" affects " slot{'"x"} `" : " slot{'"t"}
    `""


dform nuprl_d__single__sframe_df : except_mode[src] :: "d-single-sframe"[]{'"i";'"L";'"l";'"tg"} =
   `"@" slot{'"i"} `": only " slot{'"L"} `" sends on (" slot{'"l"} `" with "
    slot{'"tg"} `")"


dform nuprl_d__single__effect_df : except_mode[src] :: "d-single-effect"[]{'"i";'"ds";'"da";'"k";'"x";'"f"} =
   `"@" slot{'"i"} `": with declarations " sbreak["",""] `"ds:" slot{'"ds"} `""
    sbreak["",""] `"da:" slot{'"da"} `"" sbreak["",""] `"" sbreak["",""]
    `"effect of " slot{'"k"} `"(v) is " slot{'"x"} `" := " slot{'"f"} `" s v"


dform nuprl_d__single__sends_df : except_mode[src] :: "d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"} =
   `"@" slot{'"i"} `": with declarations " sbreak["",""] `"ds:" slot{'"ds"} `""
    sbreak["",""] `"da:" slot{'"da"} `"" sbreak["",""] `" " slot{'"k"}
    `"(v) sends " slot{'"f"} `" s v on link " slot{'"l"} `""


dform nuprl_d__single__pre_df : except_mode[src] :: "d-single-pre"[]{'"i";'"ds";'"a";'"T";'"P"} =
   `"@" slot{'"i"} `"" pushm[0:n] `" (with ds: " slot{'"ds"} `"" sbreak["",""]
    `" action " slot{'"a"} `":" slot{'"T"} `"" sbreak["",""] `" precondition "
    slot{'"a"} `"(v) is" sbreak["",""] `" " slot{'"P"} `" s v)" popm  `""


dform nuprl_d__single__pre__init_df : except_mode[src] :: "d-single-pre-init"[]{'"i";'"ds";'"init";'"a";'"T";'"P"} =
   `"@" slot{'"i"} `"" pushm[0:n] `" (with ds: " slot{'"ds"} `"" sbreak["",""]
    `" init: " slot{'"init"} `"" sbreak["",""] `" action " slot{'"a"} `":"
    slot{'"T"} `"" sbreak["",""] `" precondition " slot{'"a"} `"(v) is"
    sbreak["",""] `" " slot{'"P"} `" s v)" popm  `""


dform nuprl_d__feasible_df : except_mode[src] :: "d-feasible"[]{'"D"} =
   `"Feasible(" slot{'"D"} `")"


dform nuprl_d__world__state_df : except_mode[src] :: "d-world-state"[]{'"D";'"i"} =
   `"d-world-state(" slot{'"D"} `";" slot{'"i"} `")"


dform nuprl_stutter__state_df : except_mode[src] :: "stutter-state"[]{'"s"} =
   `"stutter-state(" slot{'"s"} `")"


dform nuprl_next__world__state_df : except_mode[src] :: "next-world-state"[]{'"D";'"i";'"s";'"k";'"v"} =
   `"next-world-state(" slot{'"D"} `";" slot{'"i"} `";" slot{'"s"} `";" slot{'"k"}
    `";" slot{'"v"} `")"


dform nuprl_d__partial__world_df : except_mode[src] :: "d-partial-world"[]{'"D";'"f";'"t'";'"s"} =
   `"d-partial-world(" slot{'"D"} `";" slot{'"f"} `";" slot{'"t'"} `";" slot{'"s"}
    `")"


dform nuprl_d__comp_df : except_mode[src] :: "d-comp"[]{'"D";'"v";'"sched";'"dec"} =
   `"d-comp(" slot{'"D"} `";" slot{'"v"} `";" slot{'"sched"} `";" slot{'"dec"} `")"


dform nuprl_d__world_df : except_mode[src] :: "d-world"[]{'"D";'"v";'"sched";'"dec"} =
   `"d-world(" slot{'"D"} `";" slot{'"v"} `";" slot{'"sched"} `";" slot{'"dec"}
    `")"


dform nuprl_d__onlnk_df : except_mode[src] :: "d-onlnk"[]{'"l";'"mss"} =
   `"onlnk(" slot{'"l"} `";" slot{'"mss"} `")"


dform nuprl_d__comp__partial__world_df : except_mode[src] :: "d-comp-partial-world"[]{'"D";'"v";'"sched";'"dec";'"t"} =
   `"d-comp-partial-world(" slot{'"D"} `";" slot{'"v"} `";" slot{'"sched"} `";"
    slot{'"dec"} `";" slot{'"t"} `")"


dform nuprl_d__rename_df : except_mode[src] :: "d-rename"[]{'"rx";'"ra";'"rt";'"D"} =
   `"d-rename(" slot{'"rx"} `";" slot{'"ra"} `";" slot{'"rt"} `";" slot{'"D"} `")"


dform nuprl_interface__check_df : except_mode[src] :: "interface-check"[]{'"D";'"l";'"tg";'"T"} =
   `"interface-check(" slot{'"D"} `";" slot{'"l"} `";" slot{'"tg"} `";" slot{'"T"}
    `")"


