extends Ma_general__theory

open Dtactic


define unfold_s__decl : "s-decl"[level:l]{} <-->
      "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}}


interactive nuprl_s__decl_wf {| intro[] |}   :
   sequent { <H> >- ("s-decl"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_s__decl_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"s-decl"[level:l]{}} }

define unfold_s__decl__null : "s-decl-null"[]{} <-->
      "fpf-empty"[]{}


interactive nuprl_s__decl__null_wf {| intro[] |}   :
   sequent { <H> >- ("s-decl-null"[]{} in "s-decl"[level:l]{}) }

define unfold_s__declared : "s-declared"[]{'"d";'"a"} <-->
      "fpf-cap"[]{'"d";"id-deq"[]{};'"a";"top"[]{}}


interactive nuprl_s__declared_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"d" in "s-decl"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- ("s-declared"[]{'"d";'"x"} in "univ"[level:l]{}) }

interactive nuprl_s__declared_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"d" in "s-decl"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"s-declared"[]{'"d";'"x"}} }

define unfold_m__at : "m-at"[]{'"M";'"i"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");'"M";"ma-empty"[]{}}}


interactive nuprl_m__at_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("m-at"[]{'"M";'"i"} in "dsys"[level:l]{}) }

interactive nuprl_m__at__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-feasible"[]{'"M"} }  -->
   sequent { <H> >- "d-feasible"[]{"m-at"[]{'"M";'"i"}} }

define unfold_in__decl : "in-decl"[level:l]{'"i"} <-->
      "fpf"[]{"set"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"p"."equal"[]{"Id"[]{};"ldst"[]{"fst"[]{'"p"}};'"i"}};"ltg"."univ"[level:l]{}}


interactive nuprl_in__decl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("in-decl"[level:l]{'"i"} in "univ"[level':l]{}) }

interactive nuprl_in__decl_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"in-decl"[level:l]{'"i"}} }

define unfold_out__decl : "out-decl"[level:l]{'"i"} <-->
      "fpf"[]{"set"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"p"."equal"[]{"Id"[]{};"lsrc"[]{"fst"[]{'"p"}};'"i"}};"ltg"."univ"[level:l]{}}


interactive nuprl_out__decl_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- ("out-decl"[level:l]{'"i"} in "univ"[level':l]{}) }

interactive nuprl_out__decl_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "type"{"out-decl"[level:l]{'"i"}} }

define unfold_s__in__declared : "s-in-declared"[]{'"d";'"p"} <-->
      "fpf-cap"[]{'"d";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};'"p";"top"[]{}}


define unfold_s__out__declared : "s-out-declared"[]{'"d";'"p"} <-->
      "fpf-cap"[]{'"d";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};'"p";"top"[]{}}


interactive nuprl_s__out__declared_wf {| intro[] |}  '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "out-decl"[level:l]{'"i"} }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{"IdLnk"[]{};""."Id"[]{}} }  -->
   sequent { <H> >- ("s-out-declared"[]{'"d";'"p"} in "univ"[level:l]{}) }

interactive nuprl_s__out__declared_wf_type {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "out-decl"[level:l]{'"i"} }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{"IdLnk"[]{};""."Id"[]{}} }  -->
   sequent { <H> >- "type"{"s-out-declared"[]{'"d";'"p"}} }

interactive nuprl_s__in__declared_wf {| intro[] |}  '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "in-decl"[level:l]{'"i"} }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{"IdLnk"[]{};""."Id"[]{}} }  -->
   sequent { <H> >- ("s-in-declared"[]{'"d";'"p"} in "univ"[level:l]{}) }

interactive nuprl_s__in__declared_wf_type {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "in-decl"[level:l]{'"i"} }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{"IdLnk"[]{};""."Id"[]{}} }  -->
   sequent { <H> >- "type"{"s-in-declared"[]{'"d";'"p"}} }

define unfold_s__valtype : "s-valtype"[]{'"k";'"da";'"din"} <-->
      "kindcase"[]{'"k";"a"."fpf-cap"[]{'"da";"id-deq"[]{};'"a";"top"[]{}};"l", "tg"."fpf-cap"[]{'"din";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{'"l";'"tg"};"top"[]{}}}


interactive nuprl_s__valtype_wf {| intro[] |}  '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"da" in "s-decl"[level:l]{} }  -->
   [wf] sequent { <H> >- '"din" in "in-decl"[level:l]{'"i"} }  -->
   sequent { <H> >- ("s-valtype"[]{'"k";'"da";'"din"} in "univ"[level:l]{}) }

interactive nuprl_s__valtype_wf_type {| intro[] |} univ[level:l] '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"da" in "s-decl"[level:l]{} }  -->
   [wf] sequent { <H> >- '"din" in "in-decl"[level:l]{'"i"} }  -->
   sequent { <H> >- "type"{"s-valtype"[]{'"k";'"da";'"din"}} }

define unfold_s__state : "s-state"[]{'"ds"} <-->
      "fun"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}


interactive nuprl_s__state_wf   :
   [wf] sequent { <H> >- '"d" in "s-decl"[level:l]{} }  -->
   sequent { <H> >- ("ma-state"[]{'"d"} in "univ"[level:l]{}) }

interactive nuprl_s__state_wf_type univ[level:l]  :
   [wf] sequent { <H> >- '"d" in "s-decl"[level:l]{} }  -->
   sequent { <H> >- "type"{"ma-state"[]{'"d"}} }

define unfold_msystem : "msystem"[level:l]{} <-->
      "set"[]{"fun"[]{"Id"[]{};"loc"."msga"[level:l]{}};"M"."all"[]{"Id"[]{};"loc"."ma-feasible"[]{('"M" '"loc")}}}


interactive nuprl_msystem_wf {| intro[] |}   :
   sequent { <H> >- ("msystem"[level:l]{} in "univ"[level':l]{}) }

interactive nuprl_msystem_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"msystem"[level:l]{}} }

define unfold_m__sys__null : "m-sys-null"[]{} <-->
      "lambda"[]{"i"."ma-empty"[]{}}


interactive nuprl_m__sys__null_wf {| intro[] |}   :
   sequent { <H> >- ("m-sys-null"[]{} in "msystem"[level:l]{}) }

interactive nuprl_d__feasible__null   :
   sequent { <H> >- "d-feasible"[]{"m-sys-null"[]{}} }

define unfold_m__sys__at : "m-sys-at"[]{'"i";'"A"} <-->
      "lambda"[]{"j"."ifthenelse"[]{"eq_id"[]{'"j";'"i"};'"A";"ma-empty"[]{}}}


interactive nuprl_m__sys__at_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"M" in "set"[]{"msga"[level:l]{};"M"."ma-feasible"[]{'"M"}} }  -->
   sequent { <H> >- ("m-sys-at"[]{'"i";'"M"} in "msystem"[level:l]{}) }

define unfold_m__sys__compatible : "m-sys-compatible"[level:l]{'"A";'"B"} <-->
      "all"[]{"Id"[]{};"i"."and"[]{"ma-compatible"[level:l]{('"A" '"i");('"B" '"i")};"and"[]{"ma-frame-compatible"[]{('"A" '"i");('"B" '"i")};"ma-sframe-compatible"[]{('"A" '"i");('"B" '"i")}}}}


interactive nuprl_m__sys__compatible_wf {| intro[] |}   :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"A" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"B" '"i" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("m-sys-compatible"[level:l]{'"A";'"B"} in "univ"[level':l]{}) }

interactive nuprl_m__sys__compatible__symmetry   :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"A" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"B" '"i" in "msga"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"B";'"A"} }

interactive nuprl_m__sys__null__compatible__right   :
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"M";"m-sys-null"[]{}} }

interactive nuprl_m__at__compatible   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"m-sys-compatible"[level:l]{"m-at"[]{'"A";'"i"};"m-at"[]{'"B";'"j"}};"implies"[]{"equal"[]{"Id"[]{};'"i";'"j"};"and"[]{"ma-compatible"[level:l]{'"A";'"B"};"and"[]{"ma-frame-compatible"[]{'"A";'"B"};"ma-sframe-compatible"[]{'"A";'"B"}}}}} }

interactive nuprl_m__at__distinct__compatible   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"i";'"j"}} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{"m-at"[]{'"A";'"i"};"m-at"[]{'"B";'"j"}} }

interactive nuprl_m__at__self__compatible   :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{"m-at"[]{'"A";'"i"};"m-at"[]{'"A";'"i"}} }

define unfold_m__sys__join : "m-sys-join"[]{'"A";'"B"} <-->
      "lambda"[]{"i"."ma-join"[]{('"A" '"i");('"B" '"i")}}


interactive nuprl_m__sys__join_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- ("m-sys-join"[]{'"A";'"B"} in "msystem"[level:l]{}) }

interactive nuprl_m__sys__join_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- ("m-sys-join"[]{'"A";'"B"} in "dsys"[level:l]{}) }

interactive nuprl_m__sys__compatible__join   :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_dsys__compatible__join   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";'"A"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";'"B"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"C";"m-sys-join"[]{'"A";'"B"}} }

define unfold_interface__link : "interface-link"[]{'"A";'"B";'"l";'"tg"} <-->
      "and"[]{"ma-declm"[]{('"A" "lsrc"[]{'"l"});'"l";'"tg"};"and"[]{"ma-declm"[]{('"B" "ldst"[]{'"l"});'"l";'"tg"};"not"[]{"ma-declm"[]{('"B" "lsrc"[]{'"l"});'"l";'"tg"}}}}


interactive nuprl_interface__link_wf {| intro[] |}   :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"A" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"B" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("interface-link"[]{'"A";'"B";'"l";'"tg"} in "univ"[level:l]{}) }

define unfold_interface__compatible : "interface-compatible"[]{'"A";'"B"} <-->
      "all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."and"[]{"implies"[]{"interface-link"[]{'"A";'"B";'"l";'"tg"};"subtype"[]{"ma-dout"[]{('"A" "lsrc"[]{'"l"});'"l";'"tg"};"ma-din"[]{('"B" "ldst"[]{'"l"});'"l";'"tg"}}};"implies"[]{"interface-link"[]{'"B";'"A";'"l";'"tg"};"subtype"[]{"ma-dout"[]{('"B" "lsrc"[]{'"l"});'"l";'"tg"};"ma-din"[]{('"A" "ldst"[]{'"l"});'"l";'"tg"}}}}}}


interactive nuprl_interface__compatible_wf {| intro[] |}   :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"A" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"B" '"i" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("interface-compatible"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_interface__compatible__symmetry univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "interface-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "interface-compatible"[]{'"B";'"A"} }

interactive nuprl_interface__compatible__null univ[level:l]  :
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "interface-compatible"[]{'"M";"m-sys-null"[]{}} }

interactive nuprl_interface__compatible__join univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "interface-compatible"[]{'"C";'"A"} }  -->
   sequent { <H> >- "interface-compatible"[]{'"C";'"B"} }  -->
   sequent { <H> >- "interface-compatible"[]{'"C";"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_interface__compatible__at__same univ[level:l]  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "interface-compatible"[]{"m-at"[]{'"A";'"i"};"m-at"[]{'"B";'"i"}} }

interactive nuprl_m__sys__feasible__join univ[level:l]  :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"A" '"i" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"i": "Id"[]{} >- '"B" '"i" in "msga"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "interface-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "d-feasible"[]{'"A"} }  -->
   sequent { <H> >- "d-feasible"[]{'"B"} }  -->
   sequent { <H> >- "d-feasible"[]{"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_m__sys__sub__join__left   :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"A";"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_dsys__sub__join__left   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"A";"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_m__sys__sub__join__right   :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"B";"m-sys-join"[]{'"A";'"B"}} }

interactive nuprl_dsys__sub__join__right   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"B";"m-sys-join"[]{'"A";'"B"}} }

define unfold_m__sys__join__list : "m-sys-join-list"[]{'"L"} <-->
      "reduce"[]{"lambda"[]{"A"."lambda"[]{"B"."m-sys-join"[]{'"A";'"B"}}};"m-sys-null"[]{};'"L"}


interactive nuprl_m__sys__join__list__property   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msystem"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{("m-sys-join-list"[]{'"L"} in "msystem"[level:l]{});"and"[]{"all"[]{"msystem"[level:l]{};"M"."implies"[]{"l_all"[]{'"L";"msystem"[level:l]{};"B"."m-sys-compatible"[level:l]{'"M";'"B"}};"m-sys-compatible"[level:l]{'"M";"m-sys-join-list"[]{'"L"}}}};"l_all"[]{'"L";"msystem"[level:l]{};"B"."d-sub"[level:l]{'"B";"m-sys-join-list"[]{'"L"}}}}}} }

interactive nuprl_dsys__join__list__property   :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{("m-sys-join-list"[]{'"L"} in "dsys"[level:l]{});"and"[]{"all"[]{"dsys"[level:l]{};"M"."implies"[]{"l_all"[]{'"L";"dsys"[level:l]{};"B"."m-sys-compatible"[level:l]{'"M";'"B"}};"m-sys-compatible"[level:l]{'"M";"m-sys-join-list"[]{'"L"}}}};"l_all"[]{'"L";"dsys"[level:l]{};"B"."d-sub"[level:l]{'"B";"m-sys-join-list"[]{'"L"}}}}}} }

interactive nuprl_m__sys__join__list_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"L" in "list"[]{"msystem"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- ("m-sys-join-list"[]{'"L"} in "msystem"[level:l]{}) }

interactive nuprl_m__sys__join__list_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- ("m-sys-join-list"[]{'"L"} in "dsys"[level:l]{}) }

interactive nuprl_m__sys__sub__join__list   :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"msystem"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "mem"[]{'"A";'"L";"dsys"[level:l]{}} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"A";"m-sys-join-list"[]{'"L"}} }

interactive nuprl_m__sys__sub__join__map  '"T" '"L" "lambda"[]{"x".'"f"['"x"]} '"x"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f"['"x"] in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "pairwise"[]{"x", "y"."m-sys-compatible"[level:l]{'"f"['"x"];'"f"['"y"]};'"L"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"f"['"x"];"m-sys-join-list"[]{"map"[]{"lambda"[]{"x".'"f"['"x"]};'"L"}}} }

interactive nuprl_m__sys__join__list__property2 univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"msystem"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"M" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "l_all"[]{'"L";"msystem"[level:l]{};"B"."interface-compatible"[]{'"M";'"B"}} }  -->
   sequent { <H> >- "interface-compatible"[]{'"M";"m-sys-join-list"[]{'"L"}} }

interactive nuprl_join__list__compatible   :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"dsys"[level:l]{};"B"."m-sys-compatible"[level:l]{'"M";'"B"}} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"M";"m-sys-join-list"[]{'"L"}} }

interactive nuprl_join__list__compatible2   :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"dsys"[level:l]{};"B"."m-sys-compatible"[level:l]{'"M";'"B"}} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{"m-sys-join-list"[]{'"L"};'"M"} }

interactive nuprl_interface__compatible__join__list univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"dsys"[level:l]{};"B"."interface-compatible"[]{'"M";'"B"}} }  -->
   sequent { <H> >- "interface-compatible"[]{'"M";"m-sys-join-list"[]{'"L"}} }

interactive nuprl_interface__compatible__join__list2 univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   [wf] sequent { <H> >- '"M" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "l_all"[]{'"L";"dsys"[level:l]{};"B"."interface-compatible"[]{'"B";'"M"}} }  -->
   sequent { <H> >- "interface-compatible"[]{"m-sys-join-list"[]{'"L"};'"M"} }

interactive nuprl_feasible__join__list univ[level:l]  :
   [wf] sequent { <H> >- '"L" in "list"[]{"dsys"[level:l]{}} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."interface-compatible"[]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."m-sys-compatible"[level:l]{'"A";'"B"};'"L"} }  -->
   sequent { <H> >- "l_all"[]{'"L";"dsys"[level:l]{};"A"."d-feasible"[]{'"A"}} }  -->
   sequent { <H> >- "d-feasible"[]{"m-sys-join-list"[]{'"L"}} }

interactive nuprl_ma__single__pre1_wf2 {| intro[] |}  '"T'" '"T" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"x"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T'" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T'" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("ma-single-pre1"[]{'"x";'"T";'"a";'"T'";"x", "v".'"P"['"x";'"v"]} in "msga"[level:l]{}) }

interactive nuprl_ma__single__effect0_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"f" '"x" '"x1" in '"A" }  -->
   sequent { <H> >- ("ma-single-effect0"[]{'"x";'"A";'"a";'"T";'"f"} in "msga"[level:l]{}) }

define unfold_s__dsys : "s-dsys"[]{'"M"} <-->
      '"M"


interactive nuprl_s__dsys_wf {| intro[] |}   :
   [wf] sequent { <H>;"i": "Id"[]{} >- '"M" '"i" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("s-dsys"[]{'"M"} in "dsys"[level:l]{}) }

define unfold_dsys__null : "dsys-null"[]{} <-->
      "s-dsys"[]{"m-sys-null"[]{}}


interactive nuprl_dsys__null_wf {| intro[] |}   :
   sequent { <H> >- ("dsys-null"[]{} in "dsys"[level:l]{}) }

interactive nuprl_s__at__sub__s__dsys   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "iff"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";'"A"};'"M"};"ma-sub"[level:l]{'"A";('"M" '"i")}} }

interactive nuprl_s__at__sub__s__at   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "iff"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";'"A"};"m-sys-at"[]{'"i";'"B"}};"ma-sub"[level:l]{'"A";'"B"}} }

interactive nuprl_s__dsys__sub__s__dsys   :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "ma-sub"[level:l]{('"A" '"i");('"B" '"i")} }  -->
   sequent { <H> >- "d-sub"[level:l]{"s-dsys"[]{'"A"};"s-dsys"[]{'"B"}} }

interactive nuprl_dsys__single__sub__dsys  '"i"  :
   [wf] sequent { <H> >- '"A" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msystem"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   sequent { <H>; "j": "Id"[]{} ; "not"[]{"equal"[]{"Id"[]{};'"j";'"i"}}  >- "equal"[]{"msga"[level:l]{};('"A" '"j");"ma-empty"[]{}} }  -->
   sequent { <H> >- "ma-sub"[level:l]{('"A" '"i");('"B" '"i")} }  -->
   sequent { <H> >- "d-sub"[level:l]{"s-dsys"[]{'"A"};"s-dsys"[]{'"B"}} }

define unfold_Rcv : "Rcv"[]{'"l";'"tg"} <-->
      "rcv"[]{'"l";'"tg"}


interactive nuprl_Rcv_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- ("Rcv"[]{'"l";'"tg"} in "Knd"[]{}) }

interactive nuprl_s__pre__init__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent { <H>; "x": "Id"[]{} ; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"ds"}}  >- "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}};'"D"};"d-realizes"[level:l]{'"D";"es"."implies"[]{"exists"[]{'"T";"v".(('"P" "lambda"[]{"x"."fpf-cap"[]{'"init";"id-deq"[]{};'"x";"it"[]{}}}) '"v")};"exists"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}}}}}} }

interactive nuprl_s__pre__init__rule0  '"T" "lambda"[]{"x".'"P"['"x"]} '"a" '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre"[]{"fpf-empty"[]{};'"a";'"T";"lambda"[]{"s"."lambda"[]{"v".'"P"['"v"]}}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre"[]{"fpf-empty"[]{};'"a";'"T";"lambda"[]{"s"."lambda"[]{"v".'"P"['"v"]}}}};'"D"};"d-realizes"[level:l]{'"D";"es"."implies"[]{"exists"[]{'"T";"v".'"P"['"v"]};"exists"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}}}}}} }

interactive nuprl_s__pre__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};(('"P" "lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}}) "es-val"[]{'"es";'"e"})};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"all"[]{'"T";"v"."not"[]{(('"P" "lambda"[]{"z"."es-after"[]{'"es";'"z";'"e'"}}) '"v")}}}}}}}}}}}}} }

interactive nuprl_s__pre__rule0  '"T" "lambda"[]{"x".'"P"['"x"]} '"a" '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre"[]{"fpf-empty"[]{};'"a";'"T";"lambda"[]{"s"."lambda"[]{"v".'"P"['"v"]}}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre"[]{"fpf-empty"[]{};'"a";'"T";"lambda"[]{"s"."lambda"[]{"v".'"P"['"v"]}}}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};'"P"["es-val"[]{'"es";'"e"}]};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"all"[]{'"T";"v"."not"[]{'"P"['"v"]}}}}}}}}}}}}} }

interactive nuprl_s__pre__rule1  '"T" '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"x" '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre1"[]{'"x";'"A";'"a";'"T";"x", "v".'"P"['"x";'"v"]}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre1"[]{'"x";'"A";'"a";'"T";"x", "v".'"P"['"x";'"v"]}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};'"P"["es-when"[]{'"es";'"x";'"e"};"es-val"[]{'"es";'"e"}]};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"all"[]{'"T";"v"."not"[]{'"P"["es-after"[]{'"es";'"x";'"e'"};'"v"]}}}}}}}}}}}}} }

interactive nuprl_s__effect__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": "ma-valtype"[]{'"da";'"k"} >- '"f" '"x" '"x1" in "fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"equal"[]{"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}};"es-after"[]{'"es";'"x";'"e"};(('"f" "lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}}) "es-val"[]{'"es";'"e"})}}}}}}}}} }

interactive nuprl_s__effect__rule0   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"f" '"x" '"x1" in '"A" }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-effect0"[]{'"x";'"A";'"a";'"T";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-effect0"[]{'"x";'"A";'"a";'"T";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"};"equal"[]{'"A";"es-after"[]{'"es";'"x";'"e"};(('"f" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}}}} }

interactive nuprl_effect__rule1   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B";"x2": '"T" >- '"f" '"x" '"x1" '"x2" in '"A" }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"y";'"x"}} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"};"subtype"[]{"es-vartype"[]{'"es";'"i";'"y"};'"B"}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"equal"[]{'"A";"es-after"[]{'"es";'"x";'"e"};((('"f" "es-when"[]{'"es";'"x";'"e"}) "es-when"[]{'"es";'"y";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}}}} }

interactive nuprl_s__sends__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"implies"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"list"[]{"set"[]{"es-E"[]{'"es"};"e'"."cand"[]{"assert"[]{"es-isrcv"[]{'"es";'"e'"}};"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e'"};'"l"}}}};"L"."and"[]{"all"[]{"es-E"[]{'"es"};"e'"."iff"[]{"mem"[]{'"e'";'"L";"es-E"[]{'"es"}};"cand"[]{"assert"[]{"es-isrcv"[]{'"es";'"e'"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e'"};'"l"};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e1"."all"[]{"es-E"[]{'"es"};"e2"."implies"[]{"l_before"[]{'"e1";'"e2";'"L";"es-E"[]{'"es"}};"es-locl"[]{'"es";'"e1";'"e2"}}}};"equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg"."ma-valtype"[]{'"da";"rcv"[]{'"l";'"tg"}}}};"map"[]{"lambda"[]{"e'"."pair"[]{"es-tag"[]{'"es";'"e'"};"es-val"[]{'"es";'"e'"}}};'"L"};"tagged-list-messages"[]{"lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}};"es-val"[]{'"es";'"e"};'"f"}}}}}}}}}}}}} }

interactive nuprl_ma__single__sends1_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in "list"[]{'"T"} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};'"a";"rcv"[]{'"l";'"tg"}}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   sequent { <H> >- ("ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"a";'"l";'"tg";'"f"} in "msga"[level:l]{}) }

interactive nuprl_s__sends__rule1   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in "list"[]{'"T"} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";"lsrc"[]{'"l"};'"x"};'"A"};"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"B"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"list"[]{"set"[]{"es-E"[]{'"es"};"e'"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}}}};"L"."and"[]{"all"[]{"es-E"[]{'"es"};"e'"."iff"[]{"mem"[]{'"e'";'"L";"es-E"[]{'"es"}};"cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e1"."all"[]{"es-E"[]{'"es"};"e2"."implies"[]{"l_before"[]{'"e1";'"e2";'"L";"es-E"[]{'"es"}};"es-locl"[]{'"es";'"e1";'"e2"}}}};"equal"[]{"list"[]{'"T"};"map"[]{"lambda"[]{"e'"."es-val"[]{'"es";'"e'"}};'"L"};(('"f" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}}}}}}} }

interactive nuprl_s__unconditional__send1__rule   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in '"T" }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{(('"f" '"a") '"b");"nil"[]{}}}}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{(('"f" '"a") '"b");"nil"[]{}}}}}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";"lsrc"[]{'"l"};'"x"};'"A"};"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"B"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"and"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"};"and"[]{"all"[]{"es-E"[]{'"es"};"e''"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e''"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};'"e"};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}};"equal"[]{'"T";"es-val"[]{'"es";'"e'"};(('"f" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}}}}}}}}} }

interactive nuprl_conditional__send1__rule   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in '"T" }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"c" '"x" '"x1" in "bool"[]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."ifthenelse"[]{(('"c" '"a") '"b");"cons"[]{(('"f" '"a") '"b");"nil"[]{}};"nil"[]{}}}}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."ifthenelse"[]{(('"c" '"a") '"b");"cons"[]{(('"f" '"a") '"b");"nil"[]{}};"nil"[]{}}}}}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";"lsrc"[]{'"l"};'"x"};'"A"};"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"B"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"and"[]{"implies"[]{"assert"[]{(('"c" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"and"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"};"and"[]{"all"[]{"es-E"[]{'"es"};"e''"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e''"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};'"e"};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}};"equal"[]{'"T";"es-val"[]{'"es";'"e'"};(('"f" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}}}}}};"implies"[]{"not"[]{"assert"[]{(('"c" "es-when"[]{'"es";'"x";'"e"}) "es-val"[]{'"es";'"e"})}};"not"[]{"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}}}}}}}}}}}} }

interactive nuprl_sends__rule0   :
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in "list"[]{'"T"} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends0"[]{'"B";'"T";'"k";'"l";'"tg";'"f"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends0"[]{'"B";'"T";'"k";'"l";'"tg";'"f"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"B"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"list"[]{"set"[]{"es-E"[]{'"es"};"e'"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}}}};"L"."and"[]{"all"[]{"es-E"[]{'"es"};"e'"."iff"[]{"mem"[]{'"e'";'"L";"es-E"[]{'"es"}};"cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e1"."all"[]{"es-E"[]{'"es"};"e2"."implies"[]{"l_before"[]{'"e1";'"e2";'"L";"es-E"[]{'"es"}};"es-locl"[]{'"es";'"e1";'"e2"}}}};"equal"[]{"list"[]{'"T"};"map"[]{"lambda"[]{"e'"."es-val"[]{'"es";'"e'"}};'"L"};('"f" "es-val"[]{'"es";'"e"})}}}}}}}}}}}} }

interactive nuprl_unconditional__send__rule0   :
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in '"T" }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends0"[]{'"B";'"T";'"k";'"l";'"tg";"lambda"[]{"b"."cons"[]{('"f" '"b");"nil"[]{}}}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sends0"[]{'"B";'"T";'"k";'"l";'"tg";"lambda"[]{"b"."cons"[]{('"f" '"b");"nil"[]{}}}}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"B"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"lsrc"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"and"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"};"equal"[]{'"T";"es-val"[]{'"es";'"e'"};('"f" "es-val"[]{'"es";'"e"})}}}}}}}}}}}} }

interactive nuprl_s__init__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-init"[]{'"x";'"T";'"v"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-init"[]{'"x";'"T";'"v"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};"equal"[]{'"T";"es-when"[]{'"es";'"x";'"e"};'"v"}}}}}}}}} }

interactive nuprl_s__frame__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-frame"[]{'"L";'"T";'"x"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-frame"[]{'"L";'"T";'"x"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}};"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"implies"[]{"not"[]{"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}}}}} }

interactive nuprl_s__pre__init__rule1  '"A" '"T" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"a" '"c" '"x" '"i"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"c" in '"A" }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"T" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-pre-init1"[]{'"x";'"A";'"c";'"a";'"T";"x", "v".'"P"['"x";'"v"]}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-pre-init1"[]{'"x";'"A";'"c";'"a";'"T";"x", "v".'"P"['"x";'"v"]}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"and"[]{"and"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"A"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};"equal"[]{'"A";"es-when"[]{'"es";'"x";'"e"};'"c"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};'"P"["es-when"[]{'"es";'"x";'"e"};"es-val"[]{'"es";'"e"}]}}};"implies"[]{"exists"[]{'"T";"v".'"P"['"c";'"v"]};"exists"[]{"es-E"[]{'"es"};"e"."and"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"all"[]{'"T";"v"."not"[]{'"P"["es-after"[]{'"es";'"x";'"e"};'"v"]}}}}}}}}}}}} }

interactive nuprl_frame__rule0   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-frame"[]{"nil"[]{};'"T";'"x"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-frame"[]{"nil"[]{};'"T";'"x"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}} }

interactive nuprl_frame__rule1   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"k";"nil"[]{}};'"T";'"x"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"k";"nil"[]{}};'"T";'"x"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."and"[]{"implies"[]{"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}};"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}}}} }

interactive nuprl_frame__rule2   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"a";"cons"[]{'"b";"nil"[]{}}};'"T";'"x"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"a";"cons"[]{'"b";"nil"[]{}}};'"T";'"x"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."and"[]{"implies"[]{"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"};"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"b"}}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"b"}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}}}}} }

interactive nuprl_frame__rule3   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"a";"cons"[]{'"b";"cons"[]{'"c";"nil"[]{}}}};'"T";'"x"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-frame"[]{"cons"[]{'"a";"cons"[]{'"b";"cons"[]{'"c";"nil"[]{}}}};'"T";'"x"}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"alle-at"[]{'"es";'"i";"e"."and"[]{"implies"[]{"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"b"};"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"c"}}}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"a"}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"b"}};"implies"[]{"not"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"c"}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}}}}}} }

interactive nuprl_s__sframe__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{'"i";"ma-single-sframe"[]{'"L";'"l";'"tg"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{'"i";"ma-single-sframe"[]{'"L";'"l";'"tg"}};'"D"};"d-realizes"[level:l]{'"D";"es"."all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"not"[]{"assert"[]{"is_nil"[]{"es-tg-sends"[]{'"es";'"l";'"tg";'"e"}}}};"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}}}}}}}} }

interactive nuprl_better__sframe__rule   :
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-single-sframe"[]{'"L";'"l";'"tg"}};'"D"};"d-realizes"[level:l]{'"D";"es"."all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};"ldst"[]{'"l"}};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"rcv"[]{'"l";'"tg"}};"mem"[]{"es-kind"[]{'"es";"es-sender"[]{'"es";'"e"}};'"L";"Knd"[]{}}}}}}}}} }

interactive nuprl_unconditional__sframe__send1__rule   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H>; "equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};'"k"}  >- "equal"[]{"univ"[level:l]{};'"T";'"B"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in '"T" }  -->
   sequent { <H> >- "cand"[]{("m-sys-at"[]{"lsrc"[]{'"l"};"ma-join"[]{"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{(('"f" '"a") '"b");"nil"[]{}}}}};"ma-single-sframe"[]{"cons"[]{'"k";"nil"[]{}};'"l";'"tg"}}} in "dsys"[level:l]{});"all"[]{"dsys"[level:l]{};"D"."implies"[]{"d-sub"[level:l]{"m-sys-at"[]{"lsrc"[]{'"l"};"ma-join"[]{"ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"k";'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{(('"f" '"a") '"b");"nil"[]{}}}}};"ma-single-sframe"[]{"cons"[]{'"k";"nil"[]{}};'"l";'"tg"}}};'"D"};"d-realizes"[level:l]{'"D";"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";"lsrc"[]{'"l"};'"x"};'"A"};"es-only-sender"[]{'"es";'"k";'"B";'"l";'"tg";'"T";"s", "v".(('"f" ('"s" '"x")) '"v")}}}}}} }


(**** display forms ****)


dform nuprl_s__decl_df : except_mode[src] :: "s-decl"[level:l]{} =
   `"Decl"


dform nuprl_s__decl__null_df : except_mode[src] :: "s-decl-null"[]{} =
   `""


dform nuprl_s__declared_df : except_mode[src] :: "s-declared"[]{'"d";'"a"} =
   `"" slot{'"d"} `"(" slot{'"a"} `")"


dform nuprl_m__at_df : except_mode[src] :: "m-at"[]{'"M";'"i"} =
   `"(@" slot{'"i"} `" " slot{'"M"} `")"


dform nuprl_in__decl_df : except_mode[src] :: "in-decl"[level:l]{'"i"} =
   `"InDecl(" slot{'"i"} `")"


dform nuprl_out__decl_df : except_mode[src] :: "out-decl"[level:l]{'"i"} =
   `"OutDecl(" slot{'"i"} `")"


dform nuprl_s__in__declared_df : except_mode[src] :: "s-in-declared"[]{'"d";'"p"} =
   `"" slot{'"d"} `"(" slot{'"p"} `")"


dform nuprl_s__out__declared_df : except_mode[src] :: "s-out-declared"[]{'"d";'"p"} =
   `"" slot{'"d"} `"(" slot{'"p"} `")"


dform nuprl_s__valtype_df : except_mode[src] :: "s-valtype"[]{'"k";'"da";'"din"} =
   `"Valtype(" slot{'"k"} `";" slot{'"da"} `";" slot{'"din"} `")"


dform nuprl_s__state_df : except_mode[src] :: "ma-state"[]{'"ds"} =
   `"State(" slot{'"ds"} `")"


dform nuprl_msystem_df : except_mode[src] :: "msystem"[level:l]{} =
   `"System"


dform nuprl_m__sys__null_df : except_mode[src] :: "m-sys-null"[]{} =
   `""


dform nuprl_m__sys__at_df : except_mode[src] :: "m-sys-at"[]{'"i";'"A"} =
   `"@" slot{'"i"} `": " slot{'"A"} `""


dform nuprl_m__sys__compatible_df : except_mode[src] :: "m-sys-compatible"[level:l]{'"A";'"B"} =
   `"" slot{'"A"} `" || " slot{'"B"} `""


dform nuprl_m__sys__join_df : except_mode[src] :: "m-sys-join"[]{'"A";'"B"} =
   `"" slot{'"A"} `" " oplus `" " slot{'"B"} `""


dform nuprl_interface__link_df : except_mode[src] :: "interface-link"[]{'"A";'"B";'"l";'"tg"} =
   `"interface-link(" slot{'"A"} `";" slot{'"B"} `";" slot{'"l"} `";" slot{'"tg"}
    `")"


dform nuprl_interface__compatible_df : except_mode[src] :: "interface-compatible"[]{'"A";'"B"} =
   `"interface-compatible(" slot{'"A"} `";" slot{'"B"} `")"


dform nuprl_m__sys__join__list_df : except_mode[src] :: "m-sys-join-list"[]{'"L"} =
   `"" oplus `"(" slot{'"L"} `")"


dform nuprl_s__dsys_df : except_mode[src] :: '"M" =
   `"Dsys(" slot{'"M"} `")"


dform nuprl_dsys__null_df : except_mode[src] :: "dsys-null"[]{} =
   `"DsysNull"


dform nuprl_Rcv_df : except_mode[src] :: "Rcv"[]{'"l";'"tg"} =
   `"Rcv(" slot{'"l"} `";" slot{'"tg"} `")"


