extends Ma_general__theory


define unfold_s__decl : "s-decl"[level:l]{} <-->
      "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}}


define unfold_s__decl__null : "s-decl-null"[]{} <-->
      "fpf-empty"[]{}


define unfold_s__declared : "s-declared"[]{'"d";'"a"} <-->
      "fpf-cap"[]{'"d";"id-deq"[]{};'"a";"top"[]{}}


define unfold_m__at : "m-at"[]{'"M";'"i"} <-->
      "lambda"[]{"j"."ifthenelse"[]{(("eqof"[]{"id-deq"[]{}} '"j") '"i");'"M";"ma-empty"[]{}}}


define unfold_in__decl : "in-decl"[level:l]{'"i"} <-->
      "fpf"[]{"set"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"p"."equal"[]{"Id"[]{};"ldst"[]{"fst"[]{'"p"}};'"i"}};"ltg"."univ"[level:l]{}}


define unfold_out__decl : "out-decl"[level:l]{'"i"} <-->
      "fpf"[]{"set"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"p"."equal"[]{"Id"[]{};"lsrc"[]{"fst"[]{'"p"}};'"i"}};"ltg"."univ"[level:l]{}}


define unfold_s__in__declared : "s-in-declared"[]{'"d";'"p"} <-->
      "fpf-cap"[]{'"d";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};'"p";"top"[]{}}


define unfold_s__out__declared : "s-out-declared"[]{'"d";'"p"} <-->
      "fpf-cap"[]{'"d";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};'"p";"top"[]{}}


define unfold_s__valtype : "s-valtype"[]{'"k";'"da";'"din"} <-->
      "kindcase"[]{'"k";"a"."fpf-cap"[]{'"da";"id-deq"[]{};'"a";"top"[]{}};"l", "tg"."fpf-cap"[]{'"din";"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{'"l";'"tg"};"top"[]{}}}


define unfold_s__state : "s-state"[]{'"ds"} <-->
      "fun"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}


define unfold_msystem : "msystem"[level:l]{} <-->
      "set"[]{"fun"[]{"Id"[]{};"loc"."msga"[level:l]{}};"M"."all"[]{"Id"[]{};"loc"."ma-feasible"[]{('"M" '"loc")}}}


define unfold_m__sys__null : "m-sys-null"[]{} <-->
      "lambda"[]{"i"."ma-empty"[]{}}


define unfold_m__sys__at : "m-sys-at"[]{'"i";'"A"} <-->
      "lambda"[]{"j"."ifthenelse"[]{"eq_id"[]{'"j";'"i"};'"A";"ma-empty"[]{}}}


define unfold_m__sys__compatible : "m-sys-compatible"[level:l]{'"A";'"B"} <-->
      "all"[]{"Id"[]{};"i"."and"[]{"ma-compatible"[level:l]{('"A" '"i");('"B" '"i")};"and"[]{"ma-frame-compatible"[]{('"A" '"i");('"B" '"i")};"ma-sframe-compatible"[]{('"A" '"i");('"B" '"i")}}}}


define unfold_m__sys__join : "m-sys-join"[]{'"A";'"B"} <-->
      "lambda"[]{"i"."ma-join"[]{('"A" '"i");('"B" '"i")}}


define unfold_interface__link : "interface-link"[]{'"A";'"B";'"l";'"tg"} <-->
      "and"[]{"ma-declm"[]{('"A" "lsrc"[]{'"l"});'"l";'"tg"};"and"[]{"ma-declm"[]{('"B" "ldst"[]{'"l"});'"l";'"tg"};"not"[]{"ma-declm"[]{('"B" "lsrc"[]{'"l"});'"l";'"tg"}}}}


define unfold_interface__compatible : "interface-compatible"[]{'"A";'"B"} <-->
      "all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."and"[]{"implies"[]{"interface-link"[]{'"A";'"B";'"l";'"tg"};"subtype"[]{"ma-dout"[]{('"A" "lsrc"[]{'"l"});'"l";'"tg"};"ma-din"[]{('"B" "ldst"[]{'"l"});'"l";'"tg"}}};"implies"[]{"interface-link"[]{'"B";'"A";'"l";'"tg"};"subtype"[]{"ma-dout"[]{('"B" "lsrc"[]{'"l"});'"l";'"tg"};"ma-din"[]{('"A" "ldst"[]{'"l"});'"l";'"tg"}}}}}}


define unfold_m__sys__join__list : "m-sys-join-list"[]{'"L"} <-->
      "reduce"[]{"lambda"[]{"A"."lambda"[]{"B"."m-sys-join"[]{'"A";'"B"}}};"m-sys-null"[]{};'"L"}


define unfold_s__dsys : "s-dsys"[]{'"M"} <-->
      '"M"


define unfold_dsys__null : "dsys-null"[]{} <-->
      "s-dsys"[]{"m-sys-null"[]{}}


define unfold_Rcv : "Rcv"[]{'"l";'"tg"} <-->
      "rcv"[]{'"l";'"tg"}


