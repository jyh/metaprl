extends Ma_diagonal__compat__lemmas_object_directory


define unfold_rset : "rset"[]{'"R"} <-->
      "set"[]{"Id"[]{};"i"."assert"[]{('"R" '"i")}}


define unfold_ring : "ring"[]{'"R";'"in";'"out"} <-->
      "and"[]{"cand"[]{"all"[]{"rset"[]{'"R"};"i"."cand"[]{"and"[]{"assert"[]{('"R" "lsrc"[]{('"in" '"i")})};"assert"[]{('"R" "ldst"[]{('"out" '"i")})}};"and"[]{"equal"[]{"Id"[]{};"lsrc"[]{('"out" '"i")};'"i"};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{('"in" '"i")};'"i"};"and"[]{"equal"[]{"IdLnk"[]{};('"in" "ldst"[]{('"out" '"i")});('"out" '"i")};"equal"[]{"IdLnk"[]{};('"out" "lsrc"[]{('"in" '"i")});('"in" '"i")}}}}}};"all"[]{"rset"[]{'"R"};"i"."all"[]{"rset"[]{'"R"};"j"."exists"[]{"nat_plus"[]{};"k"."equal"[]{"Id"[]{};("fun_exp"[]{"lambda"[]{"x"."ldst"[]{('"out" '"x")}};'"k"} '"i");'"j"}}}}};"rset"[]{'"R"}}


define unfold_rnext : "rnext"[]{'"R";'"in";'"out";'"i"} <-->
      "ldst"[]{('"out" '"i")}


define unfold_rprev : "rprev"[]{'"R";'"in";'"out";'"i"} <-->
      "lsrc"[]{('"in" '"i")}


define unfold_rdist : "rdist"[]{'"R";'"in";'"out";'"i";'"j"} <-->
      "add"[]{"mu"[]{"lambda"[]{"k"."eq_id"[]{("fun_exp"[]{"lambda"[]{"x"."rnext"[]{'"R";'"in";'"out";'"x"}};"add"[]{'"k";"number"[1:n]{}}} '"i");'"j"}}};"number"[1:n]{}}


define unfold_bi__graph : "bi-graph"[]{'"G";'"to";'"from"} <-->
      "all"[]{"rset"[]{'"G"};"i"."and"[]{"and"[]{"l_all"[]{('"to" '"i");"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"and"[]{"assert"[]{('"G" "lsrc"[]{'"l"})};"and"[]{"mem"[]{'"l";('"from" "lsrc"[]{'"l"});"IdLnk"[]{}};"mem"[]{"lnk-inv"[]{'"l"};('"from" '"i");"IdLnk"[]{}}}}}};"l_all"[]{('"from" '"i");"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"};"and"[]{"assert"[]{('"G" "ldst"[]{'"l"})};"and"[]{"mem"[]{'"l";('"to" "ldst"[]{'"l"});"IdLnk"[]{}};"mem"[]{"lnk-inv"[]{'"l"};('"to" '"i");"IdLnk"[]{}}}}}}};"and"[]{"no_repeats"[]{"IdLnk"[]{};('"to" '"i")};"no_repeats"[]{"IdLnk"[]{};('"from" '"i")}}}}


define unfold_bi__graph__edge : "bi-graph-edge"[]{'"G";'"to";'"from"} <-->
      "set"[]{"IdLnk"[]{};"l"."exists"[]{"rset"[]{'"G"};"i"."mem"[]{'"l";('"from" '"i");"IdLnk"[]{}}}}


define unfold_bi__graph__to : "bi-graph-to"[]{'"G";'"to";'"from";'"i"} <-->
      ('"to" '"i")


define unfold_bi__graph__from : "bi-graph-from"[]{'"G";'"to";'"from";'"i"} <-->
      ('"from" '"i")


define unfold_bi__graph__inv : "bi-graph-inv"[]{'"G";'"to";'"from";'"l"} <-->
      "lnk-inv"[]{'"l"}


define unfold_bi__tree : "bi-tree"[]{'"T";'"to";'"from"} <-->
      "and"[]{"bi-graph"[]{'"T";'"to";'"from"};"and"[]{"and"[]{"all"[]{"rset"[]{'"T"};"i"."all"[]{"rset"[]{'"T"};"j"."exists"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};"p"."and"[]{"lconnects"[]{'"p";'"i";'"j"};"all"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};"q"."implies"[]{"lconnects"[]{'"q";'"i";'"j"};"equal"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};'"q";'"p"}}}}}}};"exists"[]{"list"[]{"rset"[]{'"T"}};"L"."all"[]{"rset"[]{'"T"};"i"."mem"[]{'"i";'"L";"rset"[]{'"T"}}}}};"rset"[]{'"T"}}}


define unfold_spanner : "spanner"[]{'"f";'"T";'"to";'"from"} <-->
      "and"[]{"all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."equal"[]{"bool"[]{};('"f" '"l");"bnot"[]{('"f" "bi-graph-inv"[]{'"T";'"to";'"from";'"l"})}}};"all"[]{"rset"[]{'"T"};"i"."all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l1"."all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l2"."implies"[]{"mem"[]{'"l1";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"implies"[]{"mem"[]{'"l2";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"implies"[]{"not"[]{"equal"[]{"IdLnk"[]{};'"l1";'"l2"}};"or"[]{"assert"[]{('"f" '"l1")};"assert"[]{('"f" '"l2")}}}}}}}}}


define unfold_spanner__root : "spanner-root"[]{'"f";'"T";'"to";'"from";'"i"} <-->
      "all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."implies"[]{"mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"assert"[]{('"f" '"l")}}}


define unfold_update : "update"[]{'"eq";'"f";'"x";'"v"} <-->
      "lambda"[]{"y"."ifthenelse"[]{(('"eq" '"y") '"x");'"v";('"f" '"y")}}


