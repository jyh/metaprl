extends Ma_diagonal__compat__lemmas_object_directory

open Dtactic


define unfold_rset : "rset"[]{'"R"} <-->
      "set"[]{"Id"[]{};"i"."assert"[]{('"R" '"i")}}


interactive nuprl_rset_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   sequent { <H> >- ("rset"[]{'"R"} in "univ"[level:l]{}) }

interactive nuprl_rset_wf_type {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "type"{"rset"[]{'"R"}} }

define unfold_ring : "ring"[]{'"R";'"in";'"out"} <-->
      "and"[]{"cand"[]{"all"[]{"rset"[]{'"R"};"i"."cand"[]{"and"[]{"assert"[]{('"R" "lsrc"[]{('"in" '"i")})};"assert"[]{('"R" "ldst"[]{('"out" '"i")})}};"and"[]{"equal"[]{"Id"[]{};"lsrc"[]{('"out" '"i")};'"i"};"and"[]{"equal"[]{"Id"[]{};"ldst"[]{('"in" '"i")};'"i"};"and"[]{"equal"[]{"IdLnk"[]{};('"in" "ldst"[]{('"out" '"i")});('"out" '"i")};"equal"[]{"IdLnk"[]{};('"out" "lsrc"[]{('"in" '"i")});('"in" '"i")}}}}}};"all"[]{"rset"[]{'"R"};"i"."all"[]{"rset"[]{'"R"};"j"."exists"[]{"nat_plus"[]{};"k"."equal"[]{"Id"[]{};("fun_exp"[]{"lambda"[]{"x"."ldst"[]{('"out" '"x")}};'"k"} '"i");'"j"}}}}};"rset"[]{'"R"}}


interactive nuprl_ring_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("ring"[]{'"R";'"in";'"out"} in "univ"[level:l]{}) }

define unfold_rnext : "rnext"[]{'"R";'"in";'"out";'"i"} <-->
      "ldst"[]{('"out" '"i")}


interactive nuprl_rnext_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- ("rnext"[]{'"R";'"in";'"out";'"i"} in "rset"[]{'"R"}) }

define unfold_rprev : "rprev"[]{'"R";'"in";'"out";'"i"} <-->
      "lsrc"[]{('"in" '"i")}


interactive nuprl_rprev_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- ("rprev"[]{'"R";'"in";'"out";'"i"} in "rset"[]{'"R"}) }

define unfold_rdist : "rdist"[]{'"R";'"in";'"out";'"i";'"j"} <-->
      "add"[]{"mu"[]{"lambda"[]{"k"."eq_id"[]{("fun_exp"[]{"lambda"[]{"x"."rnext"[]{'"R";'"in";'"out";'"x"}};"add"[]{'"k";"number"[1:n]{}}} '"i");'"j"}}};"number"[1:n]{}}


interactive nuprl_rdist_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- ("rdist"[]{'"R";'"in";'"out";'"i";'"j"} in "nat_plus"[]{}) }

interactive nuprl_rdist__property   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"rset"[]{'"R"};("fun_exp"[]{"lambda"[]{"x"."rnext"[]{'"R";'"in";'"out";'"x"}};"rdist"[]{'"R";'"in";'"out";'"i";'"j"}} '"i");'"j"};"all"[]{"nat_plus"[]{};"k"."implies"[]{"lt"[]{'"k";"rdist"[]{'"R";'"in";'"out";'"i";'"j"}};"not"[]{"equal"[]{"rset"[]{'"R"};("fun_exp"[]{"lambda"[]{"x"."rnext"[]{'"R";'"in";'"out";'"x"}};'"k"} '"i");'"j"}}}}}} }

interactive nuprl_rnext__rprev   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "equal"[]{"rset"[]{'"R"};"rnext"[]{'"R";'"in";'"out";"rprev"[]{'"R";'"in";'"out";'"j"}};'"j"} }

interactive nuprl_rnext__one__one  '"out" '"in"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "equal"[]{"rset"[]{'"R"};"rnext"[]{'"R";'"in";'"out";'"i"};"rnext"[]{'"R";'"in";'"out";'"j"}} }  -->
   sequent { <H> >- "equal"[]{"rset"[]{'"R"};'"i";'"j"} }

interactive nuprl_rdist__rprev   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"R"} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"rset"[]{'"R"};'"i";"rprev"[]{'"R";'"in";'"out";'"j"}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rdist"[]{'"R";'"in";'"out";'"i";"rprev"[]{'"R";'"in";'"out";'"j"}};"sub"[]{"rdist"[]{'"R";'"in";'"out";'"i";'"j"};"number"[1:n]{}}} }

interactive nuprl_ring__list  '"out" '"in"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"in" '"x" in "IdLnk"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"R"} >- '"out" '"x" in "IdLnk"[]{} }  -->
   sequent { <H> >- "ring"[]{'"R";'"in";'"out"} }  -->
   sequent { <H> >- "exists"[]{"list"[]{"rset"[]{'"R"}};"L"."and"[]{"lt"[]{"number"[0:n]{};"length"[]{'"L"}};"all"[]{"rset"[]{'"R"};"i"."mem"[]{'"i";'"L";"rset"[]{'"R"}}}}} }

interactive nuprl_rset_sq   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "sq_type"[]{"rset"[]{'"R"}} }

interactive nuprl_decidable__rset_equal   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"R" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "rset"[]{'"R"} }  -->
   [wf] sequent { <H> >- '"y" in "rset"[]{'"R"} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"rset"[]{'"R"};'"x";'"y"}} }

define unfold_bi__graph : "bi-graph"[]{'"G";'"to";'"from"} <-->
      "all"[]{"rset"[]{'"G"};"i"."and"[]{"and"[]{"l_all"[]{('"to" '"i");"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"and"[]{"assert"[]{('"G" "lsrc"[]{'"l"})};"and"[]{"mem"[]{'"l";('"from" "lsrc"[]{'"l"});"IdLnk"[]{}};"mem"[]{"lnk-inv"[]{'"l"};('"from" '"i");"IdLnk"[]{}}}}}};"l_all"[]{('"from" '"i");"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"};"and"[]{"assert"[]{('"G" "ldst"[]{'"l"})};"and"[]{"mem"[]{'"l";('"to" "ldst"[]{'"l"});"IdLnk"[]{}};"mem"[]{"lnk-inv"[]{'"l"};('"to" '"i");"IdLnk"[]{}}}}}}};"and"[]{"no_repeats"[]{"IdLnk"[]{};('"to" '"i")};"no_repeats"[]{"IdLnk"[]{};('"from" '"i")}}}}


interactive nuprl_bi__graph_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- ("bi-graph"[]{'"G";'"to";'"from"} in "univ"[level:l]{}) }

define unfold_bi__graph__edge : "bi-graph-edge"[]{'"G";'"to";'"from"} <-->
      "set"[]{"IdLnk"[]{};"l"."exists"[]{"rset"[]{'"G"};"i"."mem"[]{'"l";('"from" '"i");"IdLnk"[]{}}}}


interactive nuprl_bi__graph__edge_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- ("bi-graph-edge"[]{'"G";'"to";'"from"} in "univ"[level:l]{}) }

interactive nuprl_bi__graph__edge_wf_type {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "type"{"bi-graph-edge"[]{'"G";'"to";'"from"}} }

interactive nuprl_inv__is__edge   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- ("lnk-inv"[]{'"l"} in "bi-graph-edge"[]{'"G";'"to";'"from"}) }

interactive nuprl_src__edge  '"from" '"to"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"u" in "bi-graph-edge"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- ("lsrc"[]{'"u"} in "rset"[]{'"T"}) }

interactive nuprl_dst__edge  '"from" '"to"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"u" in "bi-graph-edge"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- ("ldst"[]{'"u"} in "rset"[]{'"T"}) }

define unfold_bi__graph__to : "bi-graph-to"[]{'"G";'"to";'"from";'"i"} <-->
      ('"to" '"i")


interactive nuprl_bi__graph__to_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- ("bi-graph-to"[]{'"G";'"to";'"from";'"i"} in "list"[]{"bi-graph-edge"[]{'"G";'"to";'"from"}}) }

define unfold_bi__graph__from : "bi-graph-from"[]{'"G";'"to";'"from";'"i"} <-->
      ('"from" '"i")


interactive nuprl_bi__graph__from_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- ("bi-graph-from"[]{'"G";'"to";'"from";'"i"} in "list"[]{"bi-graph-edge"[]{'"G";'"to";'"from"}}) }

define unfold_bi__graph__inv : "bi-graph-inv"[]{'"G";'"to";'"from";'"l"} <-->
      "lnk-inv"[]{'"l"}


interactive nuprl_bi__graph__inv_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- ("bi-graph-inv"[]{'"G";'"to";'"from";'"l"} in "bi-graph-edge"[]{'"G";'"to";'"from"}) }

interactive nuprl_edge__to   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"e";"bi-graph-to"[]{'"G";'"to";'"from";'"i"};"bi-graph-edge"[]{'"G";'"to";'"from"}};"equal"[]{"Id"[]{};"ldst"[]{'"e"};'"i"}} }

interactive nuprl_to__edge   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"mem"[]{'"e";"bi-graph-to"[]{'"G";'"to";'"from";'"i"};"IdLnk"[]{}};('"e" in "bi-graph-edge"[]{'"G";'"to";'"from"})}} }

interactive nuprl_to__member__edge   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"mem"[]{'"e";"bi-graph-to"[]{'"G";'"to";'"from";'"i"};"IdLnk"[]{}};"mem"[]{'"e";"bi-graph-to"[]{'"G";'"to";'"from";'"i"};"bi-graph-edge"[]{'"G";'"to";'"from"}}}} }

interactive nuprl_edge__from   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"e";"bi-graph-from"[]{'"G";'"to";'"from";'"i"};"bi-graph-edge"[]{'"G";'"to";'"from"}};"equal"[]{"Id"[]{};"lsrc"[]{'"e"};'"i"}} }

interactive nuprl_edge__inv__to   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{"bi-graph-inv"[]{'"G";'"to";'"from";'"e"};"bi-graph-to"[]{'"G";'"to";'"from";'"i"};"bi-graph-edge"[]{'"G";'"to";'"from"}};"equal"[]{"Id"[]{};"lsrc"[]{'"e"};'"i"}} }

interactive nuprl_edge__inv__from   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"e" in "bi-graph-edge"[]{'"G";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"G"} }  -->
   sequent { <H> >- "bi-graph"[]{'"G";'"to";'"from"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{"bi-graph-inv"[]{'"G";'"to";'"from";'"e"};"bi-graph-from"[]{'"G";'"to";'"from";'"i"};"bi-graph-edge"[]{'"G";'"to";'"from"}};"equal"[]{"Id"[]{};"ldst"[]{'"e"};'"i"}} }

define unfold_bi__tree : "bi-tree"[]{'"T";'"to";'"from"} <-->
      "and"[]{"bi-graph"[]{'"T";'"to";'"from"};"and"[]{"and"[]{"all"[]{"rset"[]{'"T"};"i"."all"[]{"rset"[]{'"T"};"j"."exists"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};"p"."and"[]{"lconnects"[]{'"p";'"i";'"j"};"all"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};"q"."implies"[]{"lconnects"[]{'"q";'"i";'"j"};"equal"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};'"q";'"p"}}}}}}};"exists"[]{"list"[]{"rset"[]{'"T"}};"L"."all"[]{"rset"[]{'"T"};"i"."mem"[]{'"i";'"L";"rset"[]{'"T"}}}}};"rset"[]{'"T"}}}


interactive nuprl_bi__tree_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"G" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"G"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- ("bi-tree"[]{'"G";'"to";'"from"} in "univ"[level:l]{}) }

interactive nuprl_bi__tree__diameter   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"n"."all"[]{"list"[]{"bi-graph-edge"[]{'"T";'"to";'"from"}};"p"."implies"[]{"lpath"[]{'"p"};"le"[]{"length"[]{'"p"};'"n"}}}} }

define unfold_spanner : "spanner"[]{'"f";'"T";'"to";'"from"} <-->
      "and"[]{"all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."equal"[]{"bool"[]{};('"f" '"l");"bnot"[]{('"f" "bi-graph-inv"[]{'"T";'"to";'"from";'"l"})}}};"all"[]{"rset"[]{'"T"};"i"."all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l1"."all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l2"."implies"[]{"mem"[]{'"l1";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"implies"[]{"mem"[]{'"l2";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"implies"[]{"not"[]{"equal"[]{"IdLnk"[]{};'"l1";'"l2"}};"or"[]{"assert"[]{('"f" '"l1")};"assert"[]{('"f" '"l2")}}}}}}}}}


interactive nuprl_spanner_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "bi-graph-edge"[]{'"T";'"to";'"from"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- ("spanner"[]{'"f";'"T";'"to";'"from"} in "univ"[level:l]{}) }

define unfold_spanner__root : "spanner-root"[]{'"f";'"T";'"to";'"from";'"i"} <-->
      "all"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."implies"[]{"mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}};"assert"[]{('"f" '"l")}}}


interactive nuprl_spanner__root_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "bi-graph-edge"[]{'"T";'"to";'"from"} >- '"f" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- ("spanner-root"[]{'"f";'"T";'"to";'"from";'"i"} in "univ"[level:l]{}) }

interactive nuprl_spanner__root__exists   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "bi-graph-edge"[]{'"T";'"to";'"from"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "spanner"[]{'"f";'"T";'"to";'"from"} }  -->
   sequent { <H> >- "exists"[]{"rset"[]{'"T"};"i"."spanner-root"[]{'"f";'"T";'"to";'"from";'"i"}} }

interactive nuprl_spanner__root__unique  '"from" '"to" '"f"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "bi-graph-edge"[]{'"T";'"to";'"from"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "spanner"[]{'"f";'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"j" in "rset"[]{'"T"} }  -->
   sequent { <H> >- "spanner-root"[]{'"f";'"T";'"to";'"from";'"i"} }  -->
   sequent { <H> >- "spanner-root"[]{'"f";'"T";'"to";'"from";'"j"} }  -->
   sequent { <H> >- "equal"[]{"rset"[]{'"T"};'"i";'"j"} }

define unfold_update : "update"[]{'"eq";'"f";'"x";'"v"} <-->
      "lambda"[]{"y"."ifthenelse"[]{(('"eq" '"y") '"x");'"v";('"f" '"y")}}


interactive nuprl_update_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"A" >- '"eq" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B" }  -->
   sequent { <H> >- ("update"[]{'"eq";'"f";'"x";'"v"} in "fun"[]{'"A";"".'"B"}) }


(**** display forms ****)


dform nuprl_add_rec_module__args__df : except_mode[src] :: "!mk_create_realizer_args"[name:t]{'"a"} =
   `"Create Realizer : " slot{'"name"} `"" sbreak["",""] `"  " slot{'"a"} `""
    sbreak["",""] `" (* Some comment *)"


dform nuprl_rset_df : except_mode[src] :: "rset"[]{'"R"} =
   `"|" slot{'"R"} `"|"


dform nuprl_ring_df : except_mode[src] :: "ring"[]{'"R";'"in";'"out"} =
   `"ring(" slot{'"R"} `";" slot{'"in"} `";" slot{'"out"} `")"


dform nuprl_rnext_df : except_mode[src] :: "rnext"[]{'"R";'"in";'"out";'"i"} =
   `"rnext(" slot{'"R"} `";" slot{'"in"} `";" slot{'"out"} `";" slot{'"i"} `")"

dform nuprl_rnext_df : except_mode[src] :: "rnext"[]{'"R";'"in";'"out";'"i"} =
   `"n(" slot{'"i"} `")"


dform nuprl_rprev_df : except_mode[src] :: "rprev"[]{'"R";'"in";'"out";'"i"} =
   `"rprev(" slot{'"R"} `";" slot{'"in"} `";" slot{'"out"} `";" slot{'"i"} `")"

dform nuprl_rprev_df : except_mode[src] :: "rprev"[]{'"R";'"in";'"out";'"i"} =
   `"p(" slot{'"i"} `")"


dform nuprl_rdist_df : except_mode[src] :: "rdist"[]{'"R";'"in";'"out";'"i";'"j"} =
   `"rdist(" slot{'"R"} `";" slot{'"in"} `";" slot{'"out"} `";" slot{'"i"} `";"
    slot{'"j"} `")"

dform nuprl_rdist_df : except_mode[src] :: "rdist"[]{'"R";'"in";'"out";'"i";'"j"} =
   `"d(" slot{'"i"} `";" slot{'"j"} `")"


dform nuprl_bi__graph_df : except_mode[src] :: "bi-graph"[]{'"G";'"to";'"from"} =
   `"bi-graph(" slot{'"G"} `";" slot{'"to"} `";" slot{'"from"} `")"


dform nuprl_bi__graph__edge_df : except_mode[src] :: "bi-graph-edge"[]{'"G";'"to";'"from"} =
   `"Edge(" slot{'"G"} `";" slot{'"to"} `";" slot{'"from"} `")"

dform nuprl_bi__graph__edge_df : except_mode[src] :: "bi-graph-edge"[]{'"G";'"to";'"from"} =
   `"Edge(" slot{'"G"} `")"


dform nuprl_bi__graph__to_df : except_mode[src] :: "bi-graph-to"[]{'"G";'"to";'"from";'"i"} =
   `"bi-graph-to(" slot{'"G"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"i"}
    `")"

dform nuprl_bi__graph__to_df : except_mode[src] :: "bi-graph-to"[]{'"G";'"to";'"from";'"i"} =
   `"to(" slot{'"i"} `")"


dform nuprl_bi__graph__from_df : except_mode[src] :: "bi-graph-from"[]{'"G";'"to";'"from";'"i"} =
   `"bi-graph-from(" slot{'"G"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"i"}
    `")"

dform nuprl_bi__graph__from_df : except_mode[src] :: "bi-graph-from"[]{'"G";'"to";'"from";'"i"} =
   `"from(" slot{'"i"} `")"


dform nuprl_bi__graph__inv_df : except_mode[src] :: "bi-graph-inv"[]{'"G";'"to";'"from";'"l"} =
   `"bi-graph-inv(" slot{'"G"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"l"}
    `")"

dform nuprl_bi__graph__inv_df : except_mode[src] :: "bi-graph-inv"[]{'"G";'"to";'"from";'"l"} =
   `"inverse(" slot{'"l"} `")"


dform nuprl_bi__tree_df : except_mode[src] :: "bi-tree"[]{'"T";'"to";'"from"} =
   `"bi-tree(" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"} `")"


dform nuprl_spanner_df : except_mode[src] :: "spanner"[]{'"f";'"T";'"to";'"from"} =
   `"spanner(" slot{'"f"} `";" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"} `")"


dform nuprl_spanner__root_df : except_mode[src] :: "spanner-root"[]{'"f";'"T";'"to";'"from";'"i"} =
   `"spanner-root(" slot{'"f"} `";" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"}
    `";" slot{'"i"} `")"


dform nuprl_update_df : except_mode[src] :: "update"[]{'"eq";'"f";'"x";'"v"} =
   `"update(" slot{'"eq"} `";" slot{'"f"} `";" slot{'"x"} `";" slot{'"v"} `")"

dform nuprl_update_df : except_mode[src] :: "update"[]{'"eq";'"f";'"x";'"v"} =
   `"" slot{'"f"} `"[" slot{'"x"} `":=" szone sbreak["",""] ezone `"" slot{'"v"}
    `"]"


