extends Ma_ring__leader1_object_directory

open Dtactic


define unfold_tip__msg : "tip-msg"[]{} <-->
      "union"[]{"nat"[]{};"unit"[]{}}


interactive nuprl_tip__msg_wf {| intro[] |}   :
   sequent { <H> >- ("tip-msg"[]{} in "univ"[level:l]{}) }

interactive nuprl_tip__msg_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"tip-msg"[]{}} }

define unfold_tip__count : "tip-count"[]{'"T";'"to";'"from";'"i";'"ch"} <-->
      "length"[]{"filter"[]{"lambda"[]{"l"."bnot"[]{('"ch" '"l")}};"bi-graph-to"[]{'"T";'"to";'"from";'"i"}}}


interactive nuprl_tip__count_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   sequent { <H> >- ("tip-count"[]{'"T";'"to";'"from";'"i";'"ch"} in "nat"[]{}) }

interactive nuprl_tip__count__bound   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "le"[]{"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"};"length"[]{"bi-graph-to"[]{'"T";'"to";'"from";'"i"}}} }

define unfold_tip__fun : "tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"} <-->
      "bor"[]{('"ch" '"l");"bor"[]{"lt_bool"[]{"number"[1:n]{};"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"}};"bfalse"[]{}}}


interactive nuprl_tip__fun_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"l" in "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "tip-msg"[]{} }  -->
   sequent { <H> >- ("tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"} in "bool"[]{}) }

interactive nuprl_tip__fun__property1   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"l" in "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "tip-msg"[]{} }  -->
   sequent { <H> >- "assert"[]{('"ch" '"l")} }  -->
   sequent { <H> >- "assert"[]{"tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"}} }

interactive nuprl_tip__fun__property2   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"l" in "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "tip-msg"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[1:n]{};"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"}} }  -->
   sequent { <H> >- "assert"[]{"tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"}} }

interactive nuprl_tip__count__update   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"l" in "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"v" in "tip-msg"[]{} }  -->
   sequent { <H> >- "le"[]{"tip-count"[]{'"T";'"to";'"from";'"i";"update"[]{"eqof"[]{"idlnk-deq"[]{}};'"ch";'"l";"tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"}}};"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"}} }

interactive nuprl_tip__count__property1  '"l"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"l" in "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "l_all"[]{"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"};"l'"."implies"[]{"not"[]{"equal"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};'"l";'"l'"}};"assert"[]{('"ch" '"l'")}}} }  -->
   sequent { <H> >- "lt"[]{"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"};"number"[2:n]{}} }

define unfold_tip__msg__fun : "tip-msg-fun"[]{'"T";'"to";'"from";'"i";'"ch"} <-->
      "inr"[]{"it"[]{}}


interactive nuprl_tip__msg__fun_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-graph"[]{'"T";'"to";'"from"} }  -->
   [wf] sequent { <H> >- '"i" in "rset"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"i"};"bi-graph-edge"[]{'"T";'"to";'"from"}}} >- '"ch" '"x" in "bool"[]{} }  -->
   sequent { <H> >- ("tip-msg-fun"[]{'"T";'"to";'"from";'"i";'"ch"} in "tip-msg"[]{}) }

define unfold_tree__leader : "tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"} <-->
      "ifthenelse"[]{('"T" '"loc");"cons"[]{"ma-single-init"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"lambda"[]{"l"."bfalse"[]{}}};"cons"[]{"ma-single-pre-init1"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"lambda"[]{"l"."bfalse"[]{}};"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"unit"[]{};"ch", "v"."lt"[]{"tip-count"[]{'"T";'"to";'"from";'"loc";'"ch"};"number"[2:n]{}}};"cons"[]{"ma-single-pre1"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"unit"[]{};"ch", "v"."lt"[]{"tip-count"[]{'"T";'"to";'"from";'"loc";'"ch"};"number"[2:n]{}}};"cons"[]{"ma-join-list"[]{"mapl"[]{"lambda"[]{"l"."ma-join"[]{"ma-single-sends1"[]{"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"unit"[]{};"tip-msg"[]{};"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"locl"[]{"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"lambda"[]{"a"."lambda"[]{"b"."cons"[]{"tip-msg-fun"[]{'"T";'"to";'"from";'"loc";'"a"};"nil"[]{}}}}};"ma-single-sframe"[]{"cons"[]{"locl"[]{"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};"nil"[]{}};'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}}}};"bi-graph-from"[]{'"T";'"to";'"from";'"loc"}}};"cons"[]{"ma-single-frame"[]{"map"[]{"lambda"[]{"l"."rcv"[]{'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}}};"bi-graph-to"[]{'"T";'"to";'"from";'"loc"}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"mkid"[]{"token"["ch":t]{};"number"[0:n]{}}};"cons"[]{"ma-join-list"[]{"mapl"[]{"lambda"[]{"l"."ma-single-effect0"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"rcv"[]{'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};"tip-msg"[]{};"lambda"[]{"ch"."lambda"[]{"v"."update"[]{"eqof"[]{"idlnk-deq"[]{}};'"ch";'"l";"tip-fun"[]{'"T";'"to";'"from";'"loc";'"l";'"ch";'"v"}}}}}};"bi-graph-to"[]{'"T";'"to";'"from";'"loc"}}};"nil"[]{}}}}}}};"nil"[]{}}


interactive nuprl_tree__leader__compatible   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"T"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"}} }

interactive nuprl_tree__leader_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"loc" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"T"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- ("tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"} in "list"[]{"msga"[level:l]{}}) }

interactive nuprl_tree__leader__feasible   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"T"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "d-feasible"[]{"lambda"[]{"loc"."ma-join-list"[]{"tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"}}}} }

interactive nuprl_tree__leader__realizes   :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"T" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"uid" '"x" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"from" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "rset"[]{'"T"} >- '"to" '"x" in "list"[]{"IdLnk"[]{}} }  -->
   sequent { <H> >- "bi-tree"[]{'"T";'"to";'"from"} }  -->
   sequent { <H> >- "inject"[]{"rset"[]{'"T"};"nat"[]{};'"uid"} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"lambda"[]{"loc"."ma-join-list"[]{"tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"}}};"es"."exists"[]{"rset"[]{'"T"};"ldr"."and"[]{"existse-at"[]{'"es";'"ldr";"e"."equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{"mkid"[]{"token"["leader":t]{};"number"[0:n]{}}}}};"all"[]{"rset"[]{'"T"};"i"."alle-at"[]{'"es";'"i";"e"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{"mkid"[]{"token"["leader":t]{};"number"[0:n]{}}}};"equal"[]{"rset"[]{'"T"};'"i";'"ldr"}}}}}}} }


(**** display forms ****)


dform nuprl_tree__leader_df : except_mode[src] :: "tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"} =
   `"tree-leader(" slot{'"loc"} `";" slot{'"T"} `";" slot{'"uid"} `";"
    slot{'"from"} `";" slot{'"to"} `")"


dform nuprl_tip__msg_df : except_mode[src] :: "tip-msg"[]{} =
   `"tip-msg()"


dform nuprl_tip__count_df : except_mode[src] :: "tip-count"[]{'"T";'"to";'"from";'"i";'"ch"} =
   `"tip-count(" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"i"}
    `";" slot{'"ch"} `")"


dform nuprl_tip__fun_df : except_mode[src] :: "tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"} =
   `"tip-fun(" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"i"} `";"
    slot{'"l"} `";" slot{'"ch"} `";" slot{'"v"} `")"


dform nuprl_tip__msg__fun_df : except_mode[src] :: "tip-msg-fun"[]{'"T";'"to";'"from";'"i";'"ch"} =
   `"tip-msg-fun(" slot{'"T"} `";" slot{'"to"} `";" slot{'"from"} `";" slot{'"i"}
    `";" slot{'"ch"} `")"


