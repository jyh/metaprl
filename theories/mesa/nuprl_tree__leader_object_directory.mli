extends Ma_ring__leader1_object_directory


define unfold_tip__msg : "tip-msg"[]{} <-->
      "union"[]{"nat"[]{};"unit"[]{}}


define unfold_tip__count : "tip-count"[]{'"T";'"to";'"from";'"i";'"ch"} <-->
      "length"[]{"filter"[]{"lambda"[]{"l"."bnot"[]{('"ch" '"l")}};"bi-graph-to"[]{'"T";'"to";'"from";'"i"}}}


define unfold_tip__fun : "tip-fun"[]{'"T";'"to";'"from";'"i";'"l";'"ch";'"v"} <-->
      "bor"[]{('"ch" '"l");"bor"[]{"lt_bool"[]{"number"[1:n]{};"tip-count"[]{'"T";'"to";'"from";'"i";'"ch"}};"bfalse"[]{}}}


define unfold_tip__msg__fun : "tip-msg-fun"[]{'"T";'"to";'"from";'"i";'"ch"} <-->
      "inr"[]{"it"[]{}}


define unfold_tree__leader : "tree-leader"[]{'"loc";'"T";'"uid";'"from";'"to"} <-->
      "ifthenelse"[]{('"T" '"loc");"cons"[]{"ma-single-init"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"lambda"[]{"l"."bfalse"[]{}}};"cons"[]{"ma-single-pre-init1"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"lambda"[]{"l"."bfalse"[]{}};"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"unit"[]{};"ch", "v"."lt"[]{"tip-count"[]{'"T";'"to";'"from";'"loc";'"ch"};"number"[2:n]{}}};"cons"[]{"ma-single-pre1"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"unit"[]{};"ch", "v"."lt"[]{"tip-count"[]{'"T";'"to";'"from";'"loc";'"ch"};"number"[2:n]{}}};"cons"[]{"ma-join-list"[]{"mapl"[]{"lambda"[]{"l"."ma-join"[]{"ma-single-sends1"[]{"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"unit"[]{};"tip-msg"[]{};"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"locl"[]{"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}};"lambda"[]{"a"."lambda"[]{"b"."cons"[]{"tip-msg-fun"[]{'"T";'"to";'"from";'"loc";'"a"};"nil"[]{}}}}};"ma-single-sframe"[]{"cons"[]{"locl"[]{"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};"nil"[]{}};'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}}}};"bi-graph-from"[]{'"T";'"to";'"from";'"loc"}}};"cons"[]{"ma-single-frame"[]{"map"[]{"lambda"[]{"l"."rcv"[]{'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}}};"bi-graph-to"[]{'"T";'"to";'"from";'"loc"}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"mkid"[]{"token"["ch":t]{};"number"[0:n]{}}};"cons"[]{"ma-join-list"[]{"mapl"[]{"lambda"[]{"l"."ma-single-effect0"[]{"mkid"[]{"token"["ch":t]{};"number"[0:n]{}};"fun"[]{"set"[]{"bi-graph-edge"[]{'"T";'"to";'"from"};"l"."mem"[]{'"l";"bi-graph-to"[]{'"T";'"to";'"from";'"loc"};"bi-graph-edge"[]{'"T";'"to";'"from"}}};""."bool"[]{}};"rcv"[]{'"l";"mkid"[]{"token"["tip":t]{};"number"[0:n]{}}};"tip-msg"[]{};"lambda"[]{"ch"."lambda"[]{"v"."update"[]{"eqof"[]{"idlnk-deq"[]{}};'"ch";'"l";"tip-fun"[]{'"T";'"to";'"from";'"loc";'"l";'"ch";'"v"}}}}}};"bi-graph-to"[]{'"T";'"to";'"from";'"loc"}}};"nil"[]{}}}}}}};"nil"[]{}}


