extends Ma_int_1


define unfold_isl : "is_inl"[]{'"x"} <-->
      "decide"[]{'"x";"y"."btrue"[]{};"z"."bfalse"[]{}}


define unfold_outl : "outl"[]{'"x"} <-->
      "decide"[]{'"x";"y".'"y";"z"."token"["???":t]{}}


define unfold_outr : "outr"[]{'"x"} <-->
      "decide"[]{'"x";"y"."token"["???":t]{};"z".'"z"}


