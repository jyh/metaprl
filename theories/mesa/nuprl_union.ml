extends Ma_int_1

open Dtactic


define unfold_isl : "is_inl"[]{'"x"} <-->
      "decide"[]{'"x";"y"."btrue"[]{};"z"."bfalse"[]{}}


interactive nuprl_isl_wf {| intro[] |}  '"B" '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in "union"[]{'"A";'"B"} }  -->
   sequent { <H> >- ("is_inl"[]{'"x"} in "bool"[]{}) }

define unfold_outl : "outl"[]{'"x"} <-->
      "decide"[]{'"x";"y".'"y";"z"."token"["???":t]{}}


interactive nuprl_outl_wf {| intro[] |}  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in "union"[]{'"A";'"B"} }  -->
   sequent { <H> >- "assert"[]{"is_inl"[]{'"x"}} }  -->
   sequent { <H> >- ("outl"[]{'"x"} in '"A") }

define unfold_outr : "outr"[]{'"x"} <-->
      "decide"[]{'"x";"y"."token"["???":t]{};"z".'"z"}


interactive nuprl_outr_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in "union"[]{'"A";'"B"} }  -->
   sequent { <H> >- "assert"[]{"bnot"[]{"is_inl"[]{'"x"}}} }  -->
   sequent { <H> >- ("outr"[]{'"x"} in '"B") }


(**** display forms ****)


dform nuprl_isl_df : except_mode[src] :: "is_inl"[]{'"x"} =
   `"isl(" slot{'"x"} `")"


dform nuprl_outl_df : except_mode[src] :: "outl"[]{'"x"} =
   `"outl(" slot{'"x"} `")"


dform nuprl_outr_df : except_mode[src] :: "outr"[]{'"x"} =
   `"outr(" slot{'"x"} `")"


