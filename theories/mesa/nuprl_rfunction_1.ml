extends Ma_fun_1

open Dtactic


interactive nuprl_rfunction_void_wf   :
   sequent { <H> >- ("rfun"[]{"void"[]{};"f", "x"."void"[]{}} in "univ"[1:l]{}) }

interactive nuprl_rfunction_void_wf_type   :
   sequent { <H> >- "type"{"rfun"[]{"void"[]{};"f", "x"."void"[]{}}} }

define unfold_fincr : "fincr"[]{} <-->
      "rfun"[]{"nat"[]{};"f", "i"."ifthenelse"[]{"beq_int"[]{'"i";"number"[0:n]{}};"int"[]{};"int_upper"[]{('"f" "sub"[]{'"i";"number"[1:n]{}})}}}


interactive nuprl_fincr_wf {| intro[] |}   :
   sequent { <H> >- ("fincr"[]{} in "univ"[level:l]{}) }

interactive nuprl_fincr_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"fincr"[]{}} }

interactive nuprl_fincr_wf2 {| intro[] |}   :
   sequent { <H> >- ("fincr"[]{} in "univ"[level:l]{}) }

interactive nuprl_fincr_wf2_type {| intro[] |}   :
   sequent { <H> >- "type"{"fincr"[]{}} }

interactive nuprl_fincr_formation   :
   sequent { <H> >- "fincr"[]{} }


(**** display forms ****)


dform nuprl_rfunction : except_mode[src] :: "rfun"[]{'"A";"f", "x".'"B"} =
   `"" szone `"{" slot{'"f"} `" | " pushm[0:n] `"" slot{'"x"} `":" pushm[0:n] `""
    slot{'"A"} `"" popm  `"" sbreak[""," "] `"" longleftarrow `" " pushm[0:n] `""
    slot{'"B"} `"" popm  `"" popm  `"}" ezone `""


dform nuprl_fincr_df : except_mode[src] :: "fincr"[]{} =
   `"FIncr"


