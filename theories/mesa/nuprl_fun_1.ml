extends Ma_sqequal_1

open Dtactic


define unfold_identity : "identity"[]{} <-->
      "lambda"[]{"x".'"x"}


interactive nuprl_identity_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- ("identity"[]{} in "fun"[]{'"A";"".'"A"}) }

define unfold_tidentity : "tidentity"[]{'"T"} <-->
      "identity"[]{}


interactive nuprl_tidentity_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- ("tidentity"[]{'"A"} in "fun"[]{'"A";"".'"A"}) }

interactive nuprl_my_tidentity_wf   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- ("tidentity"[]{'"A"} in "fun"[]{'"A";"".'"A"}) }

interactive nuprl_eta_conv   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"A";"".'"B"};"lambda"[]{"x".('"f" '"x")};'"f"} }

define unfold_tlambda : "tlambda"[]{'"T";"x".'"b"['"x"]} <-->
      "lambda"[]{"x".'"b"['"x"]}


define unfold_compose : "compose"[]{'"f";'"g"} <-->
      "lambda"[]{"x".('"f" ('"g" '"x"))}


interactive nuprl_compose_wf {| intro[] |}  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in '"C" }  -->
   [wf] sequent { <H>;"x": '"A" >- '"g" '"x" in '"B" }  -->
   sequent { <H> >- ("compose"[]{'"f";'"g"} in "fun"[]{'"A";"".'"C"}) }

interactive nuprl_comb_for_compose_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"C"."lambda"[]{"f"."lambda"[]{"g"."lambda"[]{"z"."compose"[]{'"f";'"g"}}}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"univ"[level:l]{};"B"."fun"[]{"univ"[level:l]{};"C"."fun"[]{"fun"[]{'"B";"".'"C"};"f"."fun"[]{"fun"[]{'"A";"".'"B"};"g"."fun"[]{"squash"[]{"true"[]{}};""."fun"[]{'"A";"".'"C"}}}}}}}) }

interactive nuprl_comp_assoc  '"B" '"C"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"D" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"C" }  -->
   [wf] sequent { <H>;"x": '"C" >- '"h" '"x" in '"D" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"A";"".'"D"};"compose"[]{'"h";"compose"[]{'"g";'"f"}};"compose"[]{"compose"[]{'"h";'"g"};'"f"}} }

interactive nuprl_comp_id_l   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"A";"".'"B"};"compose"[]{"tidentity"[]{'"B"};'"f"};'"f"} }

interactive nuprl_comp_id_r   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"A";"".'"B"};"compose"[]{'"f";"tidentity"[]{'"A"}};'"f"} }

define unfold_inv_funs : "inv_funs"[]{'"A";'"B";'"f";'"g"} <-->
      "and"[]{"equal"[]{"fun"[]{'"A";"".'"A"};"compose"[]{'"g";'"f"};"tidentity"[]{'"A"}};"equal"[]{"fun"[]{'"B";"".'"B"};"compose"[]{'"f";'"g"};"tidentity"[]{'"B"}}}


interactive nuprl_inv_funs_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"A" }  -->
   sequent { <H> >- ("inv_funs"[]{'"A";'"B";'"f";'"g"} in "univ"[level:l]{}) }

interactive nuprl_sq_stable__inv_funs   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"A" }  -->
   sequent { <H> >- "sqst"[]{"inv_funs"[]{'"A";'"B";'"f";'"g"}} }

define unfold_one_one_corr : "one_one_corr"[]{'"A";'"B"} <-->
      "exists"[]{"fun"[]{'"A";"".'"B"};"f"."exists"[]{"fun"[]{'"B";"".'"A"};"g"."inv_funs"[]{'"A";'"B";'"f";'"g"}}}


interactive nuprl_one_one_corr_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("one_one_corr"[]{'"A";'"B"} in "univ"[level:l]{}) }

define unfold_inject : "inject"[]{'"A";'"B";'"f"} <-->
      "all"[]{'"A";"a1"."all"[]{'"A";"a2"."implies"[]{"equal"[]{'"B";('"f" '"a1");('"f" '"a2")};"equal"[]{'"A";'"a1";'"a2"}}}}


interactive nuprl_inject_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("inject"[]{'"A";'"B";'"f"} in "univ"[level:l]{}) }

interactive nuprl_sq_stable__inject   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- "sqst"[]{"inject"[]{'"A";'"B";'"f"}} }

define unfold_surject : "surject"[]{'"A";'"B";'"f"} <-->
      "all"[]{'"B";"b"."exists"[]{'"A";"a"."equal"[]{'"B";('"f" '"a");'"b"}}}


interactive nuprl_surject_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("surject"[]{'"A";'"B";'"f"} in "univ"[level:l]{}) }

define unfold_biject : "biject"[]{'"A";'"B";'"f"} <-->
      "and"[]{"inject"[]{'"A";'"B";'"f"};"surject"[]{'"A";'"B";'"f"}}


interactive nuprl_biject_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("biject"[]{'"A";'"B";'"f"} in "univ"[level:l]{}) }

interactive nuprl_ax_choice  '"B" '"A" "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- "type"{'"Q"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"A"  >- "exists"[]{'"B";"y".'"Q"['"x";'"y"]} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{'"A";"".'"B"};"f"."all"[]{'"A";"x".'"Q"['"x";('"f" '"x")]}} }

interactive nuprl_dep_ax_choice  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B"['"x"] >- "type"{'"Q"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"A"  >- "exists"[]{'"B"['"x"];"y".'"Q"['"x";'"y"]} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{'"A";"x".'"B"['"x"]};"f"."all"[]{'"A";"x".'"Q"['"x";('"f" '"x")]}} }

interactive nuprl_inv_funs_sym   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"A" }  -->
   sequent { <H> >- "inv_funs"[]{'"A";'"B";'"f";'"g"} }  -->
   sequent { <H> >- "inv_funs"[]{'"B";'"A";'"g";'"f"} }

interactive nuprl_bij_imp_exists_inv   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- "biject"[]{'"A";'"B";'"f"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{'"B";"".'"A"};"g"."inv_funs"[]{'"A";'"B";'"f";'"g"}} }

interactive nuprl_fun_with_inv_is_bij  '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"A" }  -->
   sequent { <H> >- "inv_funs"[]{'"A";'"B";'"f";'"g"} }  -->
   sequent { <H> >- "biject"[]{'"A";'"B";'"f"} }

interactive nuprl_bij_iff_1_1_corr   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "iff"[]{"exists"[]{"fun"[]{'"A";"".'"B"};"f"."biject"[]{'"A";'"B";'"f"}};"one_one_corr"[]{'"A";'"B"}} }


(**** display forms ****)


dform nuprl_identity_df : except_mode[src] :: "identity"[]{} =
   `"Id"


dform nuprl_tidentity_df : except_mode[src] :: "tidentity"[]{'"T"} =
   `"Id{" slot{'"T"} `"}"


dform nuprl_tlambda_df : except_mode[src] :: "tlambda"[]{'"T";"x".'"b"} =
   `"" lambda `"" slot{'"x"} `":" slot{'"T"} `". " slot{'"b"} `""


dform nuprl_compose_df : except_mode[src] :: "compose"[]{'"f";'"g"} =
   `"" slot{'"f"} `"" szone sbreak["",""] ezone `" o " slot{'"g"} `""


dform nuprl_inv_funs_df : except_mode[src] :: "inv_funs"[]{'"A";'"B";'"f";'"g"} =
   `"InvFuns(" slot{'"A"} `";" slot{'"B"} `";" slot{'"f"} `";" slot{'"g"} `")"


dform nuprl_one_one_corr_df : except_mode[src] :: "one_one_corr"[]{'"A";'"B"} =
   `"1-1-Corresp(" slot{'"A"} `";" slot{'"B"} `")"


dform nuprl_inject_df : except_mode[src] :: "inject"[]{'"A";'"B";'"f"} =
   `"Inj(" slot{'"A"} `";" slot{'"B"} `";" slot{'"f"} `")"


dform nuprl_surject_df : except_mode[src] :: "surject"[]{'"A";'"B";'"f"} =
   `"Surj(" slot{'"A"} `";" slot{'"B"} `";" slot{'"f"} `")"


dform nuprl_biject_df : except_mode[src] :: "biject"[]{'"A";'"B";'"f"} =
   `"Bij(" slot{'"A"} `";" slot{'"B"} `";" slot{'"f"} `")"


