extends Ma_well_fnd

open Dtactic


interactive nuprl_le_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- ("le"[]{'"i";'"j"} in "univ"[1:l]{}) }

interactive nuprl_gt_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- ("gt"[]{'"i";'"j"} in "univ"[1:l]{}) }

interactive nuprl_comb_for_gt_wf   :
   sequent { <H> >- ("lambda"[]{"i"."lambda"[]{"j"."lambda"[]{"z"."gt"[]{'"i";'"j"}}}} in "fun"[]{"int"[]{};"i"."fun"[]{"int"[]{};"j"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

interactive nuprl_ge_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- ("ge"[]{'"i";'"j"} in "univ"[1:l]{}) }

interactive nuprl_comb_for_ge_wf   :
   sequent { <H> >- ("lambda"[]{"i"."lambda"[]{"j"."lambda"[]{"z"."ge"[]{'"i";'"j"}}}} in "fun"[]{"int"[]{};"i"."fun"[]{"int"[]{};"j"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

interactive nuprl_comb_for_le_wf   :
   sequent { <H> >- ("lambda"[]{"i"."lambda"[]{"j"."lambda"[]{"z"."le"[]{'"i";'"j"}}}} in "fun"[]{"int"[]{};""."fun"[]{"int"[]{};""."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

define unfold_lelt : "lelt"[]{'"i";'"j";'"k"} <-->
      "and"[]{"le"[]{'"i";'"j"};"lt"[]{'"j";'"k"}}


define unfold_lele : "lele"[]{'"i";'"j";'"k"} <-->
      "and"[]{"le"[]{'"i";'"j"};"le"[]{'"j";'"k"}}


interactive nuprl_nat_wf {| intro[] |}   :
   sequent { <H> >- ("nat"[]{} in "univ"[1:l]{}) }

interactive nuprl_nat_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"nat"[]{}} }

interactive nuprl_nat_properties   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "ge"[]{'"i";"number"[0:n]{}} }

define unfold_nat_plus : "nat_plus"[]{} <-->
      "set"[]{"int"[]{};"i"."lt"[]{"number"[0:n]{};'"i"}}


interactive nuprl_nat_plus_wf {| intro[] |}   :
   sequent { <H> >- ("nat_plus"[]{} in "univ"[1:l]{}) }

interactive nuprl_nat_plus_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"nat_plus"[]{}} }

interactive nuprl_nat_plus_properties   :
   [wf] sequent { <H> >- '"i" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};'"i"} }

define unfold_int_nzero : "int_nzero"[]{} <-->
      "set"[]{"int"[]{};"i"."nequal"[]{"int"[]{};'"i";"number"[0:n]{}}}


interactive nuprl_int_nzero_wf {| intro[] |}   :
   sequent { <H> >- ("int_nzero"[]{} in "univ"[1:l]{}) }

interactive nuprl_int_nzero_wf_type {| intro[] |}   :
   sequent { <H> >- "type"{"int_nzero"[]{}} }

interactive nuprl_int_nzero_properties   :
   [wf] sequent { <H> >- '"i" in "int_nzero"[]{} }  -->
   sequent { <H> >- "nequal"[]{"int"[]{};'"i";"number"[0:n]{}} }

define unfold_int_upper : "int_upper"[]{'"i"} <-->
      "set"[]{"int"[]{};"j"."le"[]{'"i";'"j"}}


interactive nuprl_int_upper_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("int_upper"[]{'"n"} in "univ"[1:l]{}) }

interactive nuprl_int_upper_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "type"{"int_upper"[]{'"n"}} }

interactive nuprl_comb_for_int_upper_wf   :
   sequent { <H> >- ("lambda"[]{"n"."lambda"[]{"z"."int_upper"[]{'"n"}}} in "fun"[]{"int"[]{};"n"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}) }

interactive nuprl_int_upper_properties   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int_upper"[]{'"i"} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }

define unfold_int_lower : "int_lower"[]{'"i"} <-->
      "set"[]{"int"[]{};"j"."le"[]{'"j";'"i"}}


interactive nuprl_int_lower_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- ("int_lower"[]{'"i"} in "univ"[1:l]{}) }

interactive nuprl_int_lower_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "type"{"int_lower"[]{'"i"}} }

interactive nuprl_int_lower_properties   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int_lower"[]{'"i"} }  -->
   sequent { <H> >- "le"[]{'"j";'"i"} }

define unfold_int_seg : "int_seg"[]{'"i";'"j"} <-->
      "set"[]{"int"[]{};"k"."lelt"[]{'"i";'"k";'"j"}}


interactive nuprl_int_seg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"m" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("int_seg"[]{'"m";'"n"} in "univ"[1:l]{}) }

interactive nuprl_int_seg_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"m" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "type"{"int_seg"[]{'"m";'"n"}} }

interactive nuprl_comb_for_int_seg_wf   :
   sequent { <H> >- ("lambda"[]{"m"."lambda"[]{"n"."lambda"[]{"z"."int_seg"[]{'"m";'"n"}}}} in "fun"[]{"int"[]{};"m"."fun"[]{"int"[]{};"n"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

interactive nuprl_int_seg_properties   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int_seg"[]{'"i";'"j"} }  -->
   sequent { <H> >- "lelt"[]{'"i";'"y";'"j"} }

interactive nuprl_decidable__equal_int_seg   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{'"i";'"j"} }  -->
   [wf] sequent { <H> >- '"y" in "int_seg"[]{'"i";'"j"} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"int_seg"[]{'"i";'"j"};'"x";'"y"}} }

define unfold_int_iseg : "int_iseg"[]{'"i";'"j"} <-->
      "set"[]{"int"[]{};"k"."and"[]{"le"[]{'"i";'"k"};"le"[]{'"k";'"j"}}}


interactive nuprl_int_iseg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- ("int_iseg"[]{'"i";'"j"} in "univ"[1:l]{}) }

interactive nuprl_int_iseg_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "type"{"int_iseg"[]{'"i";'"j"}} }

interactive nuprl_int_iseg_properties   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int_iseg"[]{'"i";'"j"} }  -->
   sequent { <H> >- "and"[]{"le"[]{'"i";'"y"};"le"[]{'"y";'"j"}} }

interactive nuprl_int_lt_to_int_upper  '"i" "lambda"[]{"x".'"A"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_upper"[]{"add"[]{'"i";"number"[1:n]{}}} >- "type"{'"A"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"guard"[]{"all"[]{"int"[]{};"j"."implies"[]{"lt"[]{'"i";'"j"};'"A"['"j"]}}};"guard"[]{"all"[]{"int_upper"[]{"add"[]{'"i";"number"[1:n]{}}};"j".'"A"['"j"]}}} }

interactive nuprl_int_le_to_int_upper  '"i" "lambda"[]{"x".'"A"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_upper"[]{'"i"} >- "type"{'"A"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"guard"[]{"all"[]{"int"[]{};"j"."implies"[]{"le"[]{'"i";'"j"};'"A"['"j"]}}};"guard"[]{"all"[]{"int_upper"[]{'"i"};"j".'"A"['"j"]}}} }

interactive nuprl_nat_plus_inc_nat   :
   sequent { <H> >- "subtype"[]{"nat_plus"[]{};"nat"[]{}} }

interactive nuprl_nat_plus_inc   :
   sequent { <H> >- "subtype"[]{"nat_plus"[]{};"nat"[]{}} }

interactive nuprl_nat_plus_inc_int_nzero   :
   sequent { <H> >- "subtype"[]{"nat_plus"[]{};"int_nzero"[]{}} }

interactive nuprl_nat_ind_a  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- '"P"["number"[0:n]{}] }  -->
   sequent { <H>; "i": "nat_plus"[]{} ; '"P"["sub"[]{'"i";"number"[1:n]{}}]  >- '"P"['"i"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"nat"[]{};"i".'"P"['"i"]}} }

interactive nuprl_nat_ind_tp  "lambda"[]{"x".'"P"['"x"]} '"i"  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- '"P"["number"[0:n]{}] }  -->
   sequent { <H>; "i": "nat_plus"[]{} ; '"P"["sub"[]{'"i";"number"[1:n]{}}]  >- '"P"['"i"] }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- '"P"['"i"] }

interactive nuprl_nat_ind  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- '"P"["number"[0:n]{}] }  -->
   sequent { <H>; "i": "nat_plus"[]{} ; '"P"["sub"[]{'"i";"number"[1:n]{}}]  >- '"P"['"i"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"nat"[]{};"j".'"P"['"j"]}} }

interactive nuprl_comp_nat_ind_tp  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "i": "nat"[]{} ; "all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"j";'"i"};'"P"['"j"]}}  >- '"P"['"i"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"nat"[]{};"i".'"P"['"i"]}} }

interactive nuprl_comp_nat_ind_a  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "i": "nat"[]{} ; "all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"j";'"i"};'"P"['"j"]}}  >- '"P"['"i"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"nat"[]{};"i".'"P"['"i"]}} }

interactive nuprl_nat_well_founded   :
   sequent { <H> >- "well_founded"[level:l]{"nat"[]{};"x", "y"."lt"[]{'"x";'"y"}} }

interactive nuprl_complete_nat_ind  "lambda"[]{"x".'"P"['"x"]} '"i"  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "i": "nat"[]{} ; "all"[]{"int_seg"[]{"number"[0:n]{};'"i"};"j".'"P"['"j"]}  >- '"P"['"i"] }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- '"P"['"i"] }

define unfold_suptype : "suptype"[]{'"S";'"T"} <-->
      "subtype"[]{'"T";'"S"}


interactive nuprl_complete_nat_ind_with_y  "lambda"[]{"x".'"P"['"x"]} '"i"  :
   [wf] sequent { <H>;"x": "nat"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "i": "nat"[]{} ; "all"[]{"int_seg"[]{"number"[0:n]{};'"i"};"j".'"P"['"j"]}  >- '"P"['"i"] }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- '"P"['"i"] }


(**** display forms ****)


dform nuprl_lelt_df : except_mode[src] :: "lelt"[]{'"a";'"b";'"c"} =
   `"" slot{'"a"} `" " le `" " slot{'"b"} `" < " slot{'"c"} `""


dform nuprl_lele_df : except_mode[src] :: "lele"[]{'"i";'"j";'"k"} =
   `"" slot{'"i"} `" " le `" " slot{'"j"} `" " le `" " slot{'"k"} `""



dform nuprl_nat_plus_df : except_mode[src] :: "nat_plus"[]{} =
   `"" mathbbN `"" supplus `""


dform nuprl_int_nzero_df : except_mode[src] :: "int_nzero"[]{} =
   `"" mathbbZ `"" supminus `"" supcirc `""


dform nuprl_int_upper_df : except_mode[src] :: "int_upper"[]{'"n"} =
   `"{" slot{'"n"} `"...}"


dform nuprl_int_lower_df : except_mode[src] :: "int_lower"[]{'"i"} =
   `"{..." slot{'"i"} `"}"


dform nuprl_int_seg_df : except_mode[src] :: "int_seg"[]{'"i";'"j"} =
   `"{" slot{'"i"} `".." slot{'"j"} `"" supminus `"}"


dform nuprl_nsub : except_mode[src] :: "int_seg"[]{"number"[0:n]{};'"j"} =
   `"" mathbbN `"" slot{'"j"} `""


dform nuprl_int_iseg_df : except_mode[src] :: "int_iseg"[]{'"i";'"j"} =
   `"{" slot{'"i"} `"..." slot{'"j"} `"}"


