extends Ma_nat_extra

open Dtactic


interactive nuprl_append_firstn_lastn   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"append"[]{"firstn"[]{'"n";'"L"};"nth_tl"[]{'"n";'"L"}};'"L"} }

interactive nuprl_append_split2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P" '"x" } }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}  >- "decidable"[]{('"P" '"x")} }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; "j": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"P" '"i") ; "lt"[]{'"i";'"j"}  >- ('"P" '"j") }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L_1"."exists"[]{"list"[]{'"T"};"L_2"."and"[]{"equal"[]{"list"[]{'"T"};'"L";"append"[]{'"L_1";'"L_2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."iff"[]{('"P" '"i");"le"[]{"length"[]{'"L_1"};'"i"}}}}}} }

interactive nuprl_non_nil_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"T"};'"L";"nil"[]{}}} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }

interactive nuprl_length_zero   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};"length"[]{'"l"};"number"[0:n]{}};"equal"[]{"list"[]{'"T"};'"l";"nil"[]{}}} }

interactive_rw nuprl_list_decomp  '"T"  :
   "type"{'"T"} -->
   ('"L" in "list"[]{'"T"}) -->
   "lt"[]{"number"[0:n]{};"length"[]{'"L"}} -->
   '"L" <--> "cons"[]{"hd"[]{'"L"};"tl"[]{'"L"}}

interactive_rw nuprl_nth_tl_decomp  '"T"  :
   "type"{'"T"} -->
   ('"m" in "nat"[]{}) -->
   ('"L" in "list"[]{'"T"}) -->
   "lt"[]{'"m";"length"[]{'"L"}} -->
   "nth_tl"[]{'"m";'"L"} <--> "cons"[]{"select"[]{'"m";'"L"};"nth_tl"[]{"add"[]{"number"[1:n]{};'"m"};'"L"}}

interactive nuprl_nth_tl_decomp_eq   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "lt"[]{'"m";"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"nth_tl"[]{'"m";'"L"};"cons"[]{"select"[]{'"m";'"L"};"nth_tl"[]{"add"[]{"number"[1:n]{};'"m"};'"L"}}} }

interactive_rw nuprl_firstn_decomp  '"T"  :
   "type"{'"T"} -->
   ('"j" in "nat"[]{}) -->
   ('"l" in "list"[]{'"T"}) -->
   "lt"[]{"number"[0:n]{};'"j"} -->
   "lt"[]{'"j";"length"[]{'"l"}} -->
   "append"[]{"firstn"[]{"sub"[]{'"j";"number"[1:n]{}};'"l"};"cons"[]{"select"[]{"sub"[]{'"j";"number"[1:n]{}};'"l"};"nil"[]{}}} <--> "firstn"[]{'"j";'"l"}

interactive_rw nuprl_map_append_sq  '"A"  :
   "type"{'"A"} -->
   ('"as" in "list"[]{'"A"}) -->
   "map"[]{'"f";"append"[]{'"as";'"as'"}} <--> "append"[]{"map"[]{'"f";'"as"};"map"[]{'"f";'"as'"}}

interactive nuprl_list_extensionality   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"b" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"a"};"length"[]{'"b"}} }  -->
   sequent { <H>; "i": "nat"[]{} ; "lt"[]{'"i";"length"[]{'"a"}}  >- "equal"[]{'"T";"select"[]{'"i";'"a"};"select"[]{'"i";'"b"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"a";'"b"} }

interactive nuprl_map_equal  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"g" '"x" in '"T'" }  -->
   sequent { <H>; "i": "nat"[]{} ; "lt"[]{'"i";"length"[]{'"a"}}  >- "equal"[]{'"T'";('"f" "select"[]{'"i";'"a"});('"g" "select"[]{'"i";'"a"})} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T'"};"map"[]{'"f";'"a"};"map"[]{'"g";'"a"}} }

interactive nuprl_select_equal   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"b" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"a";'"b"} }  -->
   sequent { <H> >- "lt"[]{'"i";"length"[]{'"a"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";'"a"};"select"[]{'"i";'"b"}} }

interactive nuprl_list_decomp_reverse   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "exists"[]{'"T";"x"."exists"[]{"list"[]{'"T"};"L'"."equal"[]{"list"[]{'"T"};'"L";"append"[]{'"L'";"cons"[]{'"x";"nil"[]{}}}}}} }

interactive nuprl_list_append_singleton_ind  '"T" "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"T"} >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- '"Q"["nil"[]{}] }  -->
   sequent { <H>; "ys": "list"[]{'"T"} ; "x": '"T" ; '"Q"['"ys"]  >- '"Q"["append"[]{'"ys";"cons"[]{'"x";"nil"[]{}}}] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"list"[]{'"T"};"zs".'"Q"['"zs"]}} }

interactive nuprl_cons_one_one   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"a'" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"b'" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"list"[]{'"T"};"cons"[]{'"a";'"b"};"cons"[]{'"a'";'"b'"}};"guard"[]{"and"[]{"equal"[]{'"T";'"a";'"a'"};"equal"[]{"list"[]{'"T"};'"b";'"b'"}}}} }

interactive nuprl_map_length_nat  '"B" '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"nat"[]{};"length"[]{"map"[]{'"f";'"as"}};"length"[]{'"as"}} }

interactive nuprl_list_2_decomp   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"z" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"nat"[]{};"length"[]{'"z"};"number"[2:n]{}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"z";"cons"[]{"select"[]{"number"[0:n]{};'"z"};"cons"[]{"select"[]{"number"[1:n]{};'"z"};"nil"[]{}}}} }

interactive nuprl_append_is_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"list"[]{'"T"};"append"[]{'"l1";'"l2"};"nil"[]{}};"and"[]{"equal"[]{"list"[]{'"T"};'"l1";"nil"[]{}};"equal"[]{"list"[]{'"T"};'"l2";"nil"[]{}}}} }

interactive_rw nuprl_append_nil_sq  '"T"  :
   "type"{'"T"} -->
   ('"l" in "list"[]{'"T"}) -->
   "append"[]{'"l";"nil"[]{}} <--> '"l"

interactive nuprl_comb_for_nth_tl_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"as"."lambda"[]{"i"."lambda"[]{"z"."nth_tl"[]{'"i";'"as"}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"list"[]{'"A"};"as"."fun"[]{"int"[]{};"i"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"A"}}}}}) }

interactive nuprl_comb_for_ifthenelse_wf   :
   sequent { <H> >- ("lambda"[]{"b"."lambda"[]{"A"."lambda"[]{"p"."lambda"[]{"q"."lambda"[]{"z"."ifthenelse"[]{'"b";'"p";'"q"}}}}}} in "fun"[]{"bool"[]{};"b"."fun"[]{"univ"[level:l]{};"A"."fun"[]{'"A";"p"."fun"[]{'"A";"q"."fun"[]{"squash"[]{"true"[]{}};"".'"A"}}}}}) }

interactive nuprl_band_commutes   :
   [wf] sequent { <H> >- '"a" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"band"[]{'"a";'"b"};"band"[]{'"b";'"a"}} }

interactive_rw nuprl_null_append  '"T"  :
   "type"{'"T"} -->
   ('"L1" in "list"[]{'"T"}) -->
   ('"L2" in "list"[]{'"T"}) -->
   "is_nil"[]{"append"[]{'"L1";'"L2"}} <--> "band"[]{"is_nil"[]{'"L1"};"is_nil"[]{'"L2"}}

interactive_rw nuprl_select_cons_tl_sq2   :
   ('"i" in "nat"[]{}) -->
   "select"[]{"add"[]{'"i";"number"[1:n]{}};"cons"[]{'"x";'"l"}} <--> "select"[]{'"i";'"l"}

define unfold_mklist : "mklist"[]{'"n";'"f"} <-->
      "primrec"[]{'"n";"nil"[]{};"lambda"[]{"i"."lambda"[]{"l"."append"[]{'"l";"cons"[]{('"f" '"i");"nil"[]{}}}}}}


interactive nuprl_mklist_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- ("mklist"[]{'"n";'"f"} in "list"[]{'"T"}) }

interactive nuprl_mklist_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"mklist"[]{'"n";'"f"}};'"n"} }

interactive nuprl_mklist_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"mklist"[]{'"n";'"f"}};('"f" '"i")} }

interactive nuprl_l_member_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("mem"[]{'"x";'"l";'"T"} in "univ"[level:l]{}) }

interactive nuprl_member_exists   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"T"};'"L";"nil"[]{}}} }  -->
   sequent { <H> >- "exists"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}} }

interactive nuprl_map_equal2  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"g" '"x" in '"T'" }  -->
   sequent { <H>; "x": '"T" ; "mem"[]{'"x";'"a";'"T"}  >- "equal"[]{'"T'";('"f" '"x");('"g" '"x")} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T'"};"map"[]{'"f";'"a"};"map"[]{'"g";'"a"}} }

interactive nuprl_trivial_map   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   sequent { <H>; "x": '"T" ; "mem"[]{'"x";'"a";'"T"}  >- "equal"[]{'"T";('"f" '"x");'"x"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"map"[]{'"f";'"a"};'"a"} }

interactive nuprl_comb_for_l_member_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"x"."lambda"[]{"l"."lambda"[]{"z"."mem"[]{'"x";'"l";'"T"}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{'"T";"x"."fun"[]{"list"[]{'"T"};"l"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}}) }

interactive nuprl_member_tl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   sequent { <H> >- "mem"[]{'"x";"tl"[]{'"as"};'"T"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"as";'"T"} }

interactive nuprl_nil_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"nil"[]{};'"T"};"false"[]{}} }

interactive nuprl_null_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "assert"[]{"is_nil"[]{'"L"}} }  -->
   sequent { <H> >- "not"[]{"mem"[]{'"x";'"L";'"T"}} }

interactive nuprl_member_null  '"T" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }

interactive nuprl_cons_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"cons"[]{'"a";'"l"};'"T"};"or"[]{"equal"[]{'"T";'"x";'"a"};"mem"[]{'"x";'"l";'"T"}}} }

interactive nuprl_l_member_decidable   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H>; "y": '"T"  >- "decidable"[]{"equal"[]{'"T";'"x";'"y"}} }  -->
   sequent { <H> >- "decidable"[]{"mem"[]{'"x";'"l";'"T"}} }

interactive nuprl_member_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"append"[]{'"l1";'"l2"};'"T"};"or"[]{"mem"[]{'"x";'"l1";'"T"};"mem"[]{'"x";'"l2";'"T"}}} }

interactive nuprl_select_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "mem"[]{"select"[]{'"i";'"L"};'"L";'"T"} }

interactive nuprl_member_singleton   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"cons"[]{'"a";"nil"[]{}};'"T"};"equal"[]{'"T";'"x";'"a"}} }

interactive nuprl_member_map   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"map"[]{'"f";'"a"};'"T'"};"exists"[]{'"T";"y"."and"[]{"mem"[]{'"y";'"a";'"T"};"equal"[]{'"T'";'"x";('"f" '"y")}}}} }

interactive nuprl_l_member_non_nil  '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"T"};'"L";"nil"[]{}}} }

define unfold_agree_on_common : "agree_on_common"[]{'"T";'"as";'"bs"} <-->
      ((("ycomb"[]{} "lambda"[]{"agree_on_common"."lambda"[]{"as"."lambda"[]{"bs"."list_ind"[]{'"as";"true"[]{};"a", "as'", ""."list_ind"[]{'"bs";"true"[]{};"b", "bs'", ""."or"[]{"and"[]{"not"[]{"mem"[]{'"a";'"bs";'"T"}};(('"agree_on_common" '"as'") '"bs")};"or"[]{"and"[]{"not"[]{"mem"[]{'"b";'"as";'"T"}};(('"agree_on_common" '"as") '"bs'")};"and"[]{"equal"[]{'"T";'"a";'"b"};(('"agree_on_common" '"as'") '"bs'")}}}}}}}}) '"as") '"bs")


interactive nuprl_agree_on_common_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("agree_on_common"[]{'"T";'"as";'"bs"} in "univ"[level:l]{}) }

interactive nuprl_agree_on_common_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"agree_on_common"[]{'"T";"cons"[]{'"x";'"as"};"cons"[]{'"x";'"bs"}};"agree_on_common"[]{'"T";'"as";'"bs"}} }

interactive nuprl_agree_on_common_weakening   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"as";'"bs"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as";'"bs"} }

interactive nuprl_agree_on_common_symmetry   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as";'"bs"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"bs";'"as"} }

interactive nuprl_agree_on_common_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"agree_on_common"[]{'"T";'"as";"nil"[]{}};"true"[]{}} }

interactive nuprl_agree_on_common_cons2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "and"[]{"implies"[]{"not"[]{"mem"[]{'"x";'"bs";'"T"}};"iff"[]{"agree_on_common"[]{'"T";"cons"[]{'"x";'"as"};'"bs"};"agree_on_common"[]{'"T";'"as";'"bs"}}};"implies"[]{"not"[]{"mem"[]{'"x";'"as";'"T"}};"iff"[]{"agree_on_common"[]{'"T";'"as";"cons"[]{'"x";'"bs"}};"agree_on_common"[]{'"T";'"as";'"bs"}}}} }

define unfold_last : "last"[]{'"L"} <-->
      "select"[]{"sub"[]{"length"[]{'"L"};"number"[1:n]{}};'"L"}


interactive nuprl_last_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- ("last"[]{'"L"} in '"T") }

interactive nuprl_last_lemma   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L'"."equal"[]{"list"[]{'"T"};'"L";"append"[]{'"L'";"cons"[]{"last"[]{'"L"};"nil"[]{}}}}} }

interactive nuprl_last_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "mem"[]{"last"[]{'"L"};'"L";'"T"} }

interactive nuprl_last_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "equal"[]{'"T";"last"[]{"cons"[]{'"x";'"L"}};"last"[]{'"L"}} }

define unfold_reverse_select : "reverse_select"[]{'"l";'"n"} <-->
      "select"[]{"sub"[]{"length"[]{'"l"};"add"[]{'"n";"number"[1:n]{}}};'"l"}


interactive nuprl_reverse_select_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"n";"length"[]{'"l"}} }  -->
   sequent { <H> >- ("reverse_select"[]{'"l";'"n"} in '"T") }

define unfold_l_member__ : "l_member!"[]{'"x";'"l";'"T"} <-->
      "exists"[]{"nat"[]{};"i"."cand"[]{"lt"[]{'"i";"length"[]{'"l"}};"and"[]{"equal"[]{'"T";'"x";"select"[]{'"i";'"l"}};"all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";'"x";"select"[]{'"j";'"l"}};"equal"[]{"nat"[]{};'"j";'"i"}}}}}}}


interactive nuprl_l_member___wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- ("l_member!"[]{'"x";'"l";'"T"} in "univ"[level:l]{}) }

interactive nuprl_cons_member__   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_member!"[]{'"x";"cons"[]{'"a";'"l"};'"T"};"or"[]{"and"[]{"equal"[]{'"T";'"x";'"a"};"not"[]{"mem"[]{'"x";'"l";'"T"}}};"and"[]{"l_member!"[]{'"x";'"l";'"T"};"not"[]{"equal"[]{'"T";'"x";'"a"}}}}} }

interactive nuprl_nil_member__   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_member!"[]{'"x";"nil"[]{};'"T"};"false"[]{}} }

define unfold_sublist : "sublist"[]{'"T";'"L1";'"L2"} <-->
      "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}}};"f"."and"[]{"increasing"[]{'"f";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f" '"j");'"L2"}}}}}


interactive nuprl_sublist_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("sublist"[]{'"T";'"L1";'"L2"} in "univ"[level:l]{}) }

interactive nuprl_sublist_transitivity  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L3" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L2";'"L3"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L3"} }

interactive nuprl_length_sublist  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "le"[]{"length"[]{'"L1"};"length"[]{'"L2"}} }

interactive nuprl_cons_sublist_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"sublist"[]{'"T";"cons"[]{'"x";'"L"};"nil"[]{}};"false"[]{}} }

interactive nuprl_proper_sublist_length   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"L1"};"length"[]{'"L2"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L1";'"L2"} }

interactive nuprl_sublist_antisymmetry   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L2";'"L1"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L1";'"L2"} }

interactive nuprl_nil_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"sublist"[]{'"T";"nil"[]{};'"L"};"true"[]{}} }

interactive nuprl_cons_sublist_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x1" in '"T" }  -->
   [wf] sequent { <H> >- '"x2" in '"T" }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"sublist"[]{'"T";"cons"[]{'"x1";'"L1"};"cons"[]{'"x2";'"L2"}};"or"[]{"and"[]{"equal"[]{'"T";'"x1";'"x2"};"sublist"[]{'"T";'"L1";'"L2"}};"sublist"[]{'"T";"cons"[]{'"x1";'"L1"};'"L2"}}} }

interactive nuprl_member_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"L1";'"T"};"mem"[]{'"x";'"L2";'"T"}}}} }

interactive nuprl_sublist_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1'" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2'" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L1'"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L2";'"L2'"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"append"[]{'"L1";'"L2"};"append"[]{'"L1'";'"L2'"}} }

interactive nuprl_comb_for_sublist_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"L1"."lambda"[]{"L2"."lambda"[]{"z"."sublist"[]{'"T";'"L1";'"L2"}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"L1"."fun"[]{"list"[]{'"T"};"L2"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}}) }

interactive nuprl_sublist_weakening   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L1";'"L2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }

interactive nuprl_sublist_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"sublist"[]{'"T";'"L";"nil"[]{}};"equal"[]{"list"[]{'"T"};'"L";"nil"[]{}}} }

interactive nuprl_sublist_tl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L2"}}} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";"tl"[]{'"L2"}} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }

interactive nuprl_sublist_tl2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"u" in '"T" }  -->
   [wf] sequent { <H> >- '"v" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"v"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";"cons"[]{'"u";'"v"}} }

interactive nuprl_sublist_append_front  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H>; "not"[]{"assert"[]{"is_nil"[]{'"L"}}}  >- "not"[]{"mem"[]{"last"[]{'"L"};'"L2";'"T"}} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L";"append"[]{'"L1";'"L2"}} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L";'"L1"} }

interactive nuprl_sublist_pair   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"cons"[]{"select"[]{'"i";'"L"};"cons"[]{"select"[]{'"j";'"L"};"nil"[]{}}};'"L"} }

interactive nuprl_member_iff_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";'"L";'"T"};"sublist"[]{'"T";"cons"[]{'"x";"nil"[]{}};'"L"}} }

define unfold_l_before : "l_before"[]{'"x";'"y";'"l";'"T"} <-->
      "sublist"[]{'"T";"cons"[]{'"x";"cons"[]{'"y";"nil"[]{}}};'"l"}


interactive nuprl_l_before_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- ("l_before"[]{'"x";'"y";'"l";'"T"} in "univ"[level:l]{}) }

interactive nuprl_weak_l_before_append_front  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"y";'"L1";'"T"} }  -->
   sequent { <H> >- "not"[]{"mem"[]{'"y";'"L2";'"T"}} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";"append"[]{'"L1";'"L2"};'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"L1";'"T"} }

interactive nuprl_l_before_append_front  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "not"[]{"mem"[]{'"y";'"L2";'"T"}} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";"append"[]{'"L1";'"L2"};'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"L1";'"T"} }

interactive nuprl_l_tricotomy   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"y";'"L";'"T"} }  -->
   sequent { <H> >- "or"[]{"or"[]{"equal"[]{'"T";'"x";'"y"};"l_before"[]{'"x";'"y";'"L";'"T"}};"l_before"[]{'"y";'"x";'"L";'"T"}} }

interactive nuprl_l_before_member  '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "l_before"[]{'"a";'"b";'"L";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"b";'"L";'"T"} }

interactive nuprl_singleton_before   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"cons"[]{'"a";"nil"[]{}};'"T"};"false"[]{}} }

interactive nuprl_nil_before   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"nil"[]{};'"T"};"false"[]{}} }

interactive nuprl_l_before_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L1";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"y";'"L2";'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";"append"[]{'"L1";'"L2"};'"T"} }

interactive nuprl_l_before_member2  '"b"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "l_before"[]{'"a";'"b";'"L";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"a";'"L";'"T"} }

interactive nuprl_l_before_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"l_before"[]{'"x";'"y";'"L1";'"T"};"l_before"[]{'"x";'"y";'"L2";'"T"}}}}} }

interactive nuprl_cons_before   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"cons"[]{'"a";'"l"};'"T"};"or"[]{"and"[]{"equal"[]{'"T";'"x";'"a"};"mem"[]{'"y";'"l";'"T"}};"l_before"[]{'"x";'"y";'"l";'"T"}}} }

interactive nuprl_before_last   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{'"T";'"x";"last"[]{'"L"}}} }  -->
   sequent { <H> >- "l_before"[]{'"x";"last"[]{'"L"};'"L";'"T"} }

interactive nuprl_l_before_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "lt"[]{'"j";'"i"} }  -->
   sequent { <H> >- "l_before"[]{"select"[]{'"j";'"L"};"select"[]{'"i";'"L"};'"L";'"T"} }

define unfold_strong_before : "strong_before"[]{'"x";'"y";'"l";'"T"} <-->
      "and"[]{"and"[]{"mem"[]{'"x";'"l";'"T"};"mem"[]{'"y";'"l";'"T"}};"all"[]{"nat"[]{};"i"."all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"i";"length"[]{'"l"}};"implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};'"x"};"implies"[]{"equal"[]{'"T";"select"[]{'"j";'"l"};'"y"};"lt"[]{'"i";'"j"}}}}}}}}


interactive nuprl_strong_before_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- ("strong_before"[]{'"x";'"y";'"L";'"T"} in "univ"[level:l]{}) }

define unfold_same_order : "same_order"[]{'"x1";'"y1";'"x2";'"y2";'"L";'"T"} <-->
      "implies"[]{"strong_before"[]{'"x1";'"y1";'"L";'"T"};"implies"[]{"mem"[]{'"x2";'"L";'"T"};"implies"[]{"mem"[]{'"y2";'"L";'"T"};"strong_before"[]{'"x2";'"y2";'"L";'"T"}}}}


interactive nuprl_same_order_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x1" in '"T" }  -->
   [wf] sequent { <H> >- '"x2" in '"T" }  -->
   [wf] sequent { <H> >- '"y1" in '"T" }  -->
   [wf] sequent { <H> >- '"y2" in '"T" }  -->
   sequent { <H> >- ("same_order"[]{'"x1";'"y1";'"x2";'"y2";'"L";'"T"} in "univ"[level:l]{}) }

define unfold_l_succ : "l_succ"[]{'"x";'"l";'"T";"y".'"P"['"y"]} <-->
      "all"[]{"nat"[]{};"i"."implies"[]{"lt"[]{"add"[]{'"i";"number"[1:n]{}};"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};'"x"};'"P"["select"[]{"add"[]{'"i";"number"[1:n]{}};'"l"}]}}}


interactive nuprl_l_succ_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]} '"l" '"x"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("l_succ"[]{'"x";'"l";'"T";"y".'"P"['"y"]} in "univ"[level:l]{}) }

interactive nuprl_cons_succ  '"T" "lambda"[]{"x".'"P"['"x"]} '"l" '"a" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "l_succ"[]{'"x";"cons"[]{'"a";'"l"};'"T";"y".'"P"['"y"]} }  -->
   sequent { <H> >- "and"[]{"implies"[]{"equal"[]{'"T";'"x";'"a"};"implies"[]{"lt"[]{"number"[0:n]{};"length"[]{'"l"}};'"P"["hd"[]{'"l"}]}};"implies"[]{"not"[]{"equal"[]{'"T";'"x";'"a"}};"l_succ"[]{'"x";'"l";'"T";"y".'"P"['"y"]}}} }

define unfold_listp : "listp"[]{'"A"} <-->
      "set"[]{"list"[]{'"A"};"l"."assert"[]{"lt_bool"[]{"number"[0:n]{};"length"[]{'"l"}}}}


interactive nuprl_listp_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("listp"[]{'"A"} in "univ"[level:l]{}) }

interactive nuprl_listp_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "type"{"listp"[]{'"A"}} }

interactive nuprl_listp_properties  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "listp"[]{'"A"} }  -->
   sequent { <H> >- "ge"[]{"length"[]{'"l"};"number"[1:n]{}} }

interactive nuprl_hd_wf_listp {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "listp"[]{'"A"} }  -->
   sequent { <H> >- ("hd"[]{'"l"} in '"A") }

interactive nuprl_comb_for_hd_wf_listp   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"l"."lambda"[]{"z"."hd"[]{'"l"}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"listp"[]{'"A"};"l"."fun"[]{"squash"[]{"true"[]{}};"".'"A"}}}) }

interactive nuprl_map_equal3  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"a" in "listp"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"g" '"x" in '"T'" }  -->
   sequent { <H>; "x": '"T" ; "mem"[]{'"x";'"a";'"T"}  >- "equal"[]{'"T'";('"f" '"x");('"g" '"x")} }  -->
   sequent { <H> >- "equal"[]{"listp"[]{'"T'"};"map"[]{'"f";'"a"};"map"[]{'"g";'"a"}} }

interactive nuprl_hd_map  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"a" in "listp"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   sequent { <H> >- "equal"[]{'"T'";"hd"[]{"map"[]{'"f";'"a"}};('"f" "hd"[]{'"a"})} }

interactive nuprl_map_wf_listp {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"l" in "listp"[]{'"A"} }  -->
   sequent { <H> >- ("map"[]{'"f";'"l"} in "listp"[]{'"B"}) }

interactive nuprl_cons_wf_listp {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- ("cons"[]{'"x";'"l"} in "listp"[]{'"A"}) }

interactive nuprl_comb_for_cons_wf_listp   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"l"."lambda"[]{"x"."lambda"[]{"z"."cons"[]{'"x";'"l"}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"list"[]{'"A"};"l"."fun"[]{'"A";"x"."fun"[]{"squash"[]{"true"[]{}};""."listp"[]{'"A"}}}}}) }

define unfold_count : "count"[]{'"P";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"n"."add"[]{"ifthenelse"[]{('"P" '"a");"number"[1:n]{};"number"[0:n]{}};'"n"}}};"number"[0:n]{};'"L"}


interactive nuprl_count_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("count"[]{'"P";'"L"} in "nat"[]{}) }

define unfold_filter : "filter"[]{'"P";'"l"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"v"."ifthenelse"[]{('"P" '"a");"cons"[]{'"a";'"v"};'"v"}}};"nil"[]{};'"l"}


interactive nuprl_filter_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("filter"[]{'"P";'"l"} in "list"[]{'"T"}) }

interactive nuprl_filter_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L_1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L_2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L_1";'"L_2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"filter"[]{'"P";'"L_1"};"filter"[]{'"P";'"L_2"}} }

interactive nuprl_filter_is_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "sublist"[]{'"T";"filter"[]{'"P";'"L"};'"L"} }

interactive nuprl_length_filter  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"nat"[]{};"length"[]{"filter"[]{'"P";'"L"}};"count"[]{'"P";'"L"}} }

interactive nuprl_member_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"filter"[]{'"P";'"L"};'"T"};"and"[]{"mem"[]{'"x";'"L";'"T"};"assert"[]{('"P" '"x")}}} }

interactive nuprl_filter_before   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"filter"[]{'"P";'"L"};'"A"};"and"[]{"assert"[]{('"P" '"x")};"and"[]{"assert"[]{('"P" '"y")};"l_before"[]{'"x";'"y";'"L";'"A"}}}} }

interactive nuprl_agree_on_common_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as";'"bs"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";"filter"[]{'"P";'"as"};"filter"[]{'"P";'"bs"}} }

interactive_rw nuprl_filter_functionality  '"A" '"f2"  :
   "type"{'"A"} -->
   ('"L" in "list"[]{'"A"}) -->
   ('"f1" in "fun"[]{'"A";""."bool"[]{}}) -->
   ('"f2" in "fun"[]{'"A";""."bool"[]{}}) -->
   "equal"[]{"fun"[]{'"A";""."bool"[]{}};'"f1";'"f2"} -->
   "filter"[]{'"f1";'"L"} <--> "filter"[]{'"f2";'"L"}

interactive_rw nuprl_filter_append  '"T"  :
   "type"{'"T"} -->
   ('"P" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"l1" in "list"[]{'"T"}) -->
   ('"l2" in "list"[]{'"T"}) -->
   "filter"[]{'"P";"append"[]{'"l1";'"l2"}} <--> "append"[]{"filter"[]{'"P";'"l1"};"filter"[]{'"P";'"l2"}}

interactive_rw nuprl_filter_filter  '"T"  :
   "type"{'"T"} -->
   ('"P1" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"P2" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"L" in "list"[]{'"T"}) -->
   "filter"[]{'"P1";"filter"[]{'"P2";'"L"}} <--> "filter"[]{"lambda"[]{"t"."band"[]{('"P1" '"t");('"P2" '"t")}};'"L"}

interactive_rw nuprl_filter_filter_reduce  '"T"  :
   "type"{'"T"} -->
   ('"P1" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"P2" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"L" in "list"[]{'"T"}) -->
   "all"[]{'"T";"x"."implies"[]{"assert"[]{('"P1" '"x")};"assert"[]{('"P2" '"x")}}} -->
   "filter"[]{'"P1";"filter"[]{'"P2";'"L"}} <--> "filter"[]{'"P1";'"L"}

interactive nuprl_filter_type   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("filter"[]{'"P";'"l"} in "list"[]{"set"[]{'"T";"x"."assert"[]{('"P" '"x")}}}) }

interactive nuprl_filter_map  '"T1"  :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H>;"x": '"T1" >- '"f" '"x" in '"T2" }  -->
   [wf] sequent { <H>;"x": '"T2" >- '"Q" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T1"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T2"};"filter"[]{'"Q";"map"[]{'"f";'"L"}};"map"[]{'"f";"filter"[]{"compose"[]{'"Q";'"f"};'"L"}}} }

define unfold_iseg : "iseg"[]{'"T";'"l1";'"l2"} <-->
      "exists"[]{"list"[]{'"T"};"l"."equal"[]{"list"[]{'"T"};'"l2";"append"[]{'"l1";'"l"}}}


interactive nuprl_iseg_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("iseg"[]{'"T";'"l1";'"l2"} in "univ"[level:l]{}) }

interactive nuprl_cons_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"iseg"[]{'"T";"cons"[]{'"a";'"l1"};"cons"[]{'"b";'"l2"}};"and"[]{"equal"[]{'"T";'"a";'"b"};"iseg"[]{'"T";'"l1";'"l2"}}} }

interactive nuprl_iseg_transitivity  '"l2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l3" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l2";'"l3"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l3"} }

interactive nuprl_iseg_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l3" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";"append"[]{'"l2";'"l3"}} }

interactive nuprl_iseg_extend   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"v" in '"T" }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "cand"[]{"lt"[]{"length"[]{'"l1"};"length"[]{'"l2"}};"equal"[]{'"T";"select"[]{"length"[]{'"l1"};'"l2"};'"v"}} }  -->
   sequent { <H> >- "iseg"[]{'"T";"append"[]{'"l1";"cons"[]{'"v";"nil"[]{}}};'"l2"} }

interactive nuprl_firstn_is_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"iseg"[]{'"T";'"L1";'"L2"};"exists"[]{"int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L2"};"number"[1:n]{}}};"n"."equal"[]{"list"[]{'"T"};'"L1";"firstn"[]{'"n";'"L2"}}}} }

interactive nuprl_iseg_transitivity2  '"l2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l3" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l2";'"l3"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l3"} }

interactive nuprl_comb_for_iseg_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"l1"."lambda"[]{"l2"."lambda"[]{"z"."iseg"[]{'"T";'"l1";'"l2"}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"l1"."fun"[]{"list"[]{'"T"};"l2"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}}) }

interactive nuprl_iseg_weakening   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l";'"l"} }

interactive nuprl_nil_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";"nil"[]{};'"l"} }

interactive nuprl_iseg_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"iseg"[]{'"T";'"l1";'"l2"};"cand"[]{"le"[]{"length"[]{'"l1"};"length"[]{'"l2"}};"all"[]{"nat"[]{};"i"."implies"[]{"lt"[]{'"i";"length"[]{'"l1"}};"equal"[]{'"T";"select"[]{'"i";'"l1"};"select"[]{'"i";'"l2"}}}}}} }

interactive nuprl_iseg_member  '"l1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"l1";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"l2";'"T"} }

interactive nuprl_iseg_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"iseg"[]{'"T";'"L";"nil"[]{}};"assert"[]{"is_nil"[]{'"L"}}} }

interactive nuprl_agree_on_common_iseg  '"as2" '"bs2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"as1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs1" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"as1";'"as2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"bs1";'"bs2"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as2";'"bs2"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as1";'"bs1"} }

interactive nuprl_filter_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";"filter"[]{'"P";'"L1"};"filter"[]{'"P";'"L2"}} }

interactive nuprl_iseg_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L_1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L_2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"L_2";"filter"[]{'"P";'"L_1"}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L_3"."and"[]{"iseg"[]{'"T";'"L_3";'"L_1"};"equal"[]{"list"[]{'"T"};'"L_2";"filter"[]{'"P";'"L_3"}}}} }

interactive nuprl_iseg_append0   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";"append"[]{'"l1";'"l2"}} }

interactive nuprl_iseg_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "le"[]{"length"[]{'"l1"};"length"[]{'"l2"}} }

interactive nuprl_iseg_is_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L_1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L_2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"L_1";'"L_2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L_1";'"L_2"} }

define unfold_compat : "compat"[]{'"T";'"l1";'"l2"} <-->
      "or"[]{"iseg"[]{'"T";'"l1";'"l2"};"iseg"[]{'"T";'"l2";'"l1"}}


interactive nuprl_compat_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("compat"[]{'"T";'"l1";'"l2"} in "univ"[level:l]{}) }

interactive nuprl_common_iseg_compat  '"l"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l1";'"l"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"l2";'"l"} }  -->
   sequent { <H> >- "compat"[]{'"T";'"l1";'"l2"} }

define unfold_list_accum : "list_accum"[]{"x", "a".'"f"['"x";'"a"];'"y";'"l"} <-->
      ((("ycomb"[]{} "lambda"[]{"list_accum"."lambda"[]{"y"."lambda"[]{"l"."list_ind"[]{'"l";'"y";"b", "l'", "".(('"list_accum" '"f"['"y";'"b"]) '"l'")}}}}) '"y") '"l")


interactive nuprl_list_accum_wf {| intro[] |}  '"T" '"T'" '"l" '"y" "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"y" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T'";"x1": '"T" >- '"f"['"x";'"x1"] in '"T'" }  -->
   sequent { <H> >- ("list_accum"[]{"x", "a".'"f"['"x";'"a"];'"y";'"l"} in '"T'") }

interactive_rw nuprl_list_accum_split  '"T" '"l" '"i" '"y" "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   "type"{'"T"} -->
   ('"i" in "nat"[]{}) -->
   ('"l" in "list"[]{'"T"}) -->
   ("lambda"[]{"x1", "x".'"f"['"x1";'"x"]} in "fun"[]{"top"[]{};""."fun"[]{'"T";""."top"[]{}}}) -->
   "lt"[]{'"i";"length"[]{'"l"}} -->
   "list_accum"[]{"x", "a".'"f"['"x";'"a"];'"y";'"l"} <--> "list_accum"[]{"x", "a".'"f"['"x";'"a"];"list_accum"[]{"x", "a".'"f"['"x";'"a"];'"y";"firstn"[]{'"i";'"l"}};"nth_tl"[]{'"i";'"l"}}

define unfold_zip : "zip"[]{'"as";'"bs"} <-->
      ((("ycomb"[]{} "lambda"[]{"zip"."lambda"[]{"as"."lambda"[]{"bs"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."list_ind"[]{'"bs";"nil"[]{};"b", "bs'", ""."cons"[]{"pair"[]{'"a";'"b"};(('"zip" '"as'") '"bs'")}}}}}}) '"as") '"bs")


interactive nuprl_zip_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T1"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T2"} }  -->
   sequent { <H> >- ("zip"[]{'"as";'"bs"} in "list"[]{"prod"[]{'"T1";"".'"T2"}}) }

interactive nuprl_zip_length  '"T1" '"T2"  :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T1"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T2"} }  -->
   sequent { <H> >- "and"[]{"le"[]{"length"[]{"zip"[]{'"as";'"bs"}};"length"[]{'"as"}};"le"[]{"length"[]{"zip"[]{'"as";'"bs"}};"length"[]{'"bs"}}} }

interactive nuprl_select_zip   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T1"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T2"} }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i";"length"[]{"zip"[]{'"as";'"bs"}}} }  -->
   sequent { <H> >- "equal"[]{"prod"[]{'"T1";"".'"T2"};"select"[]{'"i";"zip"[]{'"as";'"bs"}};"pair"[]{"select"[]{'"i";'"as"};"select"[]{'"i";'"bs"}}} }

interactive nuprl_length_zip  '"T1" '"T2"  :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T1"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"as"};"length"[]{'"bs"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"zip"[]{'"as";'"bs"}};"length"[]{'"as"}} }

define unfold_unzip : "unzip"[]{'"as"} <-->
      "pair"[]{"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"as"};"map"[]{"lambda"[]{"p"."snd"[]{'"p"}};'"as"}}


interactive nuprl_unzip_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{"prod"[]{'"T1";"".'"T2"}} }  -->
   sequent { <H> >- ("unzip"[]{'"as"} in "prod"[]{"list"[]{'"T1"};""."list"[]{'"T2"}}) }

interactive nuprl_unzip_zip   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T1"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"as"};"length"[]{'"bs"}} }  -->
   sequent { <H> >- "equal"[]{"prod"[]{"list"[]{'"T1"};""."list"[]{'"T2"}};"unzip"[]{"zip"[]{'"as";'"bs"}};"pair"[]{'"as";'"bs"}} }

interactive nuprl_zip_unzip   :
   [wf] sequent { <H> >- "type"{'"T1" } }  -->
   [wf] sequent { <H> >- "type"{'"T2" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{"prod"[]{'"T1";"".'"T2"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"prod"[]{'"T1";"".'"T2"}};"zip"[]{"fst"[]{"unzip"[]{'"as"}};"snd"[]{"unzip"[]{'"as"}}};'"as"} }

define unfold_find : "find"[]{"x".'"P"['"x"];'"as";'"d"} <-->
      "list_ind"[]{"filter"[]{"lambda"[]{"x".'"P"['"x"]};'"as"};'"d";"a", "b", "".'"a"}


interactive nuprl_find_wf {| intro[] |}  '"T" '"d" '"as" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"d" in '"T" }  -->
   sequent { <H> >- ("find"[]{"a".'"P"['"a"];'"as";'"d"} in '"T") }

interactive nuprl_find_property  '"T" '"d" '"as" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"d" in '"T" }  -->
   sequent { <H> >- "or"[]{"mem"[]{"find"[]{"a".'"P"['"a"];'"as";'"d"};'"as";'"T"};"equal"[]{'"T";"find"[]{"a".'"P"['"a"];'"as";'"d"};'"d"}} }

define unfold_list_all : "list_all"[]{"x".'"P"['"x"];'"l"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"b"."and"[]{'"P"['"a"];'"b"}}};"true"[]{};'"l"}


interactive nuprl_list_all_wf {| intro[] |}  '"T" '"l" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("list_all"[]{"x".'"P"['"x"];'"l"} in "univ"[level:l]{}) }

interactive nuprl_list_all_iff  '"T" '"l" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"list_all"[]{"x".'"P"['"x"];'"l"};"all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"l";'"T"};'"P"['"x"]}}} }

define unfold_no_repeats : "no_repeats"[]{'"T";'"l"} <-->
      "all"[]{"nat"[]{};"i"."all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"i";"length"[]{'"l"}};"implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"not"[]{"equal"[]{"nat"[]{};'"i";'"j"}};"not"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};"select"[]{'"j";'"l"}}}}}}}}


interactive nuprl_no_repeats_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("no_repeats"[]{'"T";'"l"} in "univ"[level:l]{}) }

interactive nuprl_no_repeats_iff   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"no_repeats"[]{'"T";'"l"};"all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"l_before"[]{'"x";'"y";'"l";'"T"};"not"[]{"equal"[]{'"T";'"x";'"y"}}}}}} }

interactive nuprl_no_repeats_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"no_repeats"[]{'"T";"cons"[]{'"x";'"l"}};"and"[]{"no_repeats"[]{'"T";'"l"};"not"[]{"mem"[]{'"x";'"l";'"T"}}}} }

interactive nuprl_append_overlapping_sublists   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "no_repeats"[]{'"T";'"L"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"append"[]{'"L1";"cons"[]{'"x";"nil"[]{}}};'"L"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"cons"[]{'"x";'"L2"};'"L"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"append"[]{'"L1";"cons"[]{'"x";'"L2"}};'"L"} }

interactive nuprl_l_before_transitivity  '"y"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "no_repeats"[]{'"T";'"l"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"l";'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"y";'"z";'"l";'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"z";'"l";'"T"} }

interactive nuprl_l_before_antisymmetry   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "no_repeats"[]{'"T";'"l"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"l";'"T"} }  -->
   sequent { <H> >- "not"[]{"l_before"[]{'"y";'"x";'"l";'"T"}} }

interactive nuprl_no_repeats_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "no_repeats"[]{'"T";"nil"[]{}} }

define unfold_l_disjoint : "l_disjoint"[]{'"T";'"l1";'"l2"} <-->
      "all"[]{'"T";"x"."not"[]{"and"[]{"mem"[]{'"x";'"l1";'"T"};"mem"[]{'"x";'"l2";'"T"}}}}


interactive nuprl_l_disjoint_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l'" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("l_disjoint"[]{'"T";'"l";'"l'"} in "univ"[level:l]{}) }

interactive nuprl_l_disjoint_member  '"l1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "l_disjoint"[]{'"T";'"l1";'"l2"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"l1";'"T"} }  -->
   sequent { <H> >- "not"[]{"mem"[]{'"x";'"l2";'"T"}} }

interactive nuprl_no_repeats_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"l2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "no_repeats"[]{'"T";"append"[]{'"l1";'"l2"}} }  -->
   sequent { <H> >- "l_disjoint"[]{'"T";'"l1";'"l2"} }

define unfold_append_rel : "append_rel"[]{'"T";'"L1";'"L2";'"L"} <-->
      "equal"[]{"list"[]{'"T"};"append"[]{'"L1";'"L2"};'"L"}


interactive nuprl_append_rel_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("append_rel"[]{'"T";'"L1";'"L2";'"L"} in "univ"[level:l]{}) }

define unfold_safety : "safety"[]{'"A";"tr".'"P"['"tr"]} <-->
      "all"[]{"list"[]{'"A"};"tr1"."all"[]{"list"[]{'"A"};"tr2"."implies"[]{"iseg"[]{'"A";'"tr1";'"tr2"};"implies"[]{'"P"['"tr2"];'"P"['"tr1"]}}}}


interactive nuprl_safety_wf {| intro[] |}  '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("safety"[]{'"A";"x".'"P"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_no_repeats_safety   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "safety"[]{'"A";"L"."no_repeats"[]{'"A";'"L"}} }

interactive nuprl_filter_safety   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"T"} >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "safety"[]{'"T";"L".('"P" '"L")} }  -->
   sequent { <H> >- "safety"[]{'"T";"L".('"P" "filter"[]{'"f";'"L"})} }

interactive nuprl_all_safety  '"T" '"I" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"I" } }  -->
   [wf] sequent { <H>;"x": '"I";"x1": "list"[]{'"T"} >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"I"  >- "safety"[]{'"T";"L".'"P"['"x";'"L"]} }  -->
   sequent { <H> >- "safety"[]{'"T";"L"."all"[]{'"I";"x".'"P"['"x";'"L"]}} }

interactive nuprl_safety_and  '"A" "lambda"[]{"x".'"P"['"x"]} "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- "safety"[]{'"A";"x".'"P"['"x"]} }  -->
   sequent { <H> >- "safety"[]{'"A";"x".'"Q"['"x"]} }  -->
   sequent { <H> >- "safety"[]{'"A";"x"."and"[]{'"P"['"x"];'"Q"['"x"]}} }

interactive nuprl_safety_nil  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"T"} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"l".'"P"['"l"]} }  -->
   sequent { <H> >- "safety"[]{'"T";"x".'"P"['"x"]} }  -->
   sequent { <H> >- '"P"["nil"[]{}] }

interactive nuprl_cond_safety_and  '"A" "lambda"[]{"x".'"P"['"x"]} "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- "safety"[]{'"A";"x".'"P"['"x"]} }  -->
   sequent { <H>; "tr1": "list"[]{'"A"} ; "tr2": "list"[]{'"A"} ; "iseg"[]{'"A";'"tr1";'"tr2"} ; '"P"['"tr2"] ; '"Q"['"tr2"]  >- '"Q"['"tr1"] }  -->
   sequent { <H> >- "safety"[]{'"A";"x"."and"[]{'"P"['"x"];'"Q"['"x"]}} }

define unfold_l_all : "l_all"[]{'"L";'"T";"x".'"P"['"x"]} <-->
      "all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"L";'"T"};'"P"['"x"]}}


interactive nuprl_l_all_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("l_all"[]{'"L";'"T";"x".'"P"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_l_all_append  '"T" "lambda"[]{"x".'"P"['"x"]} '"L2" '"L1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{"append"[]{'"L1";'"L2"};'"T";"x".'"P"['"x"]};"and"[]{"l_all"[]{'"L1";'"T";"x".'"P"['"x"]};"l_all"[]{'"L2";'"T";"x".'"P"['"x"]}}} }

interactive nuprl_l_all_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "l_all"[]{"filter"[]{'"P";'"L"};'"T";"x"."assert"[]{('"P" '"x")}} }

interactive nuprl_l_all_cons  '"T" "lambda"[]{"x".'"P"['"x"]} '"L" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{"cons"[]{'"x";'"L"};'"T";"y".'"P"['"y"]};"and"[]{'"P"['"x"];"l_all"[]{'"L";'"T";"y".'"P"['"y"]}}} }

interactive nuprl_agree_on_common_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"cs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"ds" in "list"[]{'"T"} }  -->
   sequent { <H> >- "l_all"[]{'"cs";'"T";"x"."not"[]{"mem"[]{'"x";'"bs";'"T"}}} }  -->
   sequent { <H> >- "l_all"[]{'"as";'"T";"x"."not"[]{"mem"[]{'"x";'"ds";'"T"}}} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"as";'"cs"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";'"bs";'"ds"} }  -->
   sequent { <H> >- "agree_on_common"[]{'"T";"append"[]{'"as";'"bs"};"append"[]{'"cs";'"ds"}} }

interactive_rw nuprl_filter_trivial  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   "type"{'"T"} -->
   ("lambda"[]{"x".'"P"['"x"]} in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"L" in "list"[]{'"T"}) -->
   "l_all"[]{'"L";'"T";"x"."assert"[]{'"P"['"x"]}} -->
   "filter"[]{"lambda"[]{"x".'"P"['"x"]};'"L"} <--> '"L"

interactive nuprl_filter_trivial2  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x"."assert"[]{'"P"['"x"]}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter"[]{"lambda"[]{"x".'"P"['"x"]};'"L"};'"L"} }

interactive_rw nuprl_filter_is_nil  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   "type"{'"T"} -->
   ("lambda"[]{"x".'"P"['"x"]} in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"L" in "list"[]{'"T"}) -->
   "l_all"[]{'"L";'"T";"x"."not"[]{"assert"[]{'"P"['"x"]}}} -->
   "filter"[]{"lambda"[]{"x".'"P"['"x"]};'"L"} <--> "nil"[]{}

interactive nuprl_filter_is_singleton  '"T" '"L" '"x" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "l_member!"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "assert"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"y"."implies"[]{"assert"[]{'"P"['"y"]};"equal"[]{'"T";'"y";'"x"}}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter"[]{"lambda"[]{"x".'"P"['"x"]};'"L"};"cons"[]{'"x";"nil"[]{}}} }

interactive nuprl_list_set_type  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x".'"P"['"x"]} }  -->
   sequent { <H> >- ('"L" in "list"[]{"set"[]{'"T";"x".'"P"['"x"]}}) }

interactive nuprl_l_all_fwd  '"T" '"L" '"x" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"y".'"P"['"y"]} }  -->
   sequent { <H> >- '"P"['"x"] }

interactive nuprl_l_all_map  '"B" '"A" "lambda"[]{"x".'"P"['"x"]} '"L" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"B" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{"map"[]{'"f";'"L"};'"B";"x".'"P"['"x"]};"l_all"[]{'"L";'"A";"x".'"P"[('"f" '"x")]}} }

interactive nuprl_l_all_nil  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "l_all"[]{"nil"[]{};'"T";"x".'"P"['"x"]} }

interactive nuprl_l_all_reduce  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{'"L";'"T";"x"."assert"[]{'"P"['"x"]}};"assert"[]{"reduce"[]{"lambda"[]{"x"."lambda"[]{"y"."band"[]{'"P"['"x"];'"y"}}};"btrue"[]{};'"L"}}} }

interactive nuprl_split_rel_last  '"A" "lambda"[]{"x1", "x".'"r"['"x1";'"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"A" >- '"r"['"x";'"x1"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H>; "a": '"A"  >- "assert"[]{'"r"['"a";'"a"]} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"A"};"L1"."exists"[]{"list"[]{'"A"};"L2"."and"[]{"and"[]{"equal"[]{"list"[]{'"A"};'"L";"append"[]{'"L1";'"L2"}};"and"[]{"not"[]{"assert"[]{"is_nil"[]{'"L2"}}};"l_all"[]{'"L2";'"A";"b"."assert"[]{'"r"['"b";"last"[]{'"L"}]}}}};"implies"[]{"not"[]{"assert"[]{"is_nil"[]{'"L1"}}};"not"[]{"assert"[]{'"r"["last"[]{'"L1"};"last"[]{'"L"}]}}}}}} }

interactive nuprl_sublist_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "iff"[]{"sublist"[]{'"T";'"L2";"filter"[]{'"P";'"L1"}};"and"[]{"sublist"[]{'"T";'"L2";'"L1"};"l_all"[]{'"L2";'"T";"x"."assert"[]{('"P" '"x")}}}} }

interactive nuprl_sublist_filter_set_type   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L2";'"L1"} }  -->
   sequent { <H> >- "l_all"[]{'"L2";'"T";"x"."assert"[]{('"P" '"x")}} }  -->
   sequent { <H> >- "sublist"[]{"set"[]{'"T";"x"."assert"[]{('"P" '"x")}};'"L2";"filter"[]{'"P";'"L1"}} }

interactive nuprl_l_before_filter_set_type   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "set"[]{'"T";"x"."assert"[]{('"P" '"x")}} }  -->
   [wf] sequent { <H> >- '"y" in "set"[]{'"T";"x"."assert"[]{('"P" '"x")}} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"l";'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";"filter"[]{'"P";'"l"};"set"[]{'"T";"x"."assert"[]{('"P" '"x")}}} }

interactive nuprl_l_before_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"filter"[]{'"P";'"l"};'"T"};"and"[]{"assert"[]{('"P" '"x")};"and"[]{"assert"[]{('"P" '"y")};"l_before"[]{'"x";'"y";'"l";'"T"}}}} }

interactive nuprl_no_repeats_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   sequent { <H> >- "no_repeats"[]{'"T";'"l"} }  -->
   sequent { <H> >- "no_repeats"[]{'"T";"filter"[]{'"P";'"l"}} }

interactive nuprl_decidable__l_all  '"A" "lambda"[]{"x".'"F"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"F"['"x"] } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H>; "k": '"A"  >- "decidable"[]{'"F"['"k"]} }  -->
   sequent { <H> >- "decidable"[]{"l_all"[]{'"L";'"A";"k".'"F"['"k"]}} }

interactive nuprl_filter_is_empty  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"is_nil"[]{"filter"[]{'"P";'"L"}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."not"[]{"assert"[]{('"P" "select"[]{'"i";'"L"})}}}} }

interactive nuprl_filter_is_singleton2  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};"length"[]{"filter"[]{'"P";'"L"}};"number"[1:n]{}};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."and"[]{"assert"[]{('"P" "select"[]{'"i";'"L"})};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"j"."implies"[]{"assert"[]{('"P" "select"[]{'"j";'"L"})};"equal"[]{"int"[]{};'"i";'"j"}}}}}} }

interactive nuprl_append_split   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}  >- "decidable"[]{('"P" "select"[]{'"x";'"L"})} }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; "j": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"P" "select"[]{'"i";'"L"}) ; "lt"[]{'"i";'"j"}  >- ('"P" "select"[]{'"j";'"L"}) }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L1"."exists"[]{"list"[]{'"T"};"L2"."and"[]{"and"[]{"equal"[]{"list"[]{'"T"};'"L";"append"[]{'"L1";'"L2"}};"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"i"."not"[]{('"P" "select"[]{'"i";'"L1"})}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"i".('"P" "select"[]{'"i";'"L2"})}}};"l_all"[]{'"L";'"T";"x"."implies"[]{('"P" '"x");"mem"[]{'"x";'"L2";'"T"}}}}}} }

define unfold_l_all2 : "l_all2"[]{'"L";'"T";"x", "y".'"P"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"l_before"[]{'"x";'"y";'"L";'"T"};'"P"['"x";'"y"]}}}


interactive nuprl_l_all2_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"L"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("l_all2"[]{'"L";'"T";"x", "y".'"P"['"x";'"y"]} in "univ"[level:l]{}) }

interactive nuprl_l_all2_cons  '"T" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"L" '"u"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"P"['"x";'"x1"] } }  -->
   [wf] sequent { <H> >- '"u" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_all2"[]{"cons"[]{'"u";'"L"};'"T";"x", "y".'"P"['"x";'"y"]};"and"[]{"l_all"[]{'"L";'"T";"y".'"P"['"u";'"y"]};"l_all2"[]{'"L";'"T";"x", "y".'"P"['"x";'"y"]}}} }

define unfold_l_all_since : "l_all_since"[]{'"L";'"T";'"a";"x".'"P"['"x"]} <-->
      "and"[]{'"P"['"a"];"all"[]{'"T";"b"."implies"[]{"l_before"[]{'"a";'"b";'"L";'"T"};'"P"['"b"]}}}


interactive nuprl_l_all_since_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]} '"a" '"L"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   sequent { <H> >- ("l_all_since"[]{'"L";'"T";'"a";"x".'"P"['"x"]} in "univ"[level:l]{}) }

define unfold_l_exists : "l_exists"[]{'"L";'"T";"x".'"P"['"x"]} <-->
      "exists"[]{'"T";"x"."and"[]{"mem"[]{'"x";'"L";'"T"};'"P"['"x"]}}


interactive nuprl_l_exists_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("l_exists"[]{'"L";'"T";"x".'"P"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_l_exists_append  '"T" "lambda"[]{"x".'"P"['"x"]} '"L2" '"L1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"l_exists"[]{"append"[]{'"L1";'"L2"};'"T";"x".'"P"['"x"]};"or"[]{"l_exists"[]{'"L1";'"T";"x".'"P"['"x"]};"l_exists"[]{'"L2";'"T";"x".'"P"['"x"]}}} }

interactive nuprl_l_exists_nil  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"l_exists"[]{"nil"[]{};'"T";"x".'"P"['"x"]};"false"[]{}} }

interactive nuprl_l_exists_cons  '"T" "lambda"[]{"x".'"P"['"x"]} '"L" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"l_exists"[]{"cons"[]{'"x";'"L"};'"T";"y".'"P"['"y"]};"or"[]{'"P"['"x"];"l_exists"[]{'"L";'"T";"y".'"P"['"y"]}}} }

interactive nuprl_l_exists_reduce  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- "iff"[]{"l_exists"[]{'"L";'"T";"x"."assert"[]{'"P"['"x"]}};"assert"[]{"reduce"[]{"lambda"[]{"x"."lambda"[]{"y"."bor"[]{'"P"['"x"];'"y"}}};"bfalse"[]{};'"L"}}} }

interactive nuprl_decidable__l_exists  '"A" "lambda"[]{"x".'"F"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"F"['"x"] } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H>; "k": '"A"  >- "decidable"[]{'"F"['"k"]} }  -->
   sequent { <H> >- "decidable"[]{"l_exists"[]{'"L";'"A";"k".'"F"['"k"]}} }

define unfold_mapfilter : "mapfilter"[]{'"f";'"P";'"L"} <-->
      "map"[]{'"f";"filter"[]{'"P";'"L"}}


interactive nuprl_mapfilter_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H>;"x": "set"[]{'"T";"x"."assert"[]{('"P" '"x")}} >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("mapfilter"[]{'"f";'"P";'"L"} in "list"[]{'"T'"}) }

interactive nuprl_member_map_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H>;"x": "set"[]{'"T";"x"."assert"[]{('"P" '"x")}} >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T'" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"mapfilter"[]{'"f";'"P";'"L"};'"T'"};"exists"[]{'"T";"y"."and"[]{"mem"[]{'"y";'"L";'"T"};"cand"[]{"assert"[]{('"P" '"y")};"equal"[]{'"T'";'"x";('"f" '"y")}}}}} }

define unfold_split_tail : "split_tail"[]{"x".'"f"['"x"];'"L"} <-->
      (("ycomb"[]{} "lambda"[]{"split_tail"."lambda"[]{"L"."list_ind"[]{'"L";"pair"[]{"nil"[]{};"nil"[]{}};"a", "as", ""."spread"[]{('"split_tail" '"as");"hs", "ftail"."list_ind"[]{'"hs";"ifthenelse"[]{'"f"['"a"];"pair"[]{"nil"[]{};"cons"[]{'"a";'"ftail"}};"pair"[]{"cons"[]{'"a";"nil"[]{}};'"ftail"}};"x", "y", ""."pair"[]{"cons"[]{'"a";'"hs"};'"ftail"}}}}}}) '"L")


interactive nuprl_split_tail_wf {| intro[] |}  '"A" '"L" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("split_tail"[]{"x".'"f"['"x"];'"L"} in "prod"[]{"list"[]{'"A"};""."list"[]{'"A"}}) }

interactive nuprl_split_tail_trivial  '"A" "lambda"[]{"x".'"f"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H>; "b": '"A" ; "mem"[]{'"b";'"L";'"A"}  >- "assert"[]{'"f"['"b"]} }  -->
   sequent { <H> >- "equal"[]{"prod"[]{"list"[]{'"A"};""."list"[]{'"A"}};"split_tail"[]{"x".'"f"['"x"];'"L"};"pair"[]{"nil"[]{};'"L"}} }

interactive nuprl_split_tail_max  '"A" '"L" '"a" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "mem"[]{'"a";'"L";'"A"} }  -->
   sequent { <H> >- "assert"[]{'"f"['"a"]} }  -->
   sequent { <H>; "b": '"A" ; "l_before"[]{'"a";'"b";'"L";'"A"}  >- "assert"[]{'"f"['"b"]} }  -->
   sequent { <H> >- "mem"[]{'"a";"snd"[]{"split_tail"[]{"x".'"f"['"x"];'"L"}};'"A"} }

interactive nuprl_split_tail_correct  '"A" '"L" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "l_all"[]{"snd"[]{"split_tail"[]{"x".'"f"['"x"];'"L"}};'"A";"b"."assert"[]{'"f"['"b"]}} }

interactive nuprl_split_tail_rel  '"A" '"L" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"append"[]{"fst"[]{"split_tail"[]{"x".'"f"['"x"];'"L"}};"snd"[]{"split_tail"[]{"x".'"f"['"x"];'"L"}}};'"L"} }

interactive nuprl_split_tail_lemma  '"A" "lambda"[]{"x".'"f"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "l_all"[]{'"L";'"A";"a"."implies"[]{"l_all_since"[]{'"L";'"A";'"a";"b"."assert"[]{'"f"['"b"]}};"exists"[]{"list"[]{'"A"};"L1"."exists"[]{"list"[]{'"A"};"L2"."and"[]{"and"[]{"equal"[]{"list"[]{'"A"};'"L";"append"[]{'"L1";'"L2"}};"and"[]{"mem"[]{'"a";'"L2";'"A"};"l_all"[]{'"L2";'"A";"b"."assert"[]{'"f"['"b"]}}}};"implies"[]{"not"[]{"assert"[]{"is_nil"[]{'"L1"}}};"not"[]{"assert"[]{'"f"["last"[]{'"L1"}]}}}}}}}} }

define unfold_reduce2 : "reduce2"[]{'"f";'"k";'"i";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"reduce2"."lambda"[]{"i"."lambda"[]{"as"."list_ind"[]{'"as";'"k";"a", "as'", "".((('"f" '"a") '"i") (('"reduce2" "add"[]{'"i";"number"[1:n]{}}) '"as'"))}}}}) '"i") '"as")


interactive nuprl_reduce2_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"k" in '"A" }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": "int_seg"[]{'"i";"add"[]{'"i";"length"[]{'"L"}}};"x2": '"A" >- '"f" '"x" '"x1" '"x2" in '"A" }  -->
   sequent { <H> >- ("reduce2"[]{'"f";'"k";'"i";'"L"} in '"A") }

interactive nuprl_reduce2_shift  '"T"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"k" in '"A" }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": "int_seg"[]{'"i";"add"[]{'"i";"length"[]{'"L"}}};"x2": '"A" >- '"f" '"x" '"x1" '"x2" in '"A" }  -->
   sequent { <H> >- "equal"[]{'"A";"reduce2"[]{'"f";'"k";'"i";'"L"};"reduce2"[]{"lambda"[]{"x"."lambda"[]{"i"."lambda"[]{"l".((('"f" '"x") "sub"[]{'"i";"number"[1:n]{}}) '"l")}}};'"k";"add"[]{'"i";"number"[1:n]{}};'"L"}} }

interactive nuprl_comb_for_reduce2_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"T"."lambda"[]{"L"."lambda"[]{"k"."lambda"[]{"i"."lambda"[]{"f"."lambda"[]{"z"."reduce2"[]{'"f";'"k";'"i";'"L"}}}}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"L"."fun"[]{'"A";"k"."fun"[]{"nat"[]{};"i"."fun"[]{"fun"[]{'"T";""."fun"[]{"int_seg"[]{'"i";"add"[]{'"i";"length"[]{'"L"}}};""."fun"[]{'"A";"".'"A"}}};"f"."fun"[]{"squash"[]{"true"[]{}};"".'"A"}}}}}}}) }

define unfold_filter2 : "filter2"[]{'"P";'"L"} <-->
      "reduce2"[]{"lambda"[]{"x"."lambda"[]{"i"."lambda"[]{"l"."ifthenelse"[]{('"P" '"i");"cons"[]{'"x";'"l"};'"l"}}}};"nil"[]{};"number"[0:n]{};'"L"}


interactive nuprl_filter2_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- ("filter2"[]{'"P";'"L"} in "list"[]{'"T"}) }

interactive nuprl_cons_filter2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L"};"number"[1:n]{}}} >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter2"[]{'"P";"cons"[]{'"x";'"L"}};"ifthenelse"[]{('"P" "number"[0:n]{});"cons"[]{'"x";"filter2"[]{"lambda"[]{"i".('"P" "add"[]{'"i";"number"[1:n]{}})};'"L"}};"filter2"[]{"lambda"[]{"i".('"P" "add"[]{'"i";"number"[1:n]{}})};'"L"}}} }

interactive nuprl_filter_filter2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter"[]{'"P";'"L"};"filter2"[]{"lambda"[]{"i".('"P" "select"[]{'"i";'"L"})};'"L"}} }

interactive nuprl_member_filter2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"filter2"[]{'"P";'"L"};'"T"};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."and"[]{"equal"[]{'"T";'"x";"select"[]{'"i";'"L"}};"assert"[]{('"P" '"i")}}}} }

interactive nuprl_filter2_functionality   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f1" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f2" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};""."bool"[]{}};'"f1";'"f2"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"filter2"[]{'"f2";'"L"};"filter2"[]{'"f1";'"L"}} }

interactive nuprl_filter_of_filter2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"Q" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter"[]{'"Q";"filter2"[]{'"P";'"L"}};"filter2"[]{"lambda"[]{"i"."band"[]{('"P" '"i");('"Q" "select"[]{'"i";'"L"})}};'"L"}} }

define unfold_sublist_occurence : "sublist_occurence"[]{'"T";'"L1";'"L2";'"f"} <-->
      "and"[]{"increasing"[]{'"f";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f" '"j");'"L2"}}}}


interactive nuprl_sublist_occurence_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}} }  -->
   sequent { <H> >- ("sublist_occurence"[]{'"T";'"L1";'"L2";'"f"} in "univ"[level:l]{}) }

interactive nuprl_range_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"n"} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L1"."cand"[]{"equal"[]{"int"[]{};"length"[]{'"L1"};'"n"};"sublist_occurence"[]{'"T";'"L1";'"L";'"f"}}} }

define unfold_disjoint_sublists : "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} <-->
      "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."and"[]{"and"[]{"increasing"[]{'"f1";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f1" '"j");'"L"}}}};"and"[]{"and"[]{"increasing"[]{'"f2";"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L2"};"select"[]{('"f2" '"j");'"L"}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j2"."not"[]{"equal"[]{"int"[]{};('"f1" '"j1");('"f2" '"j2")}}}}}}}}


interactive nuprl_disjoint_sublists_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} in "univ"[level:l]{}) }

interactive nuprl_disjoint_sublists_sublist   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"sublist"[]{'"T";'"L1";'"L"};"sublist"[]{'"T";'"L2";'"L"}}} }

interactive nuprl_disjoint_sublists_witness   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f"."and"[]{"inject"[]{"int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};'"f"};"all"[]{"int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"i"."and"[]{"implies"[]{"lt"[]{'"i";"length"[]{'"L1"}};"equal"[]{'"T";"select"[]{'"i";'"L1"};"select"[]{('"f" '"i");'"L"}}};"implies"[]{"le"[]{"length"[]{'"L1"};'"i"};"equal"[]{'"T";"select"[]{"sub"[]{'"i";"length"[]{'"L1"}};'"L2"};"select"[]{('"f" '"i");'"L"}}}}}}} }

interactive nuprl_length_disjoint_sublists  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "le"[]{"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}};"length"[]{'"L"}} }

define unfold_interleaving : "interleaving"[]{'"T";'"L1";'"L2";'"L"} <-->
      "and"[]{"equal"[]{"nat"[]{};"length"[]{'"L"};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"}}


interactive nuprl_interleaving_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("interleaving"[]{'"T";'"L1";'"L2";'"L"} in "univ"[level:l]{}) }

interactive nuprl_l_before_interleaving  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"l_before"[]{'"x";'"y";'"L1";'"T"};"l_before"[]{'"x";'"y";'"L";'"T"}}}}} }

interactive nuprl_nil_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";"nil"[]{};'"L1";'"L"};"equal"[]{"list"[]{'"T"};'"L";'"L1"}} }

interactive nuprl_nil_interleaving2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";'"L1";"nil"[]{};'"L"};"equal"[]{"list"[]{'"T"};'"L";'"L1"}} }

interactive nuprl_member_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"T";"x"."iff"[]{"mem"[]{'"x";'"L";'"T"};"or"[]{"mem"[]{'"x";'"L1";'"T"};"mem"[]{'"x";'"L2";'"T"}}}}} }

interactive nuprl_cons_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";"cons"[]{'"x";'"L1"};'"L2";"cons"[]{'"x";'"L"}} }

interactive nuprl_comb_for_interleaving_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"L1"."lambda"[]{"L2"."lambda"[]{"L"."lambda"[]{"z"."interleaving"[]{'"T";'"L1";'"L2";'"L"}}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"L1"."fun"[]{"list"[]{'"T"};"L2"."fun"[]{"list"[]{'"T"};"L"."fun"[]{"squash"[]{"true"[]{}};""."univ"[level:l]{}}}}}}) }

interactive nuprl_length_interleaving  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "equal"[]{"nat"[]{};"length"[]{'"L"};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}} }

interactive nuprl_interleaving_of_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";'"L1";'"L2";"nil"[]{}};"and"[]{"equal"[]{"list"[]{'"T"};'"L1";"nil"[]{}};"equal"[]{"list"[]{'"T"};'"L2";"nil"[]{}}}} }

interactive nuprl_interleaving_symmetry   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";'"L1";'"L2";'"L"};"interleaving"[]{'"T";'"L2";'"L1";'"L"}} }

interactive nuprl_cons_interleaving2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";"cons"[]{'"x";'"L2"};"cons"[]{'"x";'"L"}} }

interactive nuprl_interleaving_of_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";'"L1";'"L2";"cons"[]{'"x";'"L"}};"or"[]{"cand"[]{"lt"[]{"number"[0:n]{};"length"[]{'"L1"}};"and"[]{"equal"[]{'"T";"select"[]{"number"[0:n]{};'"L1"};'"x"};"interleaving"[]{'"T";"tl"[]{'"L1"};'"L2";'"L"}}};"cand"[]{"lt"[]{"number"[0:n]{};"length"[]{'"L2"}};"and"[]{"equal"[]{'"T";"select"[]{"number"[0:n]{};'"L2"};'"x"};"interleaving"[]{'"T";'"L1";"tl"[]{'"L2"};'"L"}}}}} }

interactive nuprl_interleaving_filter2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"interleaving"[]{'"T";'"L1";'"L2";'"L"};"exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};""."bool"[]{}};"P"."and"[]{"equal"[]{"list"[]{'"T"};'"L1";"filter2"[]{'"P";'"L"}};"equal"[]{"list"[]{'"T"};'"L2";"filter2"[]{"lambda"[]{"i"."bnot"[]{('"P" '"i")}};'"L"}}}}} }

interactive nuprl_filter_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";"filter"[]{'"P";'"L1"};"filter"[]{'"P";'"L2"};"filter"[]{'"P";'"L"}} }

interactive nuprl_interleaving_as_filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "l_all"[]{'"L2";'"T";"x"."assert"[]{('"P" '"x")}} }  -->
   sequent { <H> >- "l_all"[]{'"L1";'"T";"x"."not"[]{"assert"[]{('"P" '"x")}}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"list"[]{'"T"};'"L2";"filter"[]{'"P";'"L"}};"equal"[]{"list"[]{'"T"};'"L1";"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}}} }

interactive nuprl_interleaving_as_filter_2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L2";"filter"[]{'"P";'"L2"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"filter"[]{'"P";'"L1"};"nil"[]{}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"list"[]{'"T"};'"L2";"filter"[]{'"P";'"L"}};"equal"[]{"list"[]{'"T"};'"L1";"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}}} }

interactive nuprl_sublist_interleaved   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L"} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L2"."interleaving"[]{'"T";'"L1";'"L2";'"L"}} }

interactive nuprl_interleaved_split  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "x": '"T"  >- "decidable"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L1"."exists"[]{"list"[]{'"T"};"L2"."and"[]{"interleaving"[]{'"T";'"L1";'"L2";'"L"};"and"[]{"all"[]{'"T";"x"."iff"[]{"mem"[]{'"x";'"L1";'"T"};"and"[]{"mem"[]{'"x";'"L";'"T"};'"P"['"x"]}}};"all"[]{'"T";"x"."iff"[]{"mem"[]{'"x";'"L2";'"T"};"and"[]{"mem"[]{'"x";'"L";'"T"};"not"[]{'"P"['"x"]}}}}}}}} }

interactive nuprl_interleaving_sublist  '"L2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L"} }

interactive nuprl_append_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";"append"[]{'"L1";'"L2"}} }

interactive nuprl_sublist_append1   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";"append"[]{'"L1";'"L2"}} }

interactive nuprl_sublist_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iseg"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }

interactive nuprl_l_before_iseg  '"L1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iseg"[]{'"T";'"L1";'"L2"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"L1";'"T"} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"L2";'"T"} }

define unfold_interleaving_occurence : "interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"} <-->
      "and"[]{"equal"[]{"nat"[]{};"length"[]{'"L"};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"and"[]{"and"[]{"increasing"[]{'"f1";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f1" '"j");'"L"}}}};"and"[]{"and"[]{"increasing"[]{'"f2";"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L2"};"select"[]{('"f2" '"j");'"L"}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j2"."not"[]{"equal"[]{"int"[]{};('"f1" '"j1");('"f2" '"j2")}}}}}}}


interactive nuprl_interleaving_occurence_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} >- '"f1" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}} >- '"f2" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- ("interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"} in "univ"[level:l]{}) }

interactive nuprl_interleaving_implies_occurence   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"}}} }

interactive nuprl_interleaving_occurence_onto  '"A" '"L"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} >- '"f1" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}} >- '"f2" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "interleaving_occurence"[]{'"A";'"L1";'"L2";'"L";'"f1";'"f2"} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "or"[]{"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"k"."equal"[]{"int"[]{};'"j";('"f1" '"k")}};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"k"."equal"[]{"int"[]{};'"j";('"f2" '"k")}}} }

interactive nuprl_interleaving_split   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P" '"x" } }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}  >- "decidable"[]{('"P" '"x")} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L1"."exists"[]{"list"[]{'"T"};"L2"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."and"[]{"interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"};"and"[]{"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"i".('"P" ('"f1" '"i"))};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"i"."not"[]{('"P" ('"f2" '"i"))}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."and"[]{"implies"[]{('"P" '"i");"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{"int"[]{};('"f1" '"j");'"i"}}};"implies"[]{"not"[]{('"P" '"i")};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j"."equal"[]{"int"[]{};('"f2" '"j");'"i"}}}}}}}}}}} }

interactive nuprl_interleaving_singleton   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"T"};"L2"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"number"[1:n]{}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."and"[]{"interleaving_occurence"[]{'"T";"cons"[]{"select"[]{'"i";'"L"};"nil"[]{}};'"L2";'"L";'"f1";'"f2"};"equal"[]{"int"[]{};('"f1" "number"[0:n]{});'"i"}}}}} }

interactive nuprl_last_with_property  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P" '"x" } }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}  >- "decidable"[]{('"P" '"x")} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i".('"P" '"i")} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."and"[]{('"P" '"i");"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"j"."implies"[]{"lt"[]{'"i";'"j"};"not"[]{('"P" '"j")}}}}} }

interactive nuprl_occurence_implies_interleaving  '"f2" '"f1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} >- '"f1" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}} >- '"f2" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";'"L1";'"L2";'"L"} }

interactive nuprl_filter_is_interleaving   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "interleaving"[]{'"T";"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"};"filter"[]{'"P";'"L"};'"L"} }

interactive nuprl_filter_interleaving_occurence   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{'"P";'"L"}}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."and"[]{"interleaving_occurence"[]{'"T";"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"};"filter"[]{'"P";'"L"};'"L";'"f1";'"f2"};"and"[]{"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."implies"[]{"assert"[]{('"P" "select"[]{'"i";'"L"})};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{'"P";'"L"}}};"k"."and"[]{"equal"[]{"int"[]{};'"i";('"f2" '"k")};"equal"[]{'"T";"select"[]{'"i";'"L"};"select"[]{'"k";"filter"[]{'"P";'"L"}}}}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."implies"[]{"not"[]{"assert"[]{('"P" "select"[]{'"i";'"L"})}};"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}};"k"."and"[]{"equal"[]{"int"[]{};'"i";('"f1" '"k")};"equal"[]{'"T";"select"[]{'"i";'"L"};"select"[]{'"k";"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}}}}}}};"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{"lambda"[]{"x"."bnot"[]{('"P" '"x")}};'"L"}}};"i"."not"[]{"assert"[]{('"P" "select"[]{('"f1" '"i");'"L"})}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{"filter"[]{'"P";'"L"}}};"i"."assert"[]{('"P" "select"[]{('"f2" '"i");'"L"})}}}}}}} }

define unfold_causal_order : "causal_order"[]{'"L";'"R";'"P";'"Q"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."implies"[]{('"Q" '"i");"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"j"."and"[]{"and"[]{"le"[]{'"j";'"i"};('"P" '"j")};(('"R" '"j") '"i")}}}}


interactive nuprl_causal_order_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"Q" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("causal_order"[]{'"L";'"R";'"P";'"Q"} in "univ"[level:l]{}) }

interactive nuprl_causal_order_filter_iseg  '"T" '"L" '"T'" "lambda"[]{"x".'"Q"['"x"]} '"g" "lambda"[]{"x".'"P"['"x"]} '"f"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"Q"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"g" '"x" in '"T'" }  -->
   sequent { <H>; "L'": "list"[]{'"T"} ; "iseg"[]{'"T";'"L'";'"L"}  >- "iseg"[]{'"T'";"map"[]{'"f";"filter2"[]{"lambda"[]{"x".'"P"['"x"]};'"L'"}};"map"[]{'"g";"filter2"[]{"lambda"[]{"x".'"Q"['"x"]};'"L'"}}} }  -->
   sequent { <H> >- "causal_order"[]{'"L";"lambda"[]{"i"."lambda"[]{"j"."equal"[]{'"T'";('"g" "select"[]{'"i";'"L"});('"f" "select"[]{'"j";'"L"})}}};"lambda"[]{"i"."assert"[]{'"Q"['"i"]}};"lambda"[]{"i"."assert"[]{'"P"['"i"]}}} }

interactive nuprl_causal_order_transitivity  '"T" '"P2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P3" '"x" } }  -->
   sequent { <H> >- "trans"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"_1", "_2".(('"R" '"_1") '"_2")} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";'"P2"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P2";'"P3"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";'"P3"} }

interactive nuprl_causal_order_reflexive  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P" '"x" } }  -->
   sequent { <H> >- "refl"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"_1", "_2".(('"R" '"_1") '"_2")} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P";'"P"} }

interactive nuprl_causal_order_or  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P3" '"x" } }  -->
   sequent { <H> >- "trans"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"_1", "_2".(('"R" '"_1") '"_2")} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";'"P2"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";'"P3"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";"lambda"[]{"i"."or"[]{('"P2" '"i");('"P3" '"i")}}} }

interactive nuprl_causal_order_sigma  '"T" '"L" '"A" '"R" "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]} "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P"['"x";'"x1"] } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"_1", "_2".(('"R" '"_1") '"_2")} }  -->
   sequent { <H>; "x": '"A"  >- "causal_order"[]{'"L";'"R";"lambda"[]{"i".'"P"['"x";'"i"]};"lambda"[]{"i".'"Q"['"x";'"i"]}} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";"lambda"[]{"i"."exists"[]{'"A";"x".'"P"['"x";'"i"]}};"lambda"[]{"i"."exists"[]{'"A";"x".'"Q"['"x";'"i"]}}} }

interactive nuprl_causal_order_monotonic  '"T" '"Q1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"Q2" '"i")  >- ('"Q1" '"i") }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P";'"Q1"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P";'"Q2"} }

interactive nuprl_causal_order_monotonic2  '"T" '"P1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"P1" '"i")  >- ('"P2" '"i") }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P1";'"Q"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R";'"P2";'"Q"} }

interactive nuprl_causal_order_monotonic3  '"T" '"P1" '"Q1" '"R1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"P1" '"i")  >- ('"P2" '"i") }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"Q2" '"i")  >- ('"Q1" '"i") }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; "j": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; (('"R1" '"i") '"j")  >- (('"R2" '"i") '"j") }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R1";'"P1";'"Q1"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R2";'"P2";'"Q2"} }

interactive nuprl_causal_order_monotonic4  '"T" '"P1" '"R1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P1" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"P2" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"Q" '"x" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; ('"P1" '"i")  >- ('"P2" '"i") }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; "y": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} ; (('"R1" '"x") '"y")  >- (('"R2" '"x") '"y") }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R1";'"P1";'"Q"} }  -->
   sequent { <H> >- "causal_order"[]{'"L";'"R2";'"P2";'"Q"} }

define unfold_interleaved_family_occurence : "interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"} <-->
      "and"[]{"and"[]{"all"[]{'"I";"i"."and"[]{"increasing"[]{('"f" '"i");"length"[]{('"L" '"i")}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};"j"."equal"[]{'"T";"select"[]{'"j";('"L" '"i")};"select"[]{(('"f" '"i") '"j");'"L2"}}}}};"all"[]{'"I";"i1"."all"[]{'"I";"i2"."implies"[]{"not"[]{"equal"[]{'"I";'"i1";'"i2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i1")}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i2")}};"j2"."not"[]{"equal"[]{"int"[]{};(('"f" '"i1") '"j1");(('"f" '"i2") '"j2")}}}}}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"x"."exists"[]{'"I";"i"."exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};"j"."equal"[]{"int"[]{};'"x";(('"f" '"i") '"j")}}}}}


interactive nuprl_interleaved_family_occurence_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"I" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"I" >- '"L" '"x" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"i": '"I";"x": "int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}} >- '"f" '"i" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}} }  -->
   sequent { <H> >- ("interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"} in "univ"[level:l]{}) }

define unfold_interleaved_family : "interleaved_family"[]{'"T";'"I";'"L";'"L2"} <-->
      "exists"[]{"fun"[]{'"I";"i"."fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}}}};"f"."interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"}}


interactive nuprl_interleaved_family_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"I" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"I" >- '"L" '"x" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("interleaved_family"[]{'"T";'"I";'"L";'"L2"} in "univ"[level:l]{}) }

define unfold_permute_list : "permute_list"[]{'"L";'"f"} <-->
      "mklist"[]{"length"[]{'"L"};"lambda"[]{"i"."select"[]{('"f" '"i");'"L"}}}


interactive nuprl_permute_list_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- ("permute_list"[]{'"L";'"f"} in "list"[]{'"T"}) }

interactive nuprl_permute_list_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"permute_list"[]{'"L";'"f"}};"select"[]{('"f" '"i");'"L"}} }

interactive nuprl_permute_list_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"permute_list"[]{'"L";'"f"}};"length"[]{'"L"}} }

interactive nuprl_permute_permute_list   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"g" '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"permute_list"[]{"permute_list"[]{'"L";'"f"};'"g"};"permute_list"[]{'"L";"compose"[]{'"f";'"g"}}} }

define unfold_swap : "swap"[]{'"L";'"i";'"j"} <-->
      "permute_list"[]{'"L";"flip"[]{'"i";'"j"}}


interactive nuprl_swap_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- ("swap"[]{'"L";'"i";'"j"} in "list"[]{'"T"}) }

interactive nuprl_swap_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"x";"swap"[]{'"L";'"i";'"j"}};"select"[]{("flip"[]{'"i";'"j"} '"x");'"L"}} }

interactive nuprl_swap_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"swap"[]{'"L";'"i";'"j"}};"length"[]{'"L"}} }

interactive nuprl_swap_swap   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"swap"[]{"swap"[]{'"L1";'"i";'"j"};'"i";'"j"};'"L1"} }

interactive nuprl_swapped_select   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L2";"swap"[]{'"L1";'"i";'"j"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"and"[]{"and"[]{"equal"[]{'"T";"select"[]{'"i";'"L2"};"select"[]{'"j";'"L1"}};"equal"[]{'"T";"select"[]{'"j";'"L2"};"select"[]{'"i";'"L1"}}};"and"[]{"equal"[]{"int"[]{};"length"[]{'"L2"};"length"[]{'"L1"}};"equal"[]{"list"[]{'"T"};'"L1";"swap"[]{'"L2";'"i";'"j"}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"x"."implies"[]{"not"[]{"equal"[]{"int"[]{};'"x";'"i"}};"implies"[]{"not"[]{"equal"[]{"int"[]{};'"x";'"j"}};"equal"[]{'"T";"select"[]{'"x";'"L2"};"select"[]{'"x";'"L1"}}}}}}} }

interactive nuprl_swap_cons   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[1:n]{};"add"[]{"length"[]{'"L"};"number"[1:n]{}}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[1:n]{};"add"[]{"length"[]{'"L"};"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"swap"[]{"cons"[]{'"x";'"L"};'"i";'"j"};"cons"[]{'"x";"swap"[]{'"L";"sub"[]{'"i";"number"[1:n]{}};"sub"[]{'"j";"number"[1:n]{}}}}} }

interactive nuprl_swap_adjacent_decomp   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "lt"[]{"add"[]{'"i";"number"[1:n]{}};"length"[]{'"L"}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{'"A"};"X"."exists"[]{"list"[]{'"A"};"Y"."and"[]{"equal"[]{"list"[]{'"A"};'"L";"append"[]{'"X";"append"[]{"cons"[]{"select"[]{'"i";'"L"};"cons"[]{"select"[]{"add"[]{'"i";"number"[1:n]{}};'"L"};"nil"[]{}}};'"Y"}}};"equal"[]{"list"[]{'"A"};"swap"[]{'"L";'"i";"add"[]{'"i";"number"[1:n]{}}};"append"[]{'"X";"append"[]{"cons"[]{"select"[]{"add"[]{'"i";"number"[1:n]{}};'"L"};"cons"[]{"select"[]{'"i";'"L"};"nil"[]{}}};'"Y"}}}}}} }

interactive nuprl_l_before_swap   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L"};"number"[1:n]{}}} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   sequent { <H> >- "l_before"[]{'"a";'"b";"swap"[]{'"L";'"i";"add"[]{'"i";"number"[1:n]{}}};'"T"} }  -->
   sequent { <H> >- "or"[]{"l_before"[]{'"a";'"b";'"L";'"T"};"and"[]{"equal"[]{'"T";'"a";"select"[]{"add"[]{'"i";"number"[1:n]{}};'"L"}};"equal"[]{'"T";'"b";"select"[]{'"i";'"L"}}}} }

interactive nuprl_map_swap  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"x" in "list"[]{'"B"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"x"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"length"[]{'"x"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"map"[]{'"f";"swap"[]{'"x";'"i";'"j"}};"swap"[]{"map"[]{'"f";'"x"};'"i";'"j"}} }

interactive nuprl_comb_for_swap_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"L"."lambda"[]{"i"."lambda"[]{"j"."lambda"[]{"z"."swap"[]{'"L";'"i";'"j"}}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"L"."fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"j"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"T"}}}}}}) }

define unfold_guarded_permutation : "guarded_permutation"[]{'"T";'"P"} <-->
      "rel_star"[]{"list"[]{'"T"};"lambda"[]{"L1"."lambda"[]{"L2"."exists"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L1"};"number"[1:n]{}}};"i"."and"[]{(('"P" '"L1") '"i");"equal"[]{"list"[]{'"T"};'"L2";"swap"[]{'"L1";'"i";"add"[]{'"i";"number"[1:n]{}}}}}}}}}


interactive nuprl_guarded_permutation_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"L": "list"[]{'"T"};"x": "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L"};"number"[1:n]{}}} >- '"P" '"L" '"x" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("guarded_permutation"[]{'"T";'"P"} in "fun"[]{"list"[]{'"T"};""."fun"[]{"list"[]{'"T"};""."univ"[level:l]{}}}) }

interactive nuprl_guarded_permutation_transitivity   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"L": "list"[]{'"T"};"x": "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L"};"number"[1:n]{}}} >- "type"{'"P" '"L" '"x" } }  -->
   sequent { <H> >- "trans"[]{"list"[]{'"T"};"_1", "_2"."infix_ap"[]{"guarded_permutation"[]{'"T";'"P"};'"_1";'"_2"}} }

define unfold_count_index_pairs : "count_index_pairs"[]{'"P";'"L"} <-->
      "double_sum"[]{"length"[]{'"L"};"length"[]{'"L"};"i", "j"."ifthenelse"[]{"band"[]{"lt_bool"[]{'"i";'"j"};((('"P" '"L") '"i") '"j")};"number"[1:n]{};"number"[0:n]{}}}


interactive nuprl_count_index_pairs_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"L": "list"[]{'"T"};"x": "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L"};"number"[1:n]{}}};"x1": "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}} >- '"P" '"L" '"x" '"x1" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("count_index_pairs"[]{'"P";'"L"} in "nat"[]{}) }

define unfold_count_pairs : "count_pairs"[]{'"L";"x", "y".'"P"['"x";'"y"]} <-->
      "double_sum"[]{"length"[]{'"L"};"length"[]{'"L"};"i", "j"."ifthenelse"[]{"band"[]{"lt_bool"[]{'"i";'"j"};'"P"["select"[]{'"i";'"L"};"select"[]{'"j";'"L"}]};"number"[1:n]{};"number"[0:n]{}}}


interactive nuprl_count_pairs_wf {| intro[] |}  '"T" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"P"['"x";'"x1"] in "bool"[]{} }  -->
   sequent { <H> >- ("count_pairs"[]{'"L";"x", "y".'"P"['"x";'"y"]} in "nat"[]{}) }

define unfold_first_index : "first_index"[]{'"L";"x".'"P"['"x"]} <-->
      "search"[]{"length"[]{'"L"};"lambda"[]{"i".'"P"["select"[]{'"i";'"L"}]}}


interactive nuprl_first_index_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- ("first_index"[]{'"L";"x".'"P"['"x"]} in "nat"[]{}) }

interactive_rw nuprl_first_index_cons  '"T" "lambda"[]{"x".'"P"['"x"]} '"L" '"a"  :
   "type"{'"T"} -->
   ('"L" in "list"[]{'"T"}) -->
   ('"a" in '"T") -->
   ("lambda"[]{"x".'"P"['"x"]} in "fun"[]{'"T";""."bool"[]{}}) -->
   "first_index"[]{"cons"[]{'"a";'"L"};"x".'"P"['"x"]} <--> "ifthenelse"[]{'"P"['"a"];"number"[1:n]{};"ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};"first_index"[]{'"L";"x".'"P"['"x"]}};"add"[]{"first_index"[]{'"L";"x".'"P"['"x"]};"number"[1:n]{}};"number"[0:n]{}}}

define unfold_agree_on : "agree_on"[]{'"T";"x".'"P"['"x"]} <-->
      "lambda"[]{"L1"."lambda"[]{"L2"."cand"[]{"equal"[]{"int"[]{};"length"[]{'"L1"};"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"i"."implies"[]{"or"[]{'"P"["select"[]{'"i";'"L1"}];'"P"["select"[]{'"i";'"L2"}]};"equal"[]{'"T";"select"[]{'"i";'"L1"};"select"[]{'"i";'"L2"}}}}}}}


interactive nuprl_agree_on_wf {| intro[] |}  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("agree_on"[]{'"T";"a".'"P"['"a"]} in "fun"[]{"list"[]{'"T"};""."fun"[]{"list"[]{'"T"};""."univ"[level:l]{}}}) }

interactive nuprl_first_index_equal  '"T" '"L2" '"L1" "lambda"[]{"x".'"P"['"x"]} "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"Q"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- "infix_ap"[]{"agree_on"[]{'"T";"a"."assert"[]{'"P"['"a"]}};'"L1";'"L2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"first_index"[]{'"L1";"a"."band"[]{'"P"['"a"];'"Q"['"a"]}};"first_index"[]{'"L2";"a"."band"[]{'"P"['"a"];'"Q"['"a"]}}} }

interactive nuprl_iseg_map  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"A"} }  -->
   sequent { <H> >- "iseg"[]{'"A";'"L1";'"L2"} }  -->
   sequent { <H> >- "iseg"[]{'"B";"map"[]{'"f";'"L1"};"map"[]{'"f";'"L2"}} }

interactive nuprl_safety_induced  '"B" '"A" "lambda"[]{"x".'"P"['"x"]} '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": "list"[]{'"B"} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "safety"[]{'"B";"L".'"P"['"L"]} }  -->
   sequent { <H> >- "safety"[]{'"A";"L".'"P"["map"[]{'"f";'"L"}]} }

interactive nuprl_agree_on_equiv  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "equiv_rel"[]{"list"[]{'"T"};"_1", "_2"."infix_ap"[]{"agree_on"[]{'"T";"a".'"P"['"a"]};'"_1";'"_2"}} }

define unfold_strong_safety : "strong_safety"[]{'"T";"tr".'"P"['"tr"]} <-->
      "all"[]{"list"[]{'"T"};"tr1"."all"[]{"list"[]{'"T"};"tr2"."implies"[]{"sublist"[]{'"T";'"tr1";'"tr2"};"implies"[]{'"P"['"tr2"];'"P"['"tr1"]}}}}


interactive nuprl_strong_safety_wf {| intro[] |}  '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("strong_safety"[]{'"A";"x".'"P"['"x"]} in "univ"[level:l]{}) }

interactive nuprl_filter_strong_safety   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"T"} >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "strong_safety"[]{'"T";"L".('"P" '"L")} }  -->
   sequent { <H> >- "strong_safety"[]{'"T";"L".('"P" "filter"[]{'"f";'"L"})} }

interactive nuprl_strong_safety_safety  '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"A"} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "strong_safety"[]{'"A";"x".'"P"['"x"]} }  -->
   sequent { <H> >- "safety"[]{'"A";"x".'"P"['"x"]} }

define unfold_l_subset : "l_subset"[]{'"T";'"as";'"bs"} <-->
      "all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"as";'"T"};"mem"[]{'"x";'"bs";'"T"}}}


interactive nuprl_l_subset_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("l_subset"[]{'"T";'"as";'"bs"} in "univ"[level:l]{}) }

define unfold_sublist__ : "sublist*"[]{'"T";'"as";'"bs"} <-->
      "all"[]{"list"[]{'"T"};"cs"."implies"[]{"sublist"[]{'"T";'"cs";'"as"};"implies"[]{"l_subset"[]{'"T";'"cs";'"bs"};"sublist"[]{'"T";'"cs";'"bs"}}}}


interactive nuprl_sublist___wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("sublist*"[]{'"T";'"as";'"bs"} in "univ"[level:l]{}) }

interactive nuprl_sublist___filter   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist*"[]{'"T";'"as";'"bs"} }  -->
   sequent { <H> >- "sublist*"[]{'"T";"filter"[]{'"P";'"as"};"filter"[]{'"P";'"bs"}} }


(**** display forms ****)


dform nuprl_mklist_df : except_mode[src] :: "mklist"[]{'"n";'"f"} =
   `"mklist(" slot{'"n"} `";" slot{'"f"} `")"



dform nuprl_agree_on_common_df : except_mode[src] :: "agree_on_common"[]{'"T";'"as";'"bs"} =
   `"agree_on_common(" slot{'"T"} `";" slot{'"as"} `";" slot{'"bs"} `")"


dform nuprl_last_df : except_mode[src] :: "last"[]{'"L"} =
   `"last(" slot{'"L"} `")"


dform nuprl_reverse_select_df : except_mode[src] :: "reverse_select"[]{'"l";'"n"} =
   `"reverse_select(" slot{'"l"} `";" slot{'"n"} `")"


dform nuprl_l_member___df : except_mode[src] :: "l_member!"[]{'"x";'"l";'"T"} =
   `"l_member!(" slot{'"x"} `";" slot{'"l"} `";" slot{'"T"} `")"

dform nuprl_l_member___df : except_mode[src] :: "l_member!"[]{'"x";'"l";'"T"} =
   `"(" slot{'"x"} `" " member `"! " slot{'"l"} `")"


dform nuprl_sublist_df : except_mode[src] :: "sublist"[]{'"T";'"L1";'"L2"} =
   `"" slot{'"L1"} `" " sqsubseteq `" " slot{'"L2"} `""


dform nuprl_l_before_df : except_mode[src] :: "l_before"[]{'"x";'"y";'"l";'"T"} =
   `"" slot{'"x"} `" before " slot{'"y"} `" " member `" " slot{'"l"} `" " member `" "
    slot{'"T"} `""

dform nuprl_l_before_df : except_mode[src] :: "l_before"[]{'"x";'"y";'"l";'"T"} =
   `"" slot{'"x"} `" before " slot{'"y"} `" " member `" " slot{'"l"} `""


dform nuprl_strong_before_df : except_mode[src] :: "strong_before"[]{'"x";'"y";'"l";'"T"} =
   `"" slot{'"x"} `" << " slot{'"y"} `" " member `" " slot{'"l"} `""


dform nuprl_same_order_df : except_mode[src] :: "same_order"[]{'"x1";'"y1";'"x2";'"y2";'"L";'"T"} =
   `"same_order(" slot{'"x1"} `";" slot{'"y1"} `";" slot{'"x2"} `";" slot{'"y2"}
    `";" slot{'"L"} `";" slot{'"T"} `")"


dform nuprl_l_succ_df : except_mode[src] :: "l_succ"[]{'"x";'"l";'"T";"y".'"P"} =
   `"" slot{'"y"} `"" member `"" slot{'"T"} `" = succ(" slot{'"x"} `") in " slot{'"l"}
    `"" sbreak["",""] `"" Rightarrow `" " slot{'"P"} `""

dform nuprl_l_succ_df : except_mode[src] :: "l_succ"[]{'"x";'"l";'"T";"y".'"P"} =
   `"" slot{'"y"} `" = succ(" slot{'"x"} `") in " slot{'"l"} `"" sbreak["",""]
    `"" Rightarrow `" " slot{'"P"} `""


dform nuprl_listp_df : except_mode[src] :: "listp"[]{'"A"} =
   `"" slot{'"A"} `" List" supplus `""


dform nuprl_count_df : except_mode[src] :: "count"[]{'"P";'"L"} =
   `"count(" slot{'"P"} `";" slot{'"L"} `")"


dform nuprl_filter_df : except_mode[src] :: "filter"[]{'"P";'"l"} =
   `"filter(" slot{'"P"} `";" slot{'"l"} `")"


dform nuprl_iseg_df : except_mode[src] :: "iseg"[]{'"T";'"l1";'"l2"} =
   `"" slot{'"l1"} `" " le `" " slot{'"l2"} `" " member `" " slot{'"T"} `" List"

dform nuprl_iseg_df : except_mode[src] :: "iseg"[]{'"T";'"l1";'"l2"} =
   `"" slot{'"l1"} `" " le `" " slot{'"l2"} `""


dform nuprl_compat_df : except_mode[src] :: "compat"[]{'"T";'"l1";'"l2"} =
   `"" slot{'"l1"} `" || " slot{'"l2"} `""


dform nuprl_list_accum_df : except_mode[src] :: "list_accum"[]{"x", "a".'"f";'"y";'"l"} =
   `"list_accum(" slot{'"x"} `"," slot{'"a"} `"." slot{'"f"} `";" slot{'"y"} `";"
    slot{'"l"} `")"


dform nuprl_zip_df : except_mode[src] :: "zip"[]{'"as";'"bs"} =
   `"zip(" slot{'"as"} `";" slot{'"bs"} `")"


dform nuprl_unzip_df : except_mode[src] :: "unzip"[]{'"as"} =
   `"unzip(" slot{'"as"} `")"


dform nuprl_find_df : except_mode[src] :: "find"[]{"x".'"P";'"as";'"d"} =
   `"(first " slot{'"x"} `" " member `" " slot{'"as"} `" s.t. " slot{'"P"} `" else "
    slot{'"d"} `")"


dform nuprl_list_all_df : except_mode[src] :: "list_all"[]{"x".'"P";'"l"} =
   `"list_all(" slot{'"x"} `"." slot{'"P"} `";" slot{'"l"} `")"


dform nuprl_no_repeats_df : except_mode[src] :: "no_repeats"[]{'"T";'"l"} =
   `"no_repeats(" slot{'"T"} `";" slot{'"l"} `")"


dform nuprl_l_disjoint_df : except_mode[src] :: "l_disjoint"[]{'"T";'"l1";'"l2"} =
   `"l_disjoint(" slot{'"T"} `";" slot{'"l1"} `";" slot{'"l2"} `")"


dform nuprl_append_rel_df : except_mode[src] :: "append_rel"[]{'"T";'"L1";'"L2";'"L"} =
   `"append_rel(" slot{'"T"} `";" slot{'"L1"} `";" slot{'"L2"} `";" slot{'"L"} `")"


dform nuprl_safety_df : except_mode[src] :: "safety"[]{'"A";"tr".'"P"} =
   `"safety(" slot{'"A"} `";" slot{'"tr"} `"." slot{'"P"} `")"


dform nuprl_l_all_df : except_mode[src] :: "l_all"[]{'"L";'"T";"x".'"P"} =
   `"l_all(" slot{'"L"} `";" slot{'"T"} `";" slot{'"x"} `"." slot{'"P"} `")"

dform nuprl_l_all_df : except_mode[src] :: "l_all"[]{'"L";'"T";"x".'"P"} =
   `"(" forall `"" slot{'"x"} `"" member `"" slot{'"L"} `"." slot{'"P"} `")"


dform nuprl_l_all2_df : except_mode[src] :: "l_all2"[]{'"L";'"T";"x", "y".'"P"} =
   `"l_all2(" slot{'"L"} `";" slot{'"T"} `";" slot{'"x"} `"," slot{'"y"} `"."
    slot{'"P"} `")"

dform nuprl_l_all2_df : except_mode[src] :: "l_all2"[]{'"L";'"T";"x", "y".'"P"} =
   `"(" forall `"" slot{'"x"} `"<" slot{'"y"} `"" member `"" slot{'"L"} `"." slot{'"P"} `")"


dform nuprl_l_all_since_df : except_mode[src] :: "l_all_since"[]{'"L";'"T";'"a";"x".'"P"} =
   `"l_all_since(" slot{'"L"} `";" slot{'"T"} `";" slot{'"a"} `";" slot{'"x"} `"."
    slot{'"P"} `")"

dform nuprl_l_all_since_df : except_mode[src] :: "l_all_since"[]{'"L";'"T";'"a";"x".'"P"} =
   `"(" forall `"" slot{'"x"} `"" ge `"" slot{'"a"} `"" member `"" slot{'"L"} `"." slot{'"P"}
    `")"


dform nuprl_l_exists_df : except_mode[src] :: "l_exists"[]{'"L";'"T";"x".'"P"} =
   `"l_exists(" slot{'"L"} `";" slot{'"T"} `";" slot{'"x"} `"." slot{'"P"} `")"

dform nuprl_l_exists_df : except_mode[src] :: "l_exists"[]{'"L";'"T";"x".'"P"} =
   `"(" "exists" `"" slot{'"x"} `"" member `"" slot{'"L"} `"." slot{'"P"} `")"


dform nuprl_mapfilter_df : except_mode[src] :: "mapfilter"[]{'"f";'"P";'"L"} =
   `"mapfilter(" slot{'"f"} `";" slot{'"P"} `";" slot{'"L"} `")"


dform nuprl_split_tail_df : except_mode[src] :: "split_tail"[]{"x".'"f";'"L"} =
   `"split_tail(" slot{'"x"} `"." slot{'"f"} `";" slot{'"L"} `")"

dform nuprl_split_tail_df : except_mode[src] :: "split_tail"[]{"x".'"f";'"L"} =
   `"split_tail(" slot{'"L"} `" | " forall `"" slot{'"x"} `"." slot{'"f"} `")"


dform nuprl_reduce2_df : except_mode[src] :: "reduce2"[]{'"f";'"k";'"i";'"as"} =
   `"reduce2(" slot{'"f"} `";" slot{'"k"} `";" slot{'"i"} `";" slot{'"as"} `")"


dform nuprl_filter2_df : except_mode[src] :: "filter2"[]{'"P";'"L"} =
   `"filter2(" slot{'"P"} `";" slot{'"L"} `")"


dform nuprl_sublist_occurence_df : except_mode[src] :: "sublist_occurence"[]{'"T";'"L1";'"L2";'"f"} =
   `"sublist_occurence(" slot{'"T"} `";" slot{'"L1"} `";" slot{'"L2"} `";"
    slot{'"f"} `")"


dform nuprl_disjoint_sublists_df : except_mode[src] :: "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} =
   `"disjoint_sublists(" slot{'"T"} `";" slot{'"L1"} `";" slot{'"L2"} `";"
    slot{'"L"} `")"


dform nuprl_interleaving_df : except_mode[src] :: "interleaving"[]{'"T";'"L1";'"L2";'"L"} =
   `"interleaving(" slot{'"T"} `";" slot{'"L1"} `";" slot{'"L2"} `";" slot{'"L"}
    `")"


dform nuprl_interleaving_occurence_df : except_mode[src] :: "interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"} =
   `"interleaving_occurence(" slot{'"T"} `";" slot{'"L1"} `";" slot{'"L2"} `";"
    slot{'"L"} `";" slot{'"f1"} `";" slot{'"f2"} `")"


dform nuprl_causal_order_df : except_mode[src] :: "causal_order"[]{'"L";'"R";'"P";'"Q"} =
   `"causal_order(" slot{'"L"} `";" slot{'"R"} `";" slot{'"P"} `";" slot{'"Q"} `")"


dform nuprl_interleaved_family_occurence_df : except_mode[src] :: "interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"} =
   `"interleaved_family_occurence(" slot{'"T"} `";" slot{'"I"} `";" slot{'"L"} `";"
    slot{'"L2"} `";" slot{'"f"} `")"


dform nuprl_interleaved_family_df : except_mode[src] :: "interleaved_family"[]{'"T";'"I";'"L";'"L2"} =
   `"interleaved_family(" slot{'"T"} `";" slot{'"I"} `";" slot{'"L"} `";"
    slot{'"L2"} `")"


dform nuprl_permute_list_df : except_mode[src] :: "permute_list"[]{'"L";'"f"} =
   `"permute_list(" slot{'"L"} `";" slot{'"f"} `")"

dform nuprl_permute_list_df : except_mode[src] :: "permute_list"[]{'"L";'"f"} =
   `"(" slot{'"L"} `" o " slot{'"f"} `")"


dform nuprl_swap_df : except_mode[src] :: "swap"[]{'"L";'"i";'"j"} =
   `"swap(" slot{'"L"} `";" slot{'"i"} `";" slot{'"j"} `")"


dform nuprl_guarded_permutation_df : except_mode[src] :: "guarded_permutation"[]{'"T";'"P"} =
   `"guarded_permutation(" slot{'"T"} `";" slot{'"P"} `")"


dform nuprl_count_index_pairs_df : except_mode[src] :: "count_index_pairs"[]{'"P";'"L"} =
   `"count_index_pairs(" slot{'"P"} `";" slot{'"L"} `")"

dform nuprl_count_index_pairs_df : except_mode[src] :: "count_index_pairs"[]{'"P";'"L"} =
   `"count(i<j<||" slot{'"L"} `"|| : " slot{'"P"} `" " slot{'"L"} `" i j)"


dform nuprl_count_pairs_df : except_mode[src] :: "count_pairs"[]{'"L";"x", "y".'"P"} =
   `"count_pairs(" slot{'"L"} `";" slot{'"x"} `"," slot{'"y"} `"." slot{'"P"} `")"

dform nuprl_count_pairs_df : except_mode[src] :: "count_pairs"[]{'"L";"x", "y".'"P"} =
   `"count(" slot{'"x"} `" < " slot{'"y"} `" in " slot{'"L"} `" | " slot{'"P"} `")"



dform nuprl_first_index_df : except_mode[src] :: "first_index"[]{'"L";"x".'"P"} =
   `"first_index(" slot{'"L"} `";" slot{'"x"} `"." slot{'"P"} `")"

dform nuprl_first_index_df : except_mode[src] :: "first_index"[]{'"L";"x".'"P"} =
   `"index-of-first " slot{'"x"} `" in " slot{'"L"} `"." slot{'"P"} `""


dform nuprl_agree_on_df : except_mode[src] :: "agree_on"[]{'"T";"x".'"P"} =
   `"agree_on(" slot{'"T"} `";" slot{'"x"} `"." slot{'"P"} `")"


dform nuprl_strong_safety_df : except_mode[src] :: "strong_safety"[]{'"T";"tr".'"P"} =
   `"strong_safety(" slot{'"T"} `";" slot{'"tr"} `"." slot{'"P"} `")"


dform nuprl_l_subset_df : except_mode[src] :: "l_subset"[]{'"T";'"as";'"bs"} =
   `"l_subset(" slot{'"T"} `";" slot{'"as"} `";" slot{'"bs"} `")"


dform nuprl_sublist___df : except_mode[src] :: "sublist*"[]{'"T";'"as";'"bs"} =
   `"sublist*(" slot{'"T"} `";" slot{'"as"} `";" slot{'"bs"} `")"


