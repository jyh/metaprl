extends Ma_strong__subtype__stuff

open Dtactic


interactive_rw nuprl_fun_exp_add_sq   :
   ('"n" in "nat"[]{}) -->
   ('"m" in "nat"[]{}) -->
   ("fun_exp"[]{'"f";"add"[]{'"n";'"m"}} '"i") <--> ("fun_exp"[]{'"f";'"n"} ("fun_exp"[]{'"f";'"m"} '"i"))

interactive nuprl_all__but__one  '"T" '"L" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T"  >- "decidable"[]{"equal"[]{'"T";'"x";'"y"}} }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{'"L";'"T";"x"."l_all"[]{'"L";'"T";"y"."implies"[]{"not"[]{"equal"[]{'"T";'"x";'"y"}};"or"[]{'"P"['"x"];'"P"['"y"]}}}};"l_exists"[]{'"L";'"T";"x"."l_all"[]{'"L";'"T";"y"."implies"[]{"not"[]{"equal"[]{'"T";'"x";'"y"}};'"P"['"y"]}}}} }

interactive nuprl_no_repeats_member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "no_repeats"[]{'"T";'"L"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "l_member!"[]{'"x";'"L";'"T"} }

define unfold_imax__list : "imax-list"[]{'"L"} <-->
      "list_accum"[]{"x", "y"."imax"[]{'"x";'"y"};"hd"[]{'"L"};"tl"[]{'"L"}}


interactive nuprl_imax__list_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"L" in "list"[]{"int"[]{}} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- ("imax-list"[]{'"L"} in "int"[]{}) }

interactive nuprl_imax__list__ub   :
   [wf] sequent { <H> >- '"L" in "list"[]{"int"[]{}} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"a";"imax-list"[]{'"L"}};"l_exists"[]{'"L";"int"[]{};"b"."le"[]{'"a";'"b"}}} }

interactive nuprl_imax__list__lb   :
   [wf] sequent { <H> >- '"L" in "list"[]{"int"[]{}} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "iff"[]{"le"[]{"imax-list"[]{'"L"};'"a"};"l_all"[]{'"L";"int"[]{};"b"."le"[]{'"b";'"a"}}} }

interactive nuprl_maximal__in__list   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"length"[]{'"L"}} }  -->
   sequent { <H> >- "l_exists"[]{'"L";'"A";"a"."l_all"[]{'"L";'"A";"x"."le"[]{('"f" '"x");('"f" '"a")}}} }

interactive nuprl_member__le__max   :
   [wf] sequent { <H> >- '"L" in "list"[]{"int"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";"int"[]{}} }  -->
   sequent { <H> >- "le"[]{'"x";"imax-list"[]{'"L"}} }

interactive nuprl_l_member_subtype  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"A"} }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"B"} }

interactive nuprl_l_all__nil  "lambda"[]{"x".'"P"['"x"]} '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{"nil"[]{};'"T";"x".'"P"['"x"]};"true"[]{}} }

interactive nuprl_l_all_iff  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"l_all"[]{'"L";'"T";"x".'"P"['"x"]};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i".'"P"["select"[]{'"i";'"L"}]}} }

define unfold_l_interval : "l_interval"[]{'"l";'"j";'"i"} <-->
      "mklist"[]{"sub"[]{'"i";'"j"};"lambda"[]{"x"."select"[]{"add"[]{'"j";'"x"};'"l"}}}


interactive nuprl_l_interval_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"add"[]{'"i";"number"[1:n]{}}} }  -->
   sequent { <H> >- ("l_interval"[]{'"l";'"j";'"i"} in "list"[]{'"T"}) }

interactive nuprl_length_l_interval  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"add"[]{'"i";"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"l_interval"[]{'"l";'"j";'"i"}};"sub"[]{'"i";'"j"}} }

interactive nuprl_select_l_interval   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};"add"[]{'"i";"number"[1:n]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};"sub"[]{'"i";'"j"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"x";"l_interval"[]{'"l";'"j";'"i"}};"select"[]{"add"[]{'"j";'"x"};'"l"}} }

interactive nuprl_hd_l_interval   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"i"} }  -->
   sequent { <H> >- "equal"[]{'"T";"hd"[]{"l_interval"[]{'"l";'"j";'"i"}};"select"[]{'"j";'"l"}} }

interactive nuprl_last_l_interval   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"l"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"i"} }  -->
   sequent { <H> >- "equal"[]{'"T";"last"[]{"l_interval"[]{'"l";'"j";'"i"}};"select"[]{"sub"[]{'"i";"number"[1:n]{}};'"l"}} }

define unfold_pairwise : "pairwise"[]{"x", "y".'"P"['"x";'"y"];'"L"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."all"[]{"int_seg"[]{"number"[0:n]{};'"i"};"j".'"P"["select"[]{'"j";'"L"};"select"[]{'"i";'"L"}]}}


interactive nuprl_pairwise_wf {| intro[] |} univ[level:l] '"T" '"L" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"P"['"x";'"x1"] in "univ"[level':l]{} }  -->
   sequent { <H> >- ("pairwise"[]{"x", "y".'"P"['"x";'"y"];'"L"} in "univ"[level':l]{}) }

interactive nuprl_pairwise__nil  "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   sequent { <H> >- "iff"[]{"pairwise"[]{"x", "y".'"P"['"x";'"y"];"nil"[]{}};"true"[]{}} }

interactive nuprl_pairwise__singleton  '"v" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   sequent { <H> >- "iff"[]{"pairwise"[]{"x", "y".'"P"['"x";'"y"];"cons"[]{'"v";"nil"[]{}}};"true"[]{}} }

interactive nuprl_pairwise__cons  '"T" '"L" '"x" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H> >- "iff"[]{"pairwise"[]{"x", "y".'"P"['"x";'"y"];"cons"[]{'"x";'"L"}};"and"[]{"pairwise"[]{"x", "y".'"P"['"x";'"y"];'"L"};"l_all"[]{'"L";'"T";"y".'"P"['"x";'"y"]}}} }

define unfold_inv__rel : "inv-rel"[]{'"A";'"B";'"f";'"finv"} <-->
      "and"[]{"all"[]{'"A";"a"."all"[]{'"B";"b"."implies"[]{"equal"[]{"union"[]{'"A";"unit"[]{}};('"finv" '"b");"inl"[]{'"a"}};"equal"[]{'"B";'"b";('"f" '"a")}}}};"all"[]{'"A";"a"."equal"[]{"union"[]{'"A";"unit"[]{}};('"finv" ('"f" '"a"));"inl"[]{'"a"}}}}


interactive nuprl_inv__rel_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"finv" '"x" in "union"[]{'"A";"unit"[]{}} }  -->
   sequent { <H> >- ("inv-rel"[]{'"A";'"B";'"f";'"finv"} in "univ"[level:l]{}) }

interactive nuprl_inv__rel__inject  '"finv"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"finv" '"x" in "union"[]{'"A";"unit"[]{}} }  -->
   sequent { <H> >- "inv-rel"[]{'"A";'"B";'"f";'"finv"} }  -->
   sequent { <H> >- "inject"[]{'"A";'"B";'"f"} }

interactive nuprl_hd__filter  '"T" "lambda"[]{"x".'"P"['"x"]} '"as"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "exists"[]{'"T";"a"."and"[]{"mem"[]{'"a";'"as";'"T"};"assert"[]{'"P"['"a"]}}} }  -->
   sequent { <H> >- "cand"[]{("hd"[]{"filter"[]{"lambda"[]{"a".'"P"['"a"]};'"as"}} in '"T");"and"[]{"mem"[]{"hd"[]{"filter"[]{"lambda"[]{"a".'"P"['"a"]};'"as"}};'"as";'"T"};"assert"[]{'"P"["hd"[]{"filter"[]{"lambda"[]{"a".'"P"['"a"]};'"as"}}]}}} }

interactive nuprl_find__hd__filter  '"T" "lambda"[]{"x".'"P"['"x"]} '"as" '"d"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "exists"[]{'"T";"a"."and"[]{"mem"[]{'"a";'"as";'"T"};"assert"[]{'"P"['"a"]}}} }  -->
   sequent { <H> >- "equal"[]{'"T";"find"[]{"a".'"P"['"a"];'"as";'"d"};"hd"[]{"filter"[]{"lambda"[]{"a".'"P"['"a"]};'"as"}}} }

interactive nuprl_list__set__type   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ('"L" in "list"[]{"set"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}}}) }

interactive nuprl_list__set__type2  '"T" "lambda"[]{"x".'"P"['"x"]} '"L"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "l_all"[]{'"L";'"T";"x".'"P"['"x"]} }  -->
   sequent { <H> >- ('"L" in "list"[]{"set"[]{'"T";"x".'"P"['"x"]}}) }

interactive nuprl_l_member_set  '"A" "lambda"[]{"x".'"P"['"x"]} '"L" '"x"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "l_all"[]{'"L";'"A";"x".'"P"['"x"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"mem"[]{'"x";'"L";'"A"};"mem"[]{'"x";'"L";"set"[]{'"A";"x".'"P"['"x"]}}}} }

interactive nuprl_map__wf2  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": "set"[]{'"A";"x"."mem"[]{'"x";'"L";'"A"}} >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("map"[]{'"f";'"L"} in "list"[]{'"B"}) }

interactive nuprl_wellfounded__anti__reflexive univ[level:l] '"T" "lambda"[]{"x1", "x".'"R"['"x1";'"x"]} '"a"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "well_founded"[level:l]{'"T";"x", "y".'"R"['"x";'"y"]} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   sequent { <H> >- "not"[]{'"R"['"a";'"a"]} }

interactive_rw nuprl_no__member__sq__nil  '"T"  :
   "type"{'"T"} -->
   ('"L" in "list"[]{'"T"}) -->
   "all"[]{'"T";"x"."not"[]{"mem"[]{'"x";'"L";'"T"}}} -->
   '"L" <--> "nil"[]{}

interactive nuprl_l_before_append_iff   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"A" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"B" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"append"[]{'"A";'"B"};'"T"};"or"[]{"l_before"[]{'"x";'"y";'"A";'"T"};"or"[]{"l_before"[]{'"x";'"y";'"B";'"T"};"and"[]{"mem"[]{'"x";'"A";'"T"};"mem"[]{'"y";'"B";'"T"}}}}} }

interactive_rw nuprl_append_assoc_sq   :
   ('"as" in "list"[]{"top"[]{}}) -->
   ('"bs" in "list"[]{"top"[]{}}) -->
   ('"cs" in "list"[]{"top"[]{}}) -->
   "append"[]{"append"[]{'"as";'"bs"};'"cs"} <--> "append"[]{'"as";"append"[]{'"bs";'"cs"}}

interactive_rw nuprl_append__nil   :
   ('"l" in "list"[]{"top"[]{}}) -->
   "append"[]{'"l";"nil"[]{}} <--> '"l"

interactive nuprl_nil__iff__no__member   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"list"[]{'"T"};'"L";"nil"[]{}};"all"[]{'"T";"x"."not"[]{"mem"[]{'"x";'"L";'"T"}}}} }

interactive nuprl_tl_sublist  '"a"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"T"} }  -->
   sequent { <H> >- "sublist"[]{'"T";"cons"[]{'"a";'"L1"};'"L2"} }  -->
   sequent { <H> >- "sublist"[]{'"T";'"L1";'"L2"} }

define unfold_dectt : "dectt"[]{'"d"} <-->
      "is_inl"[]{'"d"}


interactive nuprl_dectt_wf {| intro[] |}  '"p"  :
   [wf] sequent { <H> >- "type"{'"p" } }  -->
   [wf] sequent { <H> >- '"d" in "decidable"[]{'"p"} }  -->
   sequent { <H> >- ("dectt"[]{'"d"} in "bool"[]{}) }

interactive nuprl_assert__dectt   :
   [wf] sequent { <H> >- "type"{'"p" } }  -->
   [wf] sequent { <H> >- '"d" in "decidable"[]{'"p"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"dectt"[]{'"d"}};'"p"} }

interactive nuprl_inr_equal  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"y" in '"B" }  -->
   sequent { <H> >- "equal"[]{"union"[]{'"A";'"B"};"inr"[]{'"x"};"inr"[]{'"y"}} }  -->
   sequent { <H> >- "equal"[]{'"B";'"x";'"y"} }

interactive nuprl_inl_equal  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "equal"[]{"union"[]{'"A";'"B"};"inl"[]{'"x"};"inl"[]{'"y"}} }  -->
   sequent { <H> >- "equal"[]{'"A";'"x";'"y"} }

interactive nuprl_inl_eq_inr  '"A" '"B" '"y" '"x"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"B" }  -->
   sequent { <H> >- "equal"[]{"union"[]{'"A";'"B"};"inl"[]{'"x"};"inr"[]{'"y"}} }  -->
   sequent { <H> >- "false"[]{} }

interactive nuprl_inr_eq_inl  '"A" '"B" '"x" '"y"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"B" }  -->
   sequent { <H> >- "equal"[]{"union"[]{'"A";'"B"};"inr"[]{'"y"};"inl"[]{'"x"}} }  -->
   sequent { <H> >- "false"[]{} }

define unfold_finite__type : "finite-type"[]{'"T"} <-->
      "exists"[]{"nat"[]{};"n"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"n"};"".'"T"};"f"."surject"[]{"int_seg"[]{"number"[0:n]{};'"n"};'"T";'"f"}}}


interactive nuprl_finite__type_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("finite-type"[]{'"T"} in "univ"[level:l]{}) }

interactive nuprl_finite__type_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "type"{"finite-type"[]{'"T"}} }

interactive nuprl_finite__type__iff__list   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "iff"[]{"finite-type"[]{'"T"};"exists"[]{"list"[]{'"T"};"L"."all"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}}}} }

interactive nuprl_finite__set__type  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "x": '"T"  >- "sqst"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "iff"[]{"finite-type"[]{"set"[]{'"T";"x".'"P"['"x"]}};"exists"[]{"list"[]{'"T"};"L"."all"[]{'"T";"x"."iff"[]{'"P"['"x"];"mem"[]{'"x";'"L";'"T"}}}}} }

interactive nuprl_finite__decidable__set  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "x": '"T"  >- "decidable"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "iff"[]{"finite-type"[]{"set"[]{'"T";"x".'"P"['"x"]}};"exists"[]{"list"[]{'"T"};"L"."all"[]{'"T";"x"."implies"[]{'"P"['"x"];"mem"[]{'"x";'"L";'"T"}}}}} }

interactive nuprl_finite__subtype  '"B" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"B" >- '"P"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- "finite-type"[]{'"B"} }  -->
   sequent { <H> >- "finite-type"[]{"set"[]{'"B";"b"."assert"[]{'"P"['"b"]}}} }

interactive_rw nuprl_map__map   :
   ('"as" in "list"[]{"top"[]{}}) -->
   "map"[]{'"g";"map"[]{'"f";'"as"}} <--> "map"[]{"compose"[]{'"g";'"f"};'"as"}

interactive nuprl_map_is_nil   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"list"[]{'"B"};"map"[]{'"f";'"l"};"nil"[]{}};"equal"[]{"list"[]{'"A"};'"l";"nil"[]{}}} }

interactive_rw nuprl_map__id   :
   ('"L" in "list"[]{"top"[]{}}) -->
   "map"[]{"lambda"[]{"x".'"x"};'"L"} <--> '"L"

interactive_rw nuprl_length__map  '"T"  :
   "type"{'"T"} -->
   ('"L" in "list"[]{'"T"}) -->
   "length"[]{"map"[]{'"f";'"L"}} <--> "length"[]{'"L"}

interactive_rw nuprl_select__map  '"T"  :
   "type"{'"T"} -->
   ('"L" in "list"[]{'"T"}) -->
   ('"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}) -->
   "select"[]{'"i";"map"[]{'"f";'"L"}} <--> ('"f" "select"[]{'"i";'"L"})

interactive nuprl_pairwise__map  '"T'" '"T" '"L" '"f" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": '"T'";"x1": '"T'" >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H> >- "iff"[]{"pairwise"[]{"x", "y".'"P"['"x";'"y"];"map"[]{'"f";'"L"}};"pairwise"[]{"x", "y".'"P"[('"f" '"x");('"f" '"y")];'"L"}} }

interactive nuprl_general_length_nth_tl   :
   [wf] sequent { <H> >- '"r" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"top"[]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"nth_tl"[]{'"r";'"L"}};"ifthenelse"[]{"lt_bool"[]{'"r";"length"[]{'"L"}};"sub"[]{"length"[]{'"L"};'"r"};"number"[0:n]{}}} }

interactive_rw nuprl_nth_tl_nil   :
   ('"n" in "nat"[]{}) -->
   "nth_tl"[]{'"n";"nil"[]{}} <--> "nil"[]{}

define unfold_mu : "mu"[]{'"f"} <-->
      (("ycomb"[]{} "lambda"[]{"mu"."lambda"[]{"f"."ifthenelse"[]{('"f" "number"[0:n]{});"number"[0:n]{};"add"[]{('"mu" "lambda"[]{"x".('"f" "add"[]{'"x";"number"[1:n]{}})});"number"[1:n]{}}}}}) '"f")


interactive nuprl_mu_wf {| intro[] |}   :
   [wf] sequent { <H>;"x": "nat"[]{} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"n"."assert"[]{('"f" '"n")}} }  -->
   sequent { <H> >- ("mu"[]{'"f"} in "nat"[]{}) }

interactive nuprl_mu__property   :
   [wf] sequent { <H>;"x": "nat"[]{} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"n"."assert"[]{('"f" '"n")}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"assert"[]{('"f" "mu"[]{'"f"})};"all"[]{"nat"[]{};"i"."implies"[]{"lt"[]{'"i";"mu"[]{'"f"}};"not"[]{"assert"[]{('"f" '"i")}}}}}} }

interactive nuprl_mu__bound   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"b"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};'"b"};"n"."assert"[]{('"f" '"n")}} }  -->
   sequent { <H> >- ("mu"[]{'"f"} in "int_seg"[]{"number"[0:n]{};'"b"}) }

interactive nuprl_mu__bound__property   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"b"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};'"b"};"n"."assert"[]{('"f" '"n")}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"assert"[]{('"f" "mu"[]{'"f"})};"all"[]{"int_seg"[]{"number"[0:n]{};'"b"};"i"."implies"[]{"lt"[]{'"i";"mu"[]{'"f"}};"not"[]{"assert"[]{('"f" '"i")}}}}}} }

interactive nuprl_mu__bound__property__   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"b"} >- '"f" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};'"b"};"n"."assert"[]{('"f" '"n")}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{("mu"[]{'"f"} in "int_seg"[]{"number"[0:n]{};'"b"});"and"[]{"assert"[]{('"f" "mu"[]{'"f"})};"all"[]{"int_seg"[]{"number"[0:n]{};'"b"};"i"."implies"[]{"lt"[]{'"i";"mu"[]{'"f"}};"not"[]{"assert"[]{('"f" '"i")}}}}}}} }

interactive nuprl_mu__bound__unique  '"b"  :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"b"} >- '"f" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"b"} }  -->
   sequent { <H> >- "and"[]{"assert"[]{('"f" '"x")};"all"[]{"int_seg"[]{"number"[0:n]{};'"b"};"y"."implies"[]{"assert"[]{('"f" '"y")};"equal"[]{"int"[]{};'"y";'"x"}}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mu"[]{'"f"};'"x"} }

define unfold_upto : "upto"[]{'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"upto"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};"nil"[]{};"append"[]{('"upto" "sub"[]{'"n";"number"[1:n]{}});"cons"[]{"sub"[]{'"n";"number"[1:n]{}};"nil"[]{}}}}}}) '"n")


interactive nuprl_upto_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- ("upto"[]{'"n"} in "list"[]{"int_seg"[]{"number"[0:n]{};'"n"}}) }

interactive_rw nuprl_length_upto   :
   ('"n" in "nat"[]{}) -->
   "length"[]{"upto"[]{'"n"}} <--> '"n"

interactive nuprl_upto_is_nil   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"list"[]{"int"[]{}};"upto"[]{'"n"};"nil"[]{}};"equal"[]{"int"[]{};'"n";"number"[0:n]{}}} }

interactive_rw nuprl_upto_decomp  '"n"  :
   ('"m" in "nat"[]{}) -->
   ('"n" in "int_seg"[]{"number"[0:n]{};"add"[]{'"m";"number"[1:n]{}}}) -->
   "upto"[]{'"m"} <--> "append"[]{"upto"[]{'"n"};"map"[]{"lambda"[]{"x"."add"[]{'"x";'"n"}};"upto"[]{"sub"[]{'"m";'"n"}}}}

interactive nuprl_upto_iseg   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "nat"[]{} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }  -->
   sequent { <H> >- "iseg"[]{"int_seg"[]{"number"[0:n]{};'"j"};"upto"[]{'"i"};"upto"[]{'"j"}} }

interactive nuprl_select_upto   :
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"select"[]{'"n";"upto"[]{'"m"}};'"n"} }

interactive nuprl_member_upto   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"i";"upto"[]{'"n"};"nat"[]{}};"lt"[]{'"i";'"n"}} }

interactive nuprl_member_upto2   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i";'"n"} }  -->
   sequent { <H> >- "mem"[]{'"i";"upto"[]{'"n"};"int_seg"[]{"number"[0:n]{};'"n"}} }

interactive nuprl_before__upto   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   [wf] sequent { <H> >- '"y" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x";'"y";"upto"[]{'"n"};"int_seg"[]{"number"[0:n]{};'"n"}};"lt"[]{'"x";'"y"}} }

interactive nuprl_list__eq__set__type  '"T" '"B" '"A" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H> >- '"A" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"B" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"A";'"B"} }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};"length"[]{'"A"}}  >- '"P"["select"[]{'"i";'"A"}] }  -->
   sequent { <H> >- "equal"[]{"list"[]{"set"[]{'"T";"x".'"P"['"x"]}};'"A";'"B"} }

interactive nuprl_before__map   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x'" in '"T'" }  -->
   [wf] sequent { <H> >- '"y'" in '"T'" }  -->
   sequent { <H> >- "iff"[]{"l_before"[]{'"x'";'"y'";"map"[]{'"f";'"L"};'"T'"};"exists"[]{'"T";"x"."exists"[]{'"T";"y"."and"[]{"l_before"[]{'"x";'"y";'"L";'"T"};"and"[]{"equal"[]{'"T'";('"f" '"x");'"x'"};"equal"[]{'"T'";('"f" '"y");'"y'"}}}}}} }

interactive_rw nuprl_filter_append_sq  '"T"  :
   "type"{'"T"} -->
   ('"P" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"A" in "list"[]{'"T"}) -->
   "filter"[]{'"P";"append"[]{'"A";'"B"}} <--> "append"[]{"filter"[]{'"P";'"A"};"filter"[]{'"P";'"B"}}

interactive nuprl_filter_map_upto  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }  -->
   [wf] sequent { <H>;"x": "nat"[]{} >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "assert"[]{('"P" ('"f" '"i"))} }  -->
   sequent { <H> >- "lt"[]{"length"[]{"filter"[]{'"P";"map"[]{'"f";"upto"[]{'"i"}}}};"length"[]{"filter"[]{'"P";"map"[]{'"f";"upto"[]{'"j"}}}}} }

interactive nuprl_filter_map_upto2  '"T" '"t'"  :
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "nat"[]{} >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "le"[]{"add"[]{'"m";"number"[1:n]{}};"length"[]{"filter"[]{'"P";"map"[]{'"f";"upto"[]{'"t'"}}}}} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"t"."and"[]{"assert"[]{('"P" ('"f" '"t"))};"equal"[]{"int"[]{};"length"[]{"filter"[]{'"P";"map"[]{'"f";"upto"[]{'"t"}}}};'"m"}}} }

interactive nuprl_member__firstn   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L"};"number"[1:n]{}}} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"firstn"[]{'"n";'"L"};'"T"};"exists"[]{"int_seg"[]{"number"[0:n]{};'"n"};"i"."equal"[]{'"T";'"x";"select"[]{'"i";'"L"}}}} }

interactive_rw nuprl_first0   :
   ('"L" in "list"[]{"top"[]{}}) -->
   "firstn"[]{"number"[0:n]{};'"L"} <--> "nil"[]{}

interactive_rw nuprl_firstn_decomp2  '"T"  :
   "type"{'"T"} -->
   ('"j" in "nat"[]{}) -->
   ('"l" in "list"[]{'"T"}) -->
   "lt"[]{"number"[0:n]{};'"j"} -->
   "le"[]{'"j";"length"[]{'"l"}} -->
   "append"[]{"firstn"[]{"sub"[]{'"j";"number"[1:n]{}};'"l"};"cons"[]{"select"[]{"sub"[]{'"j";"number"[1:n]{}};'"l"};"nil"[]{}}} <--> "firstn"[]{'"j";'"l"}

interactive_rw nuprl_firstn_firstn   :
   ('"L" in "list"[]{"top"[]{}}) -->
   ('"n" in "int"[]{}) -->
   ('"m" in "int_seg"[]{"number"[0:n]{};'"n"}) -->
   "firstn"[]{'"m";"firstn"[]{'"n";'"L"}} <--> "firstn"[]{'"m";'"L"}

interactive nuprl_firstn_last   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"assert"[]{"is_nil"[]{'"L"}}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};'"L";"append"[]{"firstn"[]{"sub"[]{"length"[]{'"L"};"number"[1:n]{}};'"L"};"cons"[]{"last"[]{'"L"};"nil"[]{}}}} }

interactive_rw nuprl_firstn_append   :
   ('"L1" in "list"[]{"top"[]{}}) -->
   ('"L2" in "list"[]{"top"[]{}}) -->
   ('"n" in "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"L1"};"number"[1:n]{}}}) -->
   "firstn"[]{'"n";"append"[]{'"L1";'"L2"}} <--> "firstn"[]{'"n";'"L1"}

interactive_rw nuprl_firstn_length   :
   ('"L" in "list"[]{"top"[]{}}) -->
   "firstn"[]{"length"[]{'"L"};'"L"} <--> '"L"

interactive_rw nuprl_firstn_all   :
   ('"L" in "list"[]{"top"[]{}}) -->
   ('"n" in "int"[]{}) -->
   "le"[]{"length"[]{'"L"};'"n"} -->
   "firstn"[]{'"n";'"L"} <--> '"L"

interactive_rw nuprl_firstn_map   :
   ('"f" in "fun"[]{"top"[]{};""."top"[]{}}) -->
   ('"n" in "nat"[]{}) -->
   ('"l" in "list"[]{"top"[]{}}) -->
   "firstn"[]{'"n";"map"[]{'"f";'"l"}} <--> "map"[]{'"f";"firstn"[]{'"n";'"l"}}

interactive_rw nuprl_firstn_upto   :
   ('"n" in "nat"[]{}) -->
   ('"m" in "nat"[]{}) -->
   "firstn"[]{'"n";"upto"[]{'"m"}} <--> "ifthenelse"[]{"le_bool"[]{'"n";'"m"};"upto"[]{'"n"};"upto"[]{'"m"}}

interactive nuprl_map_is_append  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L1" in "list"[]{'"B"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"B"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"B"};"map"[]{'"f";'"L"};"append"[]{'"L1";'"L2"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{"list"[]{'"B"};"map"[]{'"f";"firstn"[]{"length"[]{'"L1"};'"L"}};'"L1"};"equal"[]{"list"[]{'"B"};"map"[]{'"f";"nth_tl"[]{"length"[]{'"L1"};'"L"}};'"L2"}}} }

interactive nuprl_map_is_cons  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{'"B"} }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"B"};"map"[]{'"f";'"L"};"cons"[]{'"b";'"L2"}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"equal"[]{'"B";('"f" "hd"[]{'"L"});'"b"};"equal"[]{"list"[]{'"B"};"map"[]{'"f";"tl"[]{'"L"}};'"L2"}}} }

interactive nuprl_map__zip   :
   sequent { <H> >- "!placeholder"[]{} }

define unfold_concat : "concat"[]{'"ll"} <-->
      "reduce"[]{"lambda"[]{"l"."lambda"[]{"l'"."append"[]{'"l";'"l'"}}};"nil"[]{};'"ll"}


interactive nuprl_concat_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll" in "list"[]{"list"[]{'"T"}} }  -->
   sequent { <H> >- ("concat"[]{'"ll"} in "list"[]{'"T"}) }

interactive_rw nuprl_concat_append   :
   ('"ll1" in "list"[]{"list"[]{"top"[]{}}}) -->
   ('"ll2" in "list"[]{"list"[]{"top"[]{}}}) -->
   "concat"[]{"append"[]{'"ll1";'"ll2"}} <--> "append"[]{"concat"[]{'"ll1"};"concat"[]{'"ll2"}}

interactive_rw nuprl_concat__cons   :
   ('"l" in "list"[]{"top"[]{}}) -->
   ('"ll" in "list"[]{"list"[]{"top"[]{}}}) -->
   "concat"[]{"cons"[]{'"l";'"ll"}} <--> "append"[]{'"l";"concat"[]{'"ll"}}

interactive_rw nuprl_concat__nil   :
   "concat"[]{"nil"[]{}} <--> "nil"[]{}

interactive_rw nuprl_map__concat   :
   ('"f" in "fun"[]{"top"[]{};""."top"[]{}}) -->
   ('"L" in "list"[]{"list"[]{"top"[]{}}}) -->
   "map"[]{'"f";"concat"[]{'"L"}} <--> "concat"[]{"map"[]{"lambda"[]{"l"."map"[]{'"f";'"l"}};'"L"}}

interactive_rw nuprl_filter__concat  '"T"  :
   "type"{'"T"} -->
   ('"P" in "fun"[]{'"T";""."bool"[]{}}) -->
   ('"L" in "list"[]{"list"[]{'"T"}}) -->
   "filter"[]{'"P";"concat"[]{'"L"}} <--> "concat"[]{"map"[]{"lambda"[]{"l"."filter"[]{'"P";'"l"}};'"L"}}

interactive nuprl_select_concat   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll" in "list"[]{"list"[]{'"T"}} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"length"[]{"concat"[]{'"ll"}}} }  -->
   sequent { <H> >- "exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"ll"}};"m"."cand"[]{"le"[]{"length"[]{"concat"[]{"firstn"[]{'"m";'"ll"}}};'"n"};"cand"[]{"lt"[]{"sub"[]{'"n";"length"[]{"concat"[]{"firstn"[]{'"m";'"ll"}}}};"length"[]{"select"[]{'"m";'"ll"}}};"equal"[]{'"T";"select"[]{'"n";"concat"[]{'"ll"}};"select"[]{"sub"[]{'"n";"length"[]{"concat"[]{"firstn"[]{'"m";'"ll"}}}};"select"[]{'"m";'"ll"}}}}}} }

interactive nuprl_member__concat   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll" in "list"[]{"list"[]{'"T"}} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"concat"[]{'"ll"};'"T"};"exists"[]{"list"[]{'"T"};"l"."and"[]{"mem"[]{'"l";'"ll";"list"[]{'"T"}};"mem"[]{'"x";'"l";'"T"}}}} }

interactive nuprl_l_member_decomp   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";'"l";'"T"};"exists"[]{"list"[]{'"T"};"l1"."exists"[]{"list"[]{'"T"};"l2"."equal"[]{"list"[]{'"T"};'"l";"append"[]{'"l1";"append"[]{"cons"[]{'"x";"nil"[]{}};'"l2"}}}}}} }

interactive nuprl_concat__decomp   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll" in "list"[]{"list"[]{'"T"}} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"concat"[]{'"ll"};'"T"};"exists"[]{"list"[]{"list"[]{'"T"}};"ll1"."exists"[]{"list"[]{"list"[]{'"T"}};"ll2"."exists"[]{"list"[]{'"T"};"l1"."exists"[]{"list"[]{'"T"};"l2"."and"[]{"equal"[]{"list"[]{'"T"};"concat"[]{'"ll"};"append"[]{"concat"[]{'"ll1"};"append"[]{"append"[]{'"l1";"append"[]{"cons"[]{'"x";"nil"[]{}};'"l2"}};"concat"[]{'"ll2"}}}};"equal"[]{"list"[]{"list"[]{'"T"}};'"ll";"append"[]{'"ll1";"append"[]{"cons"[]{"append"[]{'"l1";"append"[]{"cons"[]{'"x";"nil"[]{}};'"l2"}};"nil"[]{}};'"ll2"}}}}}}}}} }

interactive nuprl_last__concat   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll" in "list"[]{"list"[]{'"T"}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"T"};"concat"[]{'"ll"};"nil"[]{}}} }  -->
   sequent { <H> >- "exists"[]{"list"[]{"list"[]{'"T"}};"ll1"."exists"[]{"list"[]{'"T"};"l1"."and"[]{"equal"[]{"list"[]{'"T"};"concat"[]{'"ll"};"append"[]{"concat"[]{'"ll1"};"append"[]{'"l1";"cons"[]{"last"[]{"concat"[]{'"ll"}};"nil"[]{}}}}};"iseg"[]{"list"[]{'"T"};"append"[]{'"ll1";"cons"[]{"append"[]{'"l1";"cons"[]{"last"[]{"concat"[]{'"ll"}};"nil"[]{}}};"nil"[]{}}};'"ll"}}}} }

interactive nuprl_concat_iseg   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"ll1" in "list"[]{"list"[]{'"T"}} }  -->
   [wf] sequent { <H> >- '"ll2" in "list"[]{"list"[]{'"T"}} }  -->
   sequent { <H> >- "iseg"[]{"list"[]{'"T"};'"ll1";'"ll2"} }  -->
   sequent { <H> >- "iseg"[]{'"T";"concat"[]{'"ll1"};"concat"[]{'"ll2"}} }

interactive nuprl_concat_map_upto   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "nat"[]{} >- '"f" '"x" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"t" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"t'" in "nat"[]{} }  -->
   sequent { <H> >- "lt"[]{'"t";'"t'"} }  -->
   sequent { <H> >- "iseg"[]{'"T";"append"[]{"concat"[]{"map"[]{'"f";"upto"[]{'"t"}}};('"f" '"t")};"concat"[]{"map"[]{'"f";"upto"[]{'"t'"}}}} }

define unfold_mapl : "mapl"[]{'"f";'"l"} <-->
      "map"[]{'"f";'"l"}


interactive nuprl_mapl_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": "set"[]{'"A";"a"."mem"[]{'"a";'"L";'"A"}} >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("mapl"[]{'"f";'"L"} in "list"[]{'"B"}) }

interactive nuprl_member__mapl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"y" in '"T'" }  -->
   [wf] sequent { <H>;"x": "set"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}} >- '"f" '"x" in '"T'" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"y";"mapl"[]{'"f";'"L"};'"T'"};"exists"[]{'"T";"a"."cand"[]{"mem"[]{'"a";'"L";'"T"};"equal"[]{'"T'";'"y";('"f" '"a")}}}} }

interactive nuprl_pairwise__mapl  '"T" '"T'" '"L" '"f" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- "type"{'"T'" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H>;"x": "set"[]{'"T";"x"."mem"[]{'"x";'"L";'"T"}} >- '"f" '"x" in '"T'" }  -->
   [wf] sequent { <H>;"x": '"T'";"x1": '"T'" >- "type"{'"P"['"x";'"x1"] } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T" ; "mem"[]{'"x";'"L";'"T"} ; "mem"[]{'"y";'"L";'"T"}  >- '"P"[('"f" '"x");('"f" '"y")] }  -->
   sequent { <H> >- "pairwise"[]{"x", "y".'"P"['"x";'"y"];"mapl"[]{'"f";'"L"}} }

define unfold_CV : "CV"[]{'"F"} <-->
      ("ycomb"[]{} "lambda"[]{"CV"."lambda"[]{"t".(('"F" '"t") '"CV")}})


interactive nuprl_CV_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"t": "nat"[]{};"x": "fun"[]{"int_seg"[]{"number"[0:n]{};'"t"};"".'"A"} >- '"F" '"t" '"x" in '"A" }  -->
   sequent { <H> >- ("CV"[]{'"F"} in "fun"[]{"nat"[]{};"".'"A"}) }

interactive_rw nuprl_CV_property   :
   ("CV"[]{'"F"} '"t") <--> (('"F" '"t") "CV"[]{'"F"})


(**** display forms ****)


dform nuprl_imax__list_df : except_mode[src] :: "imax-list"[]{'"L"} =
   `"imax-list(" slot{'"L"} `")"


dform nuprl_l_interval_df : except_mode[src] :: "l_interval"[]{'"l";'"i";'"j"} =
   `"l_interval(" slot{'"l"} `";" slot{'"i"} `";" slot{'"j"} `")"


dform nuprl_pairwise_df : except_mode[src] :: "pairwise"[]{"x", "y".'"P";'"L"} =
   `"(" forall `"" slot{'"x"} `"," slot{'"y"} `"" member `"" slot{'"L"} `"." slot{'"P"} `")"


dform nuprl_inv__rel_df : except_mode[src] :: "inv-rel"[]{'"A";'"B";'"f";'"finv"} =
   `"inv-rel(" slot{'"A"} `";" slot{'"B"} `";" slot{'"f"} `";" slot{'"finv"} `")"


dform nuprl_dectt_df : except_mode[src] :: "dectt"[]{'"d"} =
   `"dectt(" slot{'"d"} `")"


dform nuprl_finite__type_df : except_mode[src] :: "finite-type"[]{'"T"} =
   `"finite-type(" slot{'"T"} `")"


dform nuprl_mu_df : except_mode[src] :: "mu"[]{'"f"} =
   `"mu(" slot{'"f"} `")"


dform nuprl_upto_df : except_mode[src] :: "upto"[]{'"n"} =
   `"upto(" slot{'"n"} `")"


dform nuprl_concat_df : except_mode[src] :: "concat"[]{'"ll"} =
   `"concat(" slot{'"ll"} `")"


dform nuprl_mapl_df : except_mode[src] :: "mapl"[]{'"f";'"l"} =
   `"mapl(" slot{'"f"} `";" slot{'"l"} `")"


dform nuprl_CV_df : except_mode[src] :: "CV"[]{'"F"} =
   `"CV(" slot{'"F"} `")"


