extends Ma_int_2

open Dtactic


interactive nuprl_cons_neq_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"h" in '"T" }  -->
   [wf] sequent { <H> >- '"t" in "list"[]{'"T"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"T"};"cons"[]{'"h";'"t"};"nil"[]{}}} }

define unfold_null : "is_nil"[]{'"as"} <-->
      "list_ind"[]{'"as";"btrue"[]{};"a", "as'", ""."bfalse"[]{}}


interactive nuprl_null_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("is_nil"[]{'"as"} in "bool"[]{}) }

interactive nuprl_null_wf2 {| intro[] |}   :
   sequent { <H> >- ("is_nil"[]{"nil"[]{}} in "bool"[]{}) }

interactive nuprl_assert_of_null   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"is_nil"[]{'"as"}};"equal"[]{"list"[]{'"T"};'"as";"nil"[]{}}} }

define unfold_append : "append"[]{'"as";'"bs"} <-->
      (("ycomb"[]{} "lambda"[]{"append"."lambda"[]{"as"."list_ind"[]{'"as";'"bs";"a", "as'", ""."cons"[]{'"a";('"append" '"as'")}}}}) '"as")


interactive nuprl_append_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("append"[]{'"as";'"bs"} in "list"[]{'"T"}) }

interactive nuprl_comb_for_append_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"as"."lambda"[]{"bs"."lambda"[]{"z"."append"[]{'"as";'"bs"}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"as"."fun"[]{"list"[]{'"T"};"bs"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"T"}}}}}) }

interactive nuprl_append_assoc   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"cs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"append"[]{"append"[]{'"as";'"bs"};'"cs"};"append"[]{'"as";"append"[]{'"bs";'"cs"}}} }

interactive nuprl_append_back_nil   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"append"[]{'"as";"nil"[]{}};'"as"} }

define unfold_length : "length"[]{'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"length"."lambda"[]{"as"."list_ind"[]{'"as";"number"[0:n]{};"a", "as'", ""."add"[]{('"length" '"as'");"number"[1:n]{}}}}}) '"as")


interactive nuprl_length_wf1 {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("length"[]{'"l"} in "int"[]{}) }

interactive nuprl_comb_for_length_wf1   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"l"."lambda"[]{"z"."length"[]{'"l"}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"list"[]{'"A"};"l"."fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}}}) }

interactive nuprl_length_wf2 {| intro[] |}   :
   sequent { <H> >- ("length"[]{"nil"[]{}} in "int"[]{}) }

interactive nuprl_comb_for_length_wf2   :
   sequent { <H> >- ("lambda"[]{"z"."length"[]{"nil"[]{}}} in "fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}) }

interactive nuprl_length_cons  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"cons"[]{'"a";'"as"}};"add"[]{"length"[]{'"as"};"number"[1:n]{}}} }

interactive nuprl_length_nil   :
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"nil"[]{}};"number"[0:n]{}} }

interactive nuprl_non_neg_length  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- "ge"[]{"length"[]{'"l"};"number"[0:n]{}} }

interactive nuprl_pos_length  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"list"[]{'"A"};'"l";"nil"[]{}}} }  -->
   sequent { <H> >- "ge"[]{"length"[]{'"l"};"number"[1:n]{}} }

interactive nuprl_length_append  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"append"[]{'"as";'"bs"}};"add"[]{"length"[]{'"as"};"length"[]{'"bs"}}} }

interactive nuprl_length_of_not_nil   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "iff"[]{"not"[]{"equal"[]{"list"[]{'"A"};'"as";"nil"[]{}}};"ge"[]{"length"[]{'"as"};"number"[1:n]{}}} }

interactive nuprl_length_of_null_list  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};'"as";"nil"[]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"as"};"number"[0:n]{}} }

define unfold_map : "map"[]{'"f";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"map"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."cons"[]{('"f" '"a");('"map" '"as'")}}}}) '"as")


interactive nuprl_map_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("map"[]{'"f";'"l"} in "list"[]{'"B"}) }

interactive nuprl_comb_for_map_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"f"."lambda"[]{"l"."lambda"[]{"z"."map"[]{'"f";'"l"}}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"univ"[level:l]{};"B"."fun"[]{"fun"[]{'"A";"".'"B"};"f"."fun"[]{"list"[]{'"A"};"l"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"B"}}}}}}) }

interactive nuprl_map_length  '"B" '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"map"[]{'"f";'"as"}};"length"[]{'"as"}} }

interactive nuprl_map_map  '"B" '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H>;"x": '"B" >- '"g" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"C"};"map"[]{'"g";"map"[]{'"f";'"as"}};"map"[]{"compose"[]{'"g";'"f"};'"as"}} }

interactive nuprl_map_append  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"as'" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"B"};"map"[]{'"f";"append"[]{'"as";'"as'"}};"append"[]{"map"[]{'"f";'"as"};"map"[]{'"f";'"as'"}}} }

interactive nuprl_map_id   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"map"[]{"tidentity"[]{'"A"};'"as"};'"as"} }

define unfold_hd : "hd"[]{'"l"} <-->
      "list_ind"[]{'"l";"token"["?":t]{};"h", "t", "v".'"h"}


define unfold_tl : "tl"[]{'"l"} <-->
      "list_ind"[]{'"l";"nil"[]{};"h", "t", "v".'"t"}


interactive nuprl_hd_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- "ge"[]{"length"[]{'"l"};"number"[1:n]{}} }  -->
   sequent { <H> >- ("hd"[]{'"l"} in '"A") }

interactive nuprl_tl_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("tl"[]{'"l"} in "list"[]{'"A"}) }

interactive nuprl_length_tl  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- "ge"[]{"length"[]{'"l"};"number"[1:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"tl"[]{'"l"}};"sub"[]{"length"[]{'"l"};"number"[1:n]{}}} }

define unfold_nth_tl : "nth_tl"[]{'"n";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"nth_tl"."lambda"[]{"n"."lambda"[]{"as"."ifthenelse"[]{"le_bool"[]{'"n";"number"[0:n]{}};'"as";(('"nth_tl" "sub"[]{'"n";"number"[1:n]{}}) "tl"[]{'"as"})}}}}) '"n") '"as")


interactive nuprl_nth_tl_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- ("nth_tl"[]{'"i";'"as"} in "list"[]{'"A"}) }

interactive nuprl_length_nth_tl  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"nth_tl"[]{'"n";'"as"}};"sub"[]{"length"[]{'"as"};'"n"}} }

define unfold_reverse : "reverse"[]{'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"reverse"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."append"[]{('"reverse" '"as'");"cons"[]{'"a";"nil"[]{}}}}}}) '"as")


interactive nuprl_reverse_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("reverse"[]{'"as"} in "list"[]{'"T"}) }

interactive nuprl_reverse_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"reverse"[]{"append"[]{'"as";'"bs"}};"append"[]{"reverse"[]{'"bs"};"reverse"[]{'"as"}}} }

define unfold_firstn : "firstn"[]{'"n";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"firstn"."lambda"[]{"n"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};'"n"};"cons"[]{'"a";(('"firstn" "sub"[]{'"n";"number"[1:n]{}}) '"as'")};"nil"[]{}}}}}}) '"n") '"as")


interactive nuprl_firstn_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("firstn"[]{'"n";'"as"} in "list"[]{'"A"}) }

interactive nuprl_comb_for_firstn_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"as"."lambda"[]{"n"."lambda"[]{"z"."firstn"[]{'"n";'"as"}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"list"[]{'"A"};"as"."fun"[]{"int"[]{};"n"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"A"}}}}}) }

interactive nuprl_length_firstn  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"firstn"[]{'"n";'"as"}};'"n"} }

define unfold_segment : "segment"[]{'"as";'"m";'"n"} <-->
      "firstn"[]{"sub"[]{'"n";'"m"};"nth_tl"[]{'"m";'"as"}}


interactive nuprl_segment_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"m" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("segment"[]{'"as";'"m";'"n"} in "list"[]{'"T"}) }

interactive nuprl_comb_for_segment_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"as"."lambda"[]{"m"."lambda"[]{"n"."lambda"[]{"z"."segment"[]{'"as";'"m";'"n"}}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"list"[]{'"T"};"as"."fun"[]{"int"[]{};"m"."fun"[]{"int"[]{};"n"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"T"}}}}}}) }

interactive nuprl_length_segment  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   [wf] sequent { <H> >- '"j" in "int_iseg"[]{'"i";"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{"segment"[]{'"as";'"i";'"j"}};"sub"[]{'"j";'"i"}} }

interactive nuprl_eq_cons_imp_eq_tls  '"b" '"a"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"b" in '"A" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"cons"[]{'"a";'"as"};"cons"[]{'"b";'"bs"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};'"as";'"bs"} }

interactive nuprl_eq_cons_imp_eq_hds  '"bs" '"as"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"b" in '"A" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"A"};"cons"[]{'"a";'"as"};"cons"[]{'"b";'"bs"}} }  -->
   sequent { <H> >- "equal"[]{'"A";'"a";'"b"} }

define unfold_select : "select"[]{'"i";'"l"} <-->
      "hd"[]{"nth_tl"[]{'"i";'"l"}}


interactive nuprl_select_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "lt"[]{'"n";"length"[]{'"l"}} }  -->
   sequent { <H> >- ("select"[]{'"n";'"l"} in '"A") }

interactive nuprl_comb_for_select_wf   :
   sequent { <H> >- ("lambda"[]{"A"."lambda"[]{"l"."lambda"[]{"n"."lambda"[]{"z"."select"[]{'"n";'"l"}}}}} in "fun"[]{"univ"[level:l]{};"A"."fun"[]{"list"[]{'"A"};"l"."fun"[]{"int"[]{};"n"."fun"[]{"squash"[]{"and"[]{"le"[]{"number"[0:n]{};'"n"};"lt"[]{'"n";"length"[]{'"l"}}}};"".'"A"}}}}) }

interactive nuprl_select_cons_hd   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i";"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"cons"[]{'"a";'"as"}};'"a"} }

interactive nuprl_select_cons_tl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};'"i"} }  -->
   sequent { <H> >- "le"[]{'"i";"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"cons"[]{'"a";'"as"}};"select"[]{"sub"[]{'"i";"number"[1:n]{}};'"as"}} }

interactive nuprl_select_append_back   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"length"[]{'"as"};"add"[]{"length"[]{'"as"};"length"[]{'"bs"}}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"append"[]{'"as";'"bs"}};"select"[]{"sub"[]{'"i";"length"[]{'"as"}};'"bs"}} }

interactive nuprl_select_append_front   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"append"[]{'"as";'"bs"}};"select"[]{'"i";'"as"}} }

interactive nuprl_select_append   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"bs" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"add"[]{"length"[]{'"as"};"length"[]{'"bs"}}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"append"[]{'"as";'"bs"}};"ifthenelse"[]{"lt_bool"[]{'"i";"length"[]{'"as"}};"select"[]{'"i";'"as"};"select"[]{"sub"[]{'"i";"length"[]{'"as"}};'"bs"}}} }

interactive nuprl_select_tl   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"as"};"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{'"A";"select"[]{'"n";"tl"[]{'"as"}};"select"[]{"add"[]{'"n";"number"[1:n]{}};'"as"}} }

interactive nuprl_select_nth_tl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"as"};'"n"}} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"nth_tl"[]{'"n";'"as"}};"select"[]{"add"[]{'"i";'"n"};'"as"}} }

interactive nuprl_select_firstn   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"n" in "int_iseg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"firstn"[]{'"n";'"as"}};"select"[]{'"i";'"as"}} }

define unfold_reject : "reject"[]{'"i";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"reject"."lambda"[]{"i"."lambda"[]{"as"."ifthenelse"[]{"le_bool"[]{'"i";"number"[0:n]{}};"tl"[]{'"as"};"list_ind"[]{'"as";"nil"[]{};"a'", "as'", ""."cons"[]{'"a'";(('"reject" "sub"[]{'"i";"number"[1:n]{}}) '"as'")}}}}}}) '"i") '"as")


interactive nuprl_reject_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("reject"[]{'"n";'"l"} in "list"[]{'"A"}) }

interactive nuprl_reject_cons_hd   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i";"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"reject"[]{'"i";"cons"[]{'"a";'"as"}};'"as"} }

interactive nuprl_reject_cons_tl   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};'"i"} }  -->
   sequent { <H> >- "le"[]{'"i";"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"reject"[]{'"i";"cons"[]{'"a";'"as"}};"cons"[]{'"a";"reject"[]{"sub"[]{'"i";"number"[1:n]{}};'"as"}}} }

interactive nuprl_map_select  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"length"[]{'"as"}} }  -->
   sequent { <H> >- "equal"[]{'"B";"select"[]{'"n";"map"[]{'"f";'"as"}};('"f" "select"[]{'"n";'"as"})} }

define unfold_reduce : "reduce"[]{'"f";'"k";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"reduce"."lambda"[]{"as"."list_ind"[]{'"as";'"k";"a", "as'", "".(('"f" '"a") ('"reduce" '"as'"))}}}) '"as")


interactive nuprl_reduce_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B" >- '"f" '"x" '"x1" in '"B" }  -->
   [wf] sequent { <H> >- '"k" in '"B" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("reduce"[]{'"f";'"k";'"as"} in '"B") }

define unfold_for : "for"[]{'"T";'"op";'"id";'"as";"x".'"f"['"x"]} <-->
      "reduce"[]{'"op";'"id";"map"[]{"tlambda"[]{'"T";"x".'"f"['"x"]};'"as"}}


interactive nuprl_for_wf {| intro[] |}  '"C" '"B" '"A" "lambda"[]{"x".'"g"['"x"]} '"as" '"k" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"B";"x1": '"C" >- '"f" '"x" '"x1" in '"C" }  -->
   [wf] sequent { <H> >- '"k" in '"C" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"g"['"x"] in '"B" }  -->
   sequent { <H> >- ("for"[]{'"A";'"f";'"k";'"as";"x".'"g"['"x"]} in '"C") }

define unfold_mapcons : "mapcons"[]{'"f";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"mapcons"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."cons"[]{(('"f" '"a") '"as'");('"mapcons" '"as'")}}}}) '"as")


interactive nuprl_mapcons_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "list"[]{'"A"} >- '"f" '"x" '"x1" in '"B" }  -->
   [wf] sequent { <H> >- '"l" in "list"[]{'"A"} }  -->
   sequent { <H> >- ("mapcons"[]{'"f";'"l"} in "list"[]{'"B"}) }

define unfold_for_hdtl : "for_hdtl"[]{'"A";'"f";'"k";'"as";"h", "t".'"g"['"h";'"t"]} <-->
      "reduce"[]{'"f";'"k";"mapcons"[]{"lambda"[]{"h"."lambda"[]{"t".'"g"['"h";'"t"]}};'"as"}}


interactive nuprl_for_hdtl_wf {| intro[] |}  '"C" '"B" '"A" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} '"as" '"k" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"B";"x1": '"C" >- '"f" '"x" '"x1" in '"C" }  -->
   [wf] sequent { <H> >- '"k" in '"C" }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "list"[]{'"A"} >- '"g"['"x";'"x1"] in '"B" }  -->
   sequent { <H> >- ("for_hdtl"[]{'"A";'"f";'"k";'"as";"h", "t".'"g"['"h";'"t"]} in '"C") }

define unfold_listify : "listify"[]{'"f";'"m";'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"listify"."lambda"[]{"m"."ifthenelse"[]{"le_bool"[]{'"n";'"m"};"nil"[]{};"cons"[]{('"f" '"m");('"listify" "add"[]{'"m";"number"[1:n]{}})}}}}) '"m")


interactive nuprl_listify_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"m" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{'"m";'"n"} >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- ("listify"[]{'"f";'"m";'"n"} in "list"[]{'"T"}) }

interactive nuprl_comb_for_listify_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"m"."lambda"[]{"n"."lambda"[]{"f"."lambda"[]{"z"."listify"[]{'"f";'"m";'"n"}}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"int"[]{};"m"."fun"[]{"int"[]{};"n"."fun"[]{"fun"[]{"int_seg"[]{'"m";'"n"};"".'"T"};"f"."fun"[]{"squash"[]{"true"[]{}};""."list"[]{'"T"}}}}}}) }

interactive nuprl_listify_length  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"m" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{'"m";'"n"} >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "or"[]{"lt"[]{'"n";'"m"};"equal"[]{"int"[]{};"length"[]{"listify"[]{'"f";'"m";'"n"}};"sub"[]{'"n";'"m"}}} }

interactive nuprl_listify_select_id   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"as" in "list"[]{'"T"} }  -->
   sequent { <H> >- "equal"[]{"list"[]{'"T"};"listify"[]{"tlambda"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"as"}};"i"."select"[]{'"i";'"as"}};"number"[0:n]{};"length"[]{'"as"}};'"as"} }

interactive nuprl_select_listify_id   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{'"i";"listify"[]{'"f";"number"[0:n]{};'"n"}};('"f" '"i")} }

define unfold_list_n : "list_n"[]{'"A";'"n"} <-->
      "set"[]{"list"[]{'"A"};"x"."equal"[]{"int"[]{};"length"[]{'"x"};'"n"}}


interactive nuprl_list_n_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- ("list_n"[]{'"A";'"n"} in "univ"[level:l]{}) }

interactive nuprl_list_n_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "type"{"list_n"[]{'"A";'"n"}} }

interactive nuprl_list_n_properties  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"as" in "list_n"[]{'"A";'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"length"[]{'"as"};'"n"} }

define unfold_mapc : "mapc"[]{'"f"} <-->
      (("ycomb"[]{} "lambda"[]{"mapc"."lambda"[]{"f"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as1", ""."cons"[]{('"f" '"a");(('"mapc" '"f") '"as1")}}}}}) '"f")


interactive nuprl_mapc_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"f" '"x" in '"B" }  -->
   sequent { <H> >- ("mapc"[]{'"f"} in "fun"[]{"list"[]{'"A"};""."list"[]{'"B"}}) }

interactive nuprl_list_append_ind  '"T" "lambda"[]{"x".'"Q"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": "list"[]{'"T"} >- "type"{'"Q"['"x"] } }  -->
   sequent { <H> >- '"Q"["nil"[]{}] }  -->
   sequent { <H>; "x": '"T"  >- '"Q"["cons"[]{'"x";"nil"[]{}}] }  -->
   sequent { <H>; "ys": "list"[]{'"T"} ; "ys'": "list"[]{'"T"} ; '"Q"['"ys"] ; '"Q"['"ys'"]  >- '"Q"["append"[]{'"ys";'"ys'"}] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"list"[]{'"T"};"zs".'"Q"['"zs"]}} }


(**** display forms ****)


dform nuprl_list_case : except_mode[src] :: "list_ind"[]{'"l";'"b";"h", "t", "".'"r"} =
   `"" szone `"" pushm[2:n] `"case " slot{'"l"} `" of " sbreak["",""] `"[] => "
    pushm[0:n] `"" slot{'"b"} `"" popm  `" " sbreak["","| "] `"" slot{'"h"} `"::"
    slot{'"t"} `" => " pushm[0:n] `"" slot{'"r"} `"" popm  `" " popm  `""
    sbreak["",""] `"esac" ezone `""


dform nuprl_null_df : except_mode[src] :: "is_nil"[]{'"as"} =
   `"null(" slot{'"as"} `")"


dform nuprl_append_df : except_mode[src] :: "append"[]{'"P";'"Q"} =
   `"" szone `"" slot{'"P"} `"" sbreak[""," "] `"@ " pushm[0:n] `"" slot{'"Q"} `""
    popm  `"" ezone `""

dform nuprl_append_df : except_mode[src] :: "append"[]{'"P";'"#"} =
   `"" szone `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"@ "
    slot{'"#"} `"" ezone `""

dform nuprl_append_df : except_mode[src] :: "append"[]{'"P";'"Q"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"@ " pushm[0:n] `""
    slot{'"Q"} `"" popm  `""

dform nuprl_append_df : except_mode[src] :: "append"[]{'"P";'"#"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"@ " slot{'"#"} `""


dform nuprl_length_df : except_mode[src] :: "length"[]{'"as"} =
   `"||" slot{'"as"} `"||"


dform nuprl_map_df : except_mode[src] :: "map"[]{'"f";'"as"} =
   `"map(" slot{'"f"} `";" szone sbreak["",""] ezone `"" slot{'"as"} `")"


dform nuprl_hd_df : except_mode[src] :: "hd"[]{'"l"} =
   `"hd(" slot{'"l"} `")"


dform nuprl_tl_df : except_mode[src] :: "tl"[]{'"l"} =
   `"tl(" slot{'"l"} `")"


dform nuprl_nth_tl_df : except_mode[src] :: "nth_tl"[]{'"n";'"as"} =
   `"nth_tl(" slot{'"n"} `";" slot{'"as"} `")"


dform nuprl_reverse_df : except_mode[src] :: "reverse"[]{'"as"} =
   `"rev(" slot{'"as"} `")"


dform nuprl_firstn_df : except_mode[src] :: "firstn"[]{'"n";'"as"} =
   `"firstn(" slot{'"n"} `";" slot{'"as"} `")"


dform nuprl_segment_df : except_mode[src] :: "segment"[]{'"as";'"m";'"n"} =
   `"" slot{'"as"} `"[" slot{'"m"} `".." slot{'"n"} `"" supminus `"]"


dform nuprl_select_df : except_mode[src] :: "select"[]{'"n";'"l"} =
   `"" slot{'"l"} `"[" slot{'"n"} `"]"


dform nuprl_reject_df : except_mode[src] :: "reject"[]{'"i";'"as"} =
   `"" slot{'"as"} `"\[" slot{'"i"} `"]"


dform nuprl_reduce_df : except_mode[src] :: "reduce"[]{'"f";'"k";'"as"} =
   `"reduce(" slot{'"f"} `";" slot{'"k"} `";" slot{'"as"} `")"


dform nuprl_for_df : except_mode[src] :: "for"[]{'"T";'"op";'"id";'"as";"x".'"f"} =
   `"For{" slot{'"T"} `"," slot{'"op"} `"," slot{'"id"} `"} " slot{'"x"} `" " member `" "
    slot{'"as"} `"." szone sbreak["",""] ezone `" " slot{'"f"} `""


dform nuprl_mapcons_df : except_mode[src] :: "mapcons"[]{'"f";'"as"} =
   `"mapcons(" slot{'"f"} `";" slot{'"as"} `")"


dform nuprl_for_hdtl_df : except_mode[src] :: "for_hdtl"[]{'"A";'"f";'"k";'"as";"h", "t".'"g"} =
   `"ForHdTl{" slot{'"A"} `"," slot{'"f"} `"," slot{'"k"} `"} " slot{'"h"} `"::"
    slot{'"t"} `" " member `" " slot{'"as"} `"." szone sbreak["",""] ezone `" "
    slot{'"g"} `""


dform nuprl_listify_df : except_mode[src] :: "listify"[]{'"f";'"m";'"n"} =
   `"listify(" slot{'"f"} `";" slot{'"m"} `";" slot{'"n"} `")"

dform nuprl_listify_df : except_mode[src] :: "listify"[]{'"f";"number"[0:n]{};'"n"} =
   `"(" slot{'"f"} `")[" mathbbN `"" slot{'"n"} `"]"


dform nuprl_list_n_df : except_mode[src] :: "list_n"[]{'"A";'"n"} =
   `"" slot{'"A"} `" List(" slot{'"n"} `")"


dform nuprl_mapc_df : except_mode[src] :: "mapc"[]{'"f"} =
   `"mapc(" slot{'"f"} `")"


