extends Ma_nat_extra


define unfold_mklist : "mklist"[]{'"n";'"f"} <-->
      "primrec"[]{'"n";"nil"[]{};"lambda"[]{"i"."lambda"[]{"l"."append"[]{'"l";"cons"[]{('"f" '"i");"nil"[]{}}}}}}


define unfold_agree_on_common : "agree_on_common"[]{'"T";'"as";'"bs"} <-->
      ((("ycomb"[]{} "lambda"[]{"agree_on_common"."lambda"[]{"as"."lambda"[]{"bs"."list_ind"[]{'"as";"true"[]{};"a", "as'", ""."list_ind"[]{'"bs";"true"[]{};"b", "bs'", ""."or"[]{"and"[]{"not"[]{"mem"[]{'"a";'"bs";'"T"}};(('"agree_on_common" '"as'") '"bs")};"or"[]{"and"[]{"not"[]{"mem"[]{'"b";'"as";'"T"}};(('"agree_on_common" '"as") '"bs'")};"and"[]{"equal"[]{'"T";'"a";'"b"};(('"agree_on_common" '"as'") '"bs'")}}}}}}}}) '"as") '"bs")


define unfold_last : "last"[]{'"L"} <-->
      "select"[]{"sub"[]{"length"[]{'"L"};"number"[1:n]{}};'"L"}


define unfold_reverse_select : "reverse_select"[]{'"l";'"n"} <-->
      "select"[]{"sub"[]{"length"[]{'"l"};"add"[]{'"n";"number"[1:n]{}}};'"l"}


define unfold_l_member__ : "l_member!"[]{'"x";'"l";'"T"} <-->
      "exists"[]{"nat"[]{};"i"."cand"[]{"lt"[]{'"i";"length"[]{'"l"}};"and"[]{"equal"[]{'"T";'"x";"select"[]{'"i";'"l"}};"all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";'"x";"select"[]{'"j";'"l"}};"equal"[]{"nat"[]{};'"j";'"i"}}}}}}}


define unfold_sublist : "sublist"[]{'"T";'"L1";'"L2"} <-->
      "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}}};"f"."and"[]{"increasing"[]{'"f";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f" '"j");'"L2"}}}}}


define unfold_l_before : "l_before"[]{'"x";'"y";'"l";'"T"} <-->
      "sublist"[]{'"T";"cons"[]{'"x";"cons"[]{'"y";"nil"[]{}}};'"l"}


define unfold_strong_before : "strong_before"[]{'"x";'"y";'"l";'"T"} <-->
      "and"[]{"and"[]{"mem"[]{'"x";'"l";'"T"};"mem"[]{'"y";'"l";'"T"}};"all"[]{"nat"[]{};"i"."all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"i";"length"[]{'"l"}};"implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};'"x"};"implies"[]{"equal"[]{'"T";"select"[]{'"j";'"l"};'"y"};"lt"[]{'"i";'"j"}}}}}}}}


define unfold_same_order : "same_order"[]{'"x1";'"y1";'"x2";'"y2";'"L";'"T"} <-->
      "implies"[]{"strong_before"[]{'"x1";'"y1";'"L";'"T"};"implies"[]{"mem"[]{'"x2";'"L";'"T"};"implies"[]{"mem"[]{'"y2";'"L";'"T"};"strong_before"[]{'"x2";'"y2";'"L";'"T"}}}}


define unfold_l_succ : "l_succ"[]{'"x";'"l";'"T";"y".'"P"['"y"]} <-->
      "all"[]{"nat"[]{};"i"."implies"[]{"lt"[]{"add"[]{'"i";"number"[1:n]{}};"length"[]{'"l"}};"implies"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};'"x"};'"P"["select"[]{"add"[]{'"i";"number"[1:n]{}};'"l"}]}}}


define unfold_listp : "listp"[]{'"A"} <-->
      "set"[]{"list"[]{'"A"};"l"."assert"[]{"lt_bool"[]{"number"[0:n]{};"length"[]{'"l"}}}}


define unfold_count : "count"[]{'"P";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"n"."add"[]{"ifthenelse"[]{('"P" '"a");"number"[1:n]{};"number"[0:n]{}};'"n"}}};"number"[0:n]{};'"L"}


define unfold_filter : "filter"[]{'"P";'"l"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"v"."ifthenelse"[]{('"P" '"a");"cons"[]{'"a";'"v"};'"v"}}};"nil"[]{};'"l"}


define unfold_iseg : "iseg"[]{'"T";'"l1";'"l2"} <-->
      "exists"[]{"list"[]{'"T"};"l"."equal"[]{"list"[]{'"T"};'"l2";"append"[]{'"l1";'"l"}}}


define unfold_compat : "compat"[]{'"T";'"l1";'"l2"} <-->
      "or"[]{"iseg"[]{'"T";'"l1";'"l2"};"iseg"[]{'"T";'"l2";'"l1"}}


define unfold_list_accum : "list_accum"[]{"x", "a".'"f"['"x";'"a"];'"y";'"l"} <-->
      ((("ycomb"[]{} "lambda"[]{"list_accum"."lambda"[]{"y"."lambda"[]{"l"."list_ind"[]{'"l";'"y";"b", "l'", "".(('"list_accum" '"f"['"y";'"b"]) '"l'")}}}}) '"y") '"l")


define unfold_zip : "zip"[]{'"as";'"bs"} <-->
      ((("ycomb"[]{} "lambda"[]{"zip"."lambda"[]{"as"."lambda"[]{"bs"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."list_ind"[]{'"bs";"nil"[]{};"b", "bs'", ""."cons"[]{"pair"[]{'"a";'"b"};(('"zip" '"as'") '"bs'")}}}}}}) '"as") '"bs")


define unfold_unzip : "unzip"[]{'"as"} <-->
      "pair"[]{"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"as"};"map"[]{"lambda"[]{"p"."snd"[]{'"p"}};'"as"}}


define unfold_find : "find"[]{"x".'"P"['"x"];'"as";'"d"} <-->
      "list_ind"[]{"filter"[]{"lambda"[]{"x".'"P"['"x"]};'"as"};'"d";"a", "b", "".'"a"}


define unfold_list_all : "list_all"[]{"x".'"P"['"x"];'"l"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"b"."and"[]{'"P"['"a"];'"b"}}};"true"[]{};'"l"}


define unfold_no_repeats : "no_repeats"[]{'"T";'"l"} <-->
      "all"[]{"nat"[]{};"i"."all"[]{"nat"[]{};"j"."implies"[]{"lt"[]{'"i";"length"[]{'"l"}};"implies"[]{"lt"[]{'"j";"length"[]{'"l"}};"implies"[]{"not"[]{"equal"[]{"nat"[]{};'"i";'"j"}};"not"[]{"equal"[]{'"T";"select"[]{'"i";'"l"};"select"[]{'"j";'"l"}}}}}}}}


define unfold_l_disjoint : "l_disjoint"[]{'"T";'"l1";'"l2"} <-->
      "all"[]{'"T";"x"."not"[]{"and"[]{"mem"[]{'"x";'"l1";'"T"};"mem"[]{'"x";'"l2";'"T"}}}}


define unfold_append_rel : "append_rel"[]{'"T";'"L1";'"L2";'"L"} <-->
      "equal"[]{"list"[]{'"T"};"append"[]{'"L1";'"L2"};'"L"}


define unfold_safety : "safety"[]{'"A";"tr".'"P"['"tr"]} <-->
      "all"[]{"list"[]{'"A"};"tr1"."all"[]{"list"[]{'"A"};"tr2"."implies"[]{"iseg"[]{'"A";'"tr1";'"tr2"};"implies"[]{'"P"['"tr2"];'"P"['"tr1"]}}}}


define unfold_l_all : "l_all"[]{'"L";'"T";"x".'"P"['"x"]} <-->
      "all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"L";'"T"};'"P"['"x"]}}


define unfold_l_all2 : "l_all2"[]{'"L";'"T";"x", "y".'"P"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"l_before"[]{'"x";'"y";'"L";'"T"};'"P"['"x";'"y"]}}}


define unfold_l_all_since : "l_all_since"[]{'"L";'"T";'"a";"x".'"P"['"x"]} <-->
      "and"[]{'"P"['"a"];"all"[]{'"T";"b"."implies"[]{"l_before"[]{'"a";'"b";'"L";'"T"};'"P"['"b"]}}}


define unfold_l_exists : "l_exists"[]{'"L";'"T";"x".'"P"['"x"]} <-->
      "exists"[]{'"T";"x"."and"[]{"mem"[]{'"x";'"L";'"T"};'"P"['"x"]}}


define unfold_mapfilter : "mapfilter"[]{'"f";'"P";'"L"} <-->
      "map"[]{'"f";"filter"[]{'"P";'"L"}}


define unfold_split_tail : "split_tail"[]{"x".'"f"['"x"];'"L"} <-->
      (("ycomb"[]{} "lambda"[]{"split_tail"."lambda"[]{"L"."list_ind"[]{'"L";"pair"[]{"nil"[]{};"nil"[]{}};"a", "as", ""."spread"[]{('"split_tail" '"as");"hs", "ftail"."list_ind"[]{'"hs";"ifthenelse"[]{'"f"['"a"];"pair"[]{"nil"[]{};"cons"[]{'"a";'"ftail"}};"pair"[]{"cons"[]{'"a";"nil"[]{}};'"ftail"}};"x", "y", ""."pair"[]{"cons"[]{'"a";'"hs"};'"ftail"}}}}}}) '"L")


define unfold_reduce2 : "reduce2"[]{'"f";'"k";'"i";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"reduce2"."lambda"[]{"i"."lambda"[]{"as"."list_ind"[]{'"as";'"k";"a", "as'", "".((('"f" '"a") '"i") (('"reduce2" "add"[]{'"i";"number"[1:n]{}}) '"as'"))}}}}) '"i") '"as")


define unfold_filter2 : "filter2"[]{'"P";'"L"} <-->
      "reduce2"[]{"lambda"[]{"x"."lambda"[]{"i"."lambda"[]{"l"."ifthenelse"[]{('"P" '"i");"cons"[]{'"x";'"l"};'"l"}}}};"nil"[]{};"number"[0:n]{};'"L"}


define unfold_sublist_occurence : "sublist_occurence"[]{'"T";'"L1";'"L2";'"f"} <-->
      "and"[]{"increasing"[]{'"f";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f" '"j");'"L2"}}}}


define unfold_disjoint_sublists : "disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"} <-->
      "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f1"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}};"f2"."and"[]{"and"[]{"increasing"[]{'"f1";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f1" '"j");'"L"}}}};"and"[]{"and"[]{"increasing"[]{'"f2";"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L2"};"select"[]{('"f2" '"j");'"L"}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j2"."not"[]{"equal"[]{"int"[]{};('"f1" '"j1");('"f2" '"j2")}}}}}}}}


define unfold_interleaving : "interleaving"[]{'"T";'"L1";'"L2";'"L"} <-->
      "and"[]{"equal"[]{"nat"[]{};"length"[]{'"L"};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"disjoint_sublists"[]{'"T";'"L1";'"L2";'"L"}}


define unfold_interleaving_occurence : "interleaving_occurence"[]{'"T";'"L1";'"L2";'"L";'"f1";'"f2"} <-->
      "and"[]{"equal"[]{"nat"[]{};"length"[]{'"L"};"add"[]{"length"[]{'"L1"};"length"[]{'"L2"}}};"and"[]{"and"[]{"increasing"[]{'"f1";"length"[]{'"L1"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L1"};"select"[]{('"f1" '"j");'"L"}}}};"and"[]{"and"[]{"increasing"[]{'"f2";"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j"."equal"[]{'"T";"select"[]{'"j";'"L2"};"select"[]{('"f2" '"j");'"L"}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"j2"."not"[]{"equal"[]{"int"[]{};('"f1" '"j1");('"f2" '"j2")}}}}}}}


define unfold_causal_order : "causal_order"[]{'"L";'"R";'"P";'"Q"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."implies"[]{('"Q" '"i");"exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"j"."and"[]{"and"[]{"le"[]{'"j";'"i"};('"P" '"j")};(('"R" '"j") '"i")}}}}


define unfold_interleaved_family_occurence : "interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"} <-->
      "and"[]{"and"[]{"all"[]{'"I";"i"."and"[]{"increasing"[]{('"f" '"i");"length"[]{('"L" '"i")}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};"j"."equal"[]{'"T";"select"[]{'"j";('"L" '"i")};"select"[]{(('"f" '"i") '"j");'"L2"}}}}};"all"[]{'"I";"i1"."all"[]{'"I";"i2"."implies"[]{"not"[]{"equal"[]{'"I";'"i1";'"i2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i1")}};"j1"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i2")}};"j2"."not"[]{"equal"[]{"int"[]{};(('"f" '"i1") '"j1");(('"f" '"i2") '"j2")}}}}}}}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}};"x"."exists"[]{'"I";"i"."exists"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};"j"."equal"[]{"int"[]{};'"x";(('"f" '"i") '"j")}}}}}


define unfold_interleaved_family : "interleaved_family"[]{'"T";'"I";'"L";'"L2"} <-->
      "exists"[]{"fun"[]{'"I";"i"."fun"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"L" '"i")}};""."int_seg"[]{"number"[0:n]{};"length"[]{'"L2"}}}};"f"."interleaved_family_occurence"[]{'"T";'"I";'"L";'"L2";'"f"}}


define unfold_permute_list : "permute_list"[]{'"L";'"f"} <-->
      "mklist"[]{"length"[]{'"L"};"lambda"[]{"i"."select"[]{('"f" '"i");'"L"}}}


define unfold_swap : "swap"[]{'"L";'"i";'"j"} <-->
      "permute_list"[]{'"L";"flip"[]{'"i";'"j"}}


define unfold_guarded_permutation : "guarded_permutation"[]{'"T";'"P"} <-->
      "rel_star"[]{"list"[]{'"T"};"lambda"[]{"L1"."lambda"[]{"L2"."exists"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{"length"[]{'"L1"};"number"[1:n]{}}};"i"."and"[]{(('"P" '"L1") '"i");"equal"[]{"list"[]{'"T"};'"L2";"swap"[]{'"L1";'"i";"add"[]{'"i";"number"[1:n]{}}}}}}}}}


define unfold_count_index_pairs : "count_index_pairs"[]{'"P";'"L"} <-->
      "double_sum"[]{"length"[]{'"L"};"length"[]{'"L"};"i", "j"."ifthenelse"[]{"band"[]{"lt_bool"[]{'"i";'"j"};((('"P" '"L") '"i") '"j")};"number"[1:n]{};"number"[0:n]{}}}


define unfold_count_pairs : "count_pairs"[]{'"L";"x", "y".'"P"['"x";'"y"]} <-->
      "double_sum"[]{"length"[]{'"L"};"length"[]{'"L"};"i", "j"."ifthenelse"[]{"band"[]{"lt_bool"[]{'"i";'"j"};'"P"["select"[]{'"i";'"L"};"select"[]{'"j";'"L"}]};"number"[1:n]{};"number"[0:n]{}}}


define unfold_first_index : "first_index"[]{'"L";"x".'"P"['"x"]} <-->
      "search"[]{"length"[]{'"L"};"lambda"[]{"i".'"P"["select"[]{'"i";'"L"}]}}


define unfold_agree_on : "agree_on"[]{'"T";"x".'"P"['"x"]} <-->
      "lambda"[]{"L1"."lambda"[]{"L2"."cand"[]{"equal"[]{"int"[]{};"length"[]{'"L1"};"length"[]{'"L2"}};"all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L1"}};"i"."implies"[]{"or"[]{'"P"["select"[]{'"i";'"L1"}];'"P"["select"[]{'"i";'"L2"}]};"equal"[]{'"T";"select"[]{'"i";'"L1"};"select"[]{'"i";'"L2"}}}}}}}


define unfold_strong_safety : "strong_safety"[]{'"T";"tr".'"P"['"tr"]} <-->
      "all"[]{"list"[]{'"T"};"tr1"."all"[]{"list"[]{'"T"};"tr2"."implies"[]{"sublist"[]{'"T";'"tr1";'"tr2"};"implies"[]{'"P"['"tr2"];'"P"['"tr1"]}}}}


define unfold_l_subset : "l_subset"[]{'"T";'"as";'"bs"} <-->
      "all"[]{'"T";"x"."implies"[]{"mem"[]{'"x";'"as";'"T"};"mem"[]{'"x";'"bs";'"T"}}}


define unfold_sublist__ : "sublist*"[]{'"T";'"as";'"bs"} <-->
      "all"[]{"list"[]{'"T"};"cs"."implies"[]{"sublist"[]{'"T";'"cs";'"as"};"implies"[]{"l_subset"[]{'"T";'"cs";'"bs"};"sublist"[]{'"T";'"cs";'"bs"}}}}


