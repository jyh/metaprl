extends Ma_tree_1


define unfold_primrec : "primrec"[]{'"n";'"b";'"c"} <-->
      (("ycomb"[]{} "lambda"[]{"primrec"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};'"b";(('"c" "sub"[]{'"n";"number"[1:n]{}}) ('"primrec" "sub"[]{'"n";"number"[1:n]{}}))}}}) '"n")


define unfold_nondecreasing : "nondecreasing"[]{'"f";'"k"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};"i"."le"[]{('"f" '"i");('"f" "add"[]{'"i";"number"[1:n]{}})}}


define unfold_fadd : "fadd"[]{'"f";'"g"} <-->
      "lambda"[]{"i"."add"[]{('"f" '"i");('"g" '"i")}}


define unfold_fshift : "fshift"[]{'"f";'"x"} <-->
      "lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"i";"number"[0:n]{}};'"x";('"f" "sub"[]{'"i";"number"[1:n]{}})}}


define unfold_finite : "finite"[]{'"T"} <-->
      "all"[]{"fun"[]{'"T";"".'"T"};"f"."implies"[]{"inject"[]{'"T";'"T";'"f"};"surject"[]{'"T";'"T";'"f"}}}


define unfold_fappend : "fappend"[]{'"f";'"n";'"x"} <-->
      "lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"i";'"n"};'"x";('"f" '"i")}}


define unfold_sum : "sum"[]{'"k";"x".'"f"['"x"]} <-->
      "primrec"[]{'"k";"number"[0:n]{};"lambda"[]{"x"."lambda"[]{"n"."add"[]{'"n";'"f"['"x"]}}}}


define unfold_double_sum : "double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]} <-->
      "sum"[]{'"n";"x"."sum"[]{'"m";"y".'"f"['"x";'"y"]}}


define unfold_rel_exp : "rel_exp"[]{'"T";'"R";'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"rel_exp"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};"lambda"[]{"x"."lambda"[]{"y"."equal"[]{'"T";'"x";'"y"}}};"lambda"[]{"x"."lambda"[]{"y"."exists"[]{'"T";"z"."and"[]{"infix_ap"[]{'"R";'"x";'"z"};"infix_ap"[]{('"rel_exp" "sub"[]{'"n";"number"[1:n]{}});'"z";'"y"}}}}}}}}) '"n")


define unfold_rel_implies : "rel_implies"[]{'"T";'"R1";'"R2"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}


define unfold_preserved_by : "preserved_by"[]{'"T";'"R";'"P"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{('"P" '"x");"implies"[]{"infix_ap"[]{'"R";'"x";'"y"};('"P" '"y")}}}}


define unfold_cond_rel_implies : "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{('"P" '"x");"implies"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}}


define unfold_rel_star : "rel_star"[]{'"T";'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."exists"[]{"nat"[]{};"n"."infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"x";'"y"}}}}


define unfold_rel_inverse : "rel_inverse"[]{'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."infix_ap"[]{'"R";'"y";'"x"}}}


define unfold_rel_or : "rel_or"[]{'"R1";'"R2"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."or"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}


define unfold_as_strong : "as_strong"[]{'"T";'"Q";'"P"} <-->
      "all"[]{'"T";"x"."implies"[]{('"P" '"x");('"Q" '"x")}}


define unfold_fun_exp : "fun_exp"[]{'"f";'"n"} <-->
      "primrec"[]{'"n";"lambda"[]{"x".'"x"};"lambda"[]{"i"."lambda"[]{"g"."compose"[]{'"f";'"g"}}}}


define unfold_flip : "flip"[]{'"i";'"j"} <-->
      "lambda"[]{"x"."ifthenelse"[]{"beq_int"[]{'"x";'"i"};'"j";"ifthenelse"[]{"beq_int"[]{'"x";'"j"};'"i";'"x"}}}


define unfold_search : "search"[]{'"k";'"P"} <-->
      "primrec"[]{'"k";"number"[0:n]{};"lambda"[]{"i"."lambda"[]{"j"."ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};'"j"};'"j";"ifthenelse"[]{('"P" '"i");"add"[]{'"i";"number"[1:n]{}};"number"[0:n]{}}}}}}


define unfold_prop_and : "prop_and"[]{'"P";'"Q"} <-->
      "lambda"[]{"L"."and"[]{('"P" '"L");('"Q" '"L")}}


define unfold_preserved_by2 : "preserved_by2"[]{'"T";'"R";'"P"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."all"[]{'"T";"z"."implies"[]{('"P" '"x");"implies"[]{('"P" '"y");"implies"[]{((('"R" '"x") '"y") '"z");('"P" '"z")}}}}}}


