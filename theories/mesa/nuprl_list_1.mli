extends Ma_int_2


define unfold_null : "is_nil"[]{'"as"} <-->
      "list_ind"[]{'"as";"btrue"[]{};"a", "as'", ""."bfalse"[]{}}


define unfold_append : "append"[]{'"as";'"bs"} <-->
      (("ycomb"[]{} "lambda"[]{"append"."lambda"[]{"as"."list_ind"[]{'"as";'"bs";"a", "as'", ""."cons"[]{'"a";('"append" '"as'")}}}}) '"as")


define unfold_length : "length"[]{'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"length"."lambda"[]{"as"."list_ind"[]{'"as";"number"[0:n]{};"a", "as'", ""."add"[]{('"length" '"as'");"number"[1:n]{}}}}}) '"as")


define unfold_map : "map"[]{'"f";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"map"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."cons"[]{('"f" '"a");('"map" '"as'")}}}}) '"as")


define unfold_hd : "hd"[]{'"l"} <-->
      "list_ind"[]{'"l";"token"["?":t]{};"h", "t", "v".'"h"}


define unfold_tl : "tl"[]{'"l"} <-->
      "list_ind"[]{'"l";"nil"[]{};"h", "t", "v".'"t"}


define unfold_nth_tl : "nth_tl"[]{'"n";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"nth_tl"."lambda"[]{"n"."lambda"[]{"as"."ifthenelse"[]{"le_bool"[]{'"n";"number"[0:n]{}};'"as";(('"nth_tl" "sub"[]{'"n";"number"[1:n]{}}) "tl"[]{'"as"})}}}}) '"n") '"as")


define unfold_reverse : "reverse"[]{'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"reverse"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."append"[]{('"reverse" '"as'");"cons"[]{'"a";"nil"[]{}}}}}}) '"as")


define unfold_firstn : "firstn"[]{'"n";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"firstn"."lambda"[]{"n"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};'"n"};"cons"[]{'"a";(('"firstn" "sub"[]{'"n";"number"[1:n]{}}) '"as'")};"nil"[]{}}}}}}) '"n") '"as")


define unfold_segment : "segment"[]{'"as";'"m";'"n"} <-->
      "firstn"[]{"sub"[]{'"n";'"m"};"nth_tl"[]{'"m";'"as"}}


define unfold_select : "select"[]{'"i";'"l"} <-->
      "hd"[]{"nth_tl"[]{'"i";'"l"}}


define unfold_reject : "reject"[]{'"i";'"as"} <-->
      ((("ycomb"[]{} "lambda"[]{"reject"."lambda"[]{"i"."lambda"[]{"as"."ifthenelse"[]{"le_bool"[]{'"i";"number"[0:n]{}};"tl"[]{'"as"};"list_ind"[]{'"as";"nil"[]{};"a'", "as'", ""."cons"[]{'"a'";(('"reject" "sub"[]{'"i";"number"[1:n]{}}) '"as'")}}}}}}) '"i") '"as")


define unfold_reduce : "reduce"[]{'"f";'"k";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"reduce"."lambda"[]{"as"."list_ind"[]{'"as";'"k";"a", "as'", "".(('"f" '"a") ('"reduce" '"as'"))}}}) '"as")


define unfold_for : "for"[]{'"T";'"op";'"id";'"as";"x".'"f"['"x"]} <-->
      "reduce"[]{'"op";'"id";"map"[]{"tlambda"[]{'"T";"x".'"f"['"x"]};'"as"}}


define unfold_mapcons : "mapcons"[]{'"f";'"as"} <-->
      (("ycomb"[]{} "lambda"[]{"mapcons"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as'", ""."cons"[]{(('"f" '"a") '"as'");('"mapcons" '"as'")}}}}) '"as")


define unfold_for_hdtl : "for_hdtl"[]{'"A";'"f";'"k";'"as";"h", "t".'"g"['"h";'"t"]} <-->
      "reduce"[]{'"f";'"k";"mapcons"[]{"lambda"[]{"h"."lambda"[]{"t".'"g"['"h";'"t"]}};'"as"}}


define unfold_listify : "listify"[]{'"f";'"m";'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"listify"."lambda"[]{"m"."ifthenelse"[]{"le_bool"[]{'"n";'"m"};"nil"[]{};"cons"[]{('"f" '"m");('"listify" "add"[]{'"m";"number"[1:n]{}})}}}}) '"m")


define unfold_list_n : "list_n"[]{'"A";'"n"} <-->
      "set"[]{"list"[]{'"A"};"x"."equal"[]{"int"[]{};"length"[]{'"x"};'"n"}}


define unfold_mapc : "mapc"[]{'"f"} <-->
      (("ycomb"[]{} "lambda"[]{"mapc"."lambda"[]{"f"."lambda"[]{"as"."list_ind"[]{'"as";"nil"[]{};"a", "as1", ""."cons"[]{('"f" '"a");(('"mapc" '"f") '"as1")}}}}}) '"f")


