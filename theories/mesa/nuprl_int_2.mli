extends Ma_quot_1


define unfold_absval : "absval"[]{'"i"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"i"};'"i";"minus"[]{'"i"}}


define unfold_pm_equal : "pm_equal"[]{'"i";'"j"} <-->
      "or"[]{"equal"[]{"int"[]{};'"i";'"j"};"equal"[]{"int"[]{};'"i";"minus"[]{'"j"}}}


define unfold_imax : "imax"[]{'"a";'"b"} <-->
      "ifthenelse"[]{"le_bool"[]{'"a";'"b"};'"b";'"a"}


define unfold_imin : "imin"[]{'"a";'"b"} <-->
      "ifthenelse"[]{"le_bool"[]{'"a";'"b"};'"a";'"b"}


define unfold_ndiff : "ndiff"[]{'"a";'"b"} <-->
      "imax"[]{"sub"[]{'"a";'"b"};"number"[0:n]{}}


define unfold_div_nrel : "div_nrel"[]{'"a";'"n";'"q"} <-->
      "lelt"[]{"mul"[]{'"n";'"q"};'"a";"mul"[]{'"n";"add"[]{'"q";"number"[1:n]{}}}}


define unfold_rem_nrel : "rem_nrel"[]{'"a";'"n";'"r"} <-->
      "exists"[]{"nat"[]{};"q"."and"[]{"div_nrel"[]{'"a";'"n";'"q"};"equal"[]{"int"[]{};"add"[]{"mul"[]{'"q";'"n"};'"r"};'"a"}}}


define unfold_modulus : "modulus"[]{'"a";'"n"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"a"};"rem"[]{'"a";'"n"};"ifthenelse"[]{"beq_int"[]{"rem"[]{"minus"[]{'"a"};'"n"};"number"[0:n]{}};"number"[0:n]{};"sub"[]{'"n";"rem"[]{"minus"[]{'"a"};'"n"}}}}


define unfold_div_floor : "div_floor"[]{'"a";'"n"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"a"};"div"[]{'"a";'"n"};"ifthenelse"[]{"beq_int"[]{"rem"[]{"minus"[]{'"a"};'"n"};"number"[0:n]{}};"minus"[]{"div"[]{"minus"[]{'"a"};'"n"}};"add"[]{"minus"[]{"div"[]{"minus"[]{'"a"};'"n"}};"minus"[]{"number"[1:n]{}}}}}


