extends Ma_list_1


define unfold_divides : "divides"[]{'"b";'"a"} <-->
      "exists"[]{"int"[]{};"c"."equal"[]{"int"[]{};'"a";"mul"[]{'"b";'"c"}}}


define unfold_assoced : "assoced"[]{'"a";'"b"} <-->
      "and"[]{"divides"[]{'"a";'"b"};"divides"[]{'"b";'"a"}}


define unfold_gcd_p : "gcd_p"[]{'"a";'"b";'"y"} <-->
      "and"[]{"divides"[]{'"y";'"a"};"and"[]{"divides"[]{'"y";'"b"};"all"[]{"int"[]{};"z"."implies"[]{"and"[]{"divides"[]{'"z";'"a"};"divides"[]{'"z";'"b"}};"divides"[]{'"z";'"y"}}}}}


define unfold_gcd : "gcd"[]{'"a";'"b"} <-->
      ((("ycomb"[]{} "lambda"[]{"gcd"."lambda"[]{"a"."lambda"[]{"b"."ifthenelse"[]{"beq_int"[]{'"b";"number"[0:n]{}};'"a";(('"gcd" '"b") "rem"[]{'"a";'"b"})}}}}) '"a") '"b")


