extends Ma_strong__subtype__stuff


define unfold_imax__list : "imax-list"[]{'"L"} <-->
      "list_accum"[]{"x", "y"."imax"[]{'"x";'"y"};"hd"[]{'"L"};"tl"[]{'"L"}}


define unfold_l_interval : "l_interval"[]{'"l";'"j";'"i"} <-->
      "mklist"[]{"sub"[]{'"i";'"j"};"lambda"[]{"x"."select"[]{"add"[]{'"j";'"x"};'"l"}}}


define unfold_pairwise : "pairwise"[]{"x", "y".'"P"['"x";'"y"];'"L"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{'"L"}};"i"."all"[]{"int_seg"[]{"number"[0:n]{};'"i"};"j".'"P"["select"[]{'"j";'"L"};"select"[]{'"i";'"L"}]}}


define unfold_inv__rel : "inv-rel"[]{'"A";'"B";'"f";'"finv"} <-->
      "and"[]{"all"[]{'"A";"a"."all"[]{'"B";"b"."implies"[]{"equal"[]{"union"[]{'"A";"unit"[]{}};('"finv" '"b");"inl"[]{'"a"}};"equal"[]{'"B";'"b";('"f" '"a")}}}};"all"[]{'"A";"a"."equal"[]{"union"[]{'"A";"unit"[]{}};('"finv" ('"f" '"a"));"inl"[]{'"a"}}}}


define unfold_dectt : "dectt"[]{'"d"} <-->
      "is_inl"[]{'"d"}


define unfold_finite__type : "finite-type"[]{'"T"} <-->
      "exists"[]{"nat"[]{};"n"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"n"};"".'"T"};"f"."surject"[]{"int_seg"[]{"number"[0:n]{};'"n"};'"T";'"f"}}}


define unfold_mu : "mu"[]{'"f"} <-->
      (("ycomb"[]{} "lambda"[]{"mu"."lambda"[]{"f"."ifthenelse"[]{('"f" "number"[0:n]{});"number"[0:n]{};"add"[]{('"mu" "lambda"[]{"x".('"f" "add"[]{'"x";"number"[1:n]{}})});"number"[1:n]{}}}}}) '"f")


define unfold_upto : "upto"[]{'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"upto"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};"nil"[]{};"append"[]{('"upto" "sub"[]{'"n";"number"[1:n]{}});"cons"[]{"sub"[]{'"n";"number"[1:n]{}};"nil"[]{}}}}}}) '"n")


define unfold_concat : "concat"[]{'"ll"} <-->
      "reduce"[]{"lambda"[]{"l"."lambda"[]{"l'"."append"[]{'"l";'"l'"}}};"nil"[]{};'"ll"}


define unfold_mapl : "mapl"[]{'"f";'"l"} <-->
      "map"[]{'"f";'"l"}


define unfold_CV : "CV"[]{'"F"} <-->
      ("ycomb"[]{} "lambda"[]{"CV"."lambda"[]{"t".(('"F" '"t") '"CV")}})


