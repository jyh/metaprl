extends Ma_rfunction_1


define unfold_refl : "refl"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a".'"E"['"a";'"a"]}


define unfold_sym : "sym"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."all"[]{'"T";"b"."implies"[]{'"E"['"a";'"b"];'"E"['"b";'"a"]}}}


define unfold_trans : "trans"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."all"[]{'"T";"b"."all"[]{'"T";"c"."implies"[]{'"E"['"a";'"b"];"implies"[]{'"E"['"b";'"c"];'"E"['"a";'"c"]}}}}}


define unfold_equiv_rel : "equiv_rel"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"E"['"x";'"y"]};"and"[]{"sym"[]{'"T";"x", "y".'"E"['"x";'"y"]};"trans"[]{'"T";"x", "y".'"E"['"x";'"y"]}}}


define unfold_preorder : "preorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]};"trans"[]{'"T";"x", "y".'"R"['"x";'"y"]}}


define unfold_symmetrize : "symmetrize"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} <-->
      "and"[]{'"R"['"a";'"b"];'"R"['"b";'"a"]}


define unfold_eqfun_p : "eqfun_p"[]{'"T";'"eq"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."iff"[]{"assert"[]{"infix_ap"[]{'"eq";'"x";'"y"}};"equal"[]{'"T";'"x";'"y"}}}}


define unfold_anti_sym : "anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{'"R"['"x";'"y"];"implies"[]{'"R"['"y";'"x"];"equal"[]{'"T";'"x";'"y"}}}}}


define unfold_st_anti_sym : "st_anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."not"[]{"and"[]{'"R"['"x";'"y"];'"R"['"y";'"x"]}}}}


define unfold_strict_part : "strict_part"[]{"x", "y".'"R"['"x";'"y"];'"a";'"b"} <-->
      "and"[]{'"R"['"a";'"b"];"not"[]{'"R"['"b";'"a"]}}


define unfold_connex : "connex"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."or"[]{'"R"['"x";'"y"];'"R"['"y";'"x"]}}}


define unfold_order : "order"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"refl"[]{'"T";"x", "y".'"R"['"x";'"y"]};"and"[]{"trans"[]{'"T";"x", "y".'"R"['"x";'"y"]};"anti_sym"[]{'"T";"x", "y".'"R"['"x";'"y"]}}}


define unfold_linorder : "linorder"[]{'"T";"x", "y".'"R"['"x";'"y"]} <-->
      "and"[]{"order"[]{'"T";"x", "y".'"R"['"x";'"y"]};"connex"[]{'"T";"x", "y".'"R"['"x";'"y"]}}


define unfold_irrefl : "irrefl"[]{'"T";"x", "y".'"E"['"x";'"y"]} <-->
      "all"[]{'"T";"a"."not"[]{'"E"['"a";'"a"]}}


