extends Ma_once_object_directory


define unfold_send__once : "send-once"[]{'"loc";'"T";'"A";'"a";'"f";'"tg";'"l";'"x"} <-->
      "cons"[]{"ma-join-list"[]{"once"[]{'"loc";'"a";"lsrc"[]{'"l"}}};"cons"[]{"ifthenelse"[]{"eq_id"[]{'"loc";"lsrc"[]{'"l"}};"ma-single-sends1"[]{'"A";"unit"[]{};'"T";'"x";"locl"[]{'"a"};'"l";'"tg";"lambda"[]{"a"."lambda"[]{"b"."cons"[]{('"f" '"a");"nil"[]{}}}}};"ma-empty"[]{}};"nil"[]{}}}


