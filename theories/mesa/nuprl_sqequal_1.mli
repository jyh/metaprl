extends Ma_union


define unfold_sq_type : "sq_type"[]{'"T"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"equal"[]{'"T";'"x";'"y"};"guard"[]{"rewrite"[]{'"x";'"y"}}}}}


