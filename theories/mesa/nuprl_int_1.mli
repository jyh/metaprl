extends Ma_well_fnd


define unfold_lelt : "lelt"[]{'"i";'"j";'"k"} <-->
      "and"[]{"le"[]{'"i";'"j"};"lt"[]{'"j";'"k"}}


define unfold_lele : "lele"[]{'"i";'"j";'"k"} <-->
      "and"[]{"le"[]{'"i";'"j"};"le"[]{'"j";'"k"}}


define unfold_nat_plus : "nat_plus"[]{} <-->
      "set"[]{"int"[]{};"i"."lt"[]{"number"[0:n]{};'"i"}}


define unfold_int_nzero : "int_nzero"[]{} <-->
      "set"[]{"int"[]{};"i"."nequal"[]{"int"[]{};'"i";"number"[0:n]{}}}


define unfold_int_upper : "int_upper"[]{'"i"} <-->
      "set"[]{"int"[]{};"j"."le"[]{'"i";'"j"}}


define unfold_int_lower : "int_lower"[]{'"i"} <-->
      "set"[]{"int"[]{};"j"."le"[]{'"j";'"i"}}


define unfold_int_seg : "int_seg"[]{'"i";'"j"} <-->
      "set"[]{"int"[]{};"k"."lelt"[]{'"i";'"k";'"j"}}


define unfold_int_iseg : "int_iseg"[]{'"i";'"j"} <-->
      "set"[]{"int"[]{};"k"."and"[]{"le"[]{'"i";'"k"};"le"[]{'"k";'"j"}}}


define unfold_suptype : "suptype"[]{'"S";'"T"} <-->
      "subtype"[]{'"T";'"S"}


