extends Ma_fun_1


define unfold_fincr : "fincr"[]{} <-->
      "rfun"[]{"nat"[]{};"f", "i"."ifthenelse"[]{"beq_int"[]{'"i";"number"[0:n]{}};"int"[]{};"int_upper"[]{('"f" "sub"[]{'"i";"number"[1:n]{}})}}}


