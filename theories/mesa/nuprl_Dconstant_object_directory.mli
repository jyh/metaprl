extends Ma_event__system__applications


define unfold_Dconstant : "Dconstant"[]{'"loc";'"T";'"c";'"x";'"i"} <-->
      "ifthenelse"[]{"eq_id"[]{'"loc";'"i"};"cons"[]{"ma-single-init"[]{'"x";'"T";'"c"};"cons"[]{"ma-single-frame"[]{"nil"[]{};'"T";'"x"};"nil"[]{}}};"nil"[]{}}


