extends Ma_event__system


define unfold_strong__subtype : "subset"[]{'"A";'"B"} <-->
      "cand"[]{"subtype"[]{'"A";'"B"};"cand"[]{"subtype"[]{"set"[]{'"B";"b"."exists"[]{'"A";"a"."equal"[]{'"B";'"b";'"a"}}};'"A"};"all"[]{'"A";"a1"."all"[]{'"A";"a2"."implies"[]{"equal"[]{'"B";'"a1";'"a2"};"equal"[]{'"A";'"a1";'"a2"}}}}}}


