extends Ma_distributed__systems


define unfold_possible__world : "possible-world"[level:l]{'"D";'"w"} <-->
      "and"[]{"fair-fifo"[]{'"w"};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"x"."subtype"[]{"w-vartype"[]{'"w";'"i";'"x"};"ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"w-action"[]{'"w";'"i"};"a"."implies"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";'"a"}}};"subtype"[]{"w-valtype"[]{'"w";'"i";'"a"};"ma-da"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";'"a"}}}}}};"cand"[]{"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."subtype"[]{(("w-M"[]{'"w"} '"l") '"tg");"ma-da"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};"rcv"[]{'"l";'"tg"}}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"x"."ma-init"[]{"d-m"[]{'"D";'"i"};'"x";"w-s"[]{'"w";'"i";"number"[0:n]{};'"x"}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."implies"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"and"[]{"implies"[]{"assert"[]{"islocal"[]{"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"ma-pre"[]{"d-m"[]{'"D";'"i"};"actof"[]{"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}};"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"and"[]{"all"[]{"Id"[]{};"x"."ma-ef"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"x";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"}}};"and"[]{"all"[]{"IdLnk"[]{};"l"."ma-send"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"l";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};"w-withlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}};'"i"}};"and"[]{"all"[]{"Id"[]{};"x"."implies"[]{"not"[]{"ma-frame"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"x"}};"equal"[]{"ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"};"w-s"[]{'"w";'"i";'"t";'"x"};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"}}}};"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."implies"[]{"not"[]{"ma-sframe"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"l";'"tg"}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-tagged"[]{'"tg";"w-onlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}}};"nil"[]{}}}}}}}}}}}};"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"a"."all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"or"[]{"cand"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t'"}}}};"equal"[]{"Knd"[]{};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t'"}};"locl"[]{'"a"}}};"or"[]{"not"[]{"ma-decla"[]{"d-m"[]{'"D";'"i"};'"a"}};"ma-npre"[]{"d-m"[]{'"D";'"i"};'"a";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t'";'"x"}}}}}}}}}}}}}}}}


define unfold_d__es : "d-es"[level:l]{'"D";'"es"} <-->
      "exists"[]{"world"[level:l]{};"w"."exists"[]{"fair-fifo"[]{'"w"};"p"."and"[]{"possible-world"[level:l]{'"D";'"w"};"equal"[]{"event_system"[level:l]{};'"es";"w-es"[level:l]{'"w";'"p"}}}}}


define unfold_d__realizes : "d-realizes"[level:l]{'"D";"es".'"P"['"es"]} <-->
      "all"[]{"dsys"[level:l]{};"D'"."implies"[]{"d-sub"[level:l]{'"D";'"D'"};"all"[]{"world"[level:l]{};"w"."all"[]{"fair-fifo"[]{'"w"};"p"."implies"[]{"possible-world"[level:l]{'"D'";'"w"};'"P"["w-es"[level:l]{'"w";'"p"}]}}}}}


define unfold_d__realizes2 : "d-realizes2"[level:l]{'"D";"es".'"P"['"es"]} <-->
      "all"[]{"world"[level:l]{};"w"."all"[]{"fair-fifo"[]{'"w"};"p"."implies"[]{"possible-world"[level:l]{'"D";'"w"};'"P"["w-es"[level:l]{'"w";'"p"}]}}}


