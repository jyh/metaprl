extends Ma_distributed__systems

open Dtactic


define unfold_possible__world : "possible-world"[level:l]{'"D";'"w"} <-->
      "and"[]{"fair-fifo"[]{'"w"};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"x"."subtype"[]{"w-vartype"[]{'"w";'"i";'"x"};"ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"w-action"[]{'"w";'"i"};"a"."implies"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";'"a"}}};"subtype"[]{"w-valtype"[]{'"w";'"i";'"a"};"ma-da"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";'"a"}}}}}};"cand"[]{"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."subtype"[]{(("w-M"[]{'"w"} '"l") '"tg");"ma-da"[]{"d-m"[]{'"D";"lsrc"[]{'"l"}};"rcv"[]{'"l";'"tg"}}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"x"."ma-init"[]{"d-m"[]{'"D";'"i"};'"x";"w-s"[]{'"w";'"i";"number"[0:n]{};'"x"}}}};"cand"[]{"all"[]{"Id"[]{};"i"."all"[]{"nat"[]{};"t"."implies"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"and"[]{"implies"[]{"assert"[]{"islocal"[]{"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"ma-pre"[]{"d-m"[]{'"D";'"i"};"actof"[]{"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}};"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}}}};"and"[]{"all"[]{"Id"[]{};"x"."ma-ef"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"x";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"}}};"and"[]{"all"[]{"IdLnk"[]{};"l"."ma-send"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"l";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t";'"x"}};"w-val"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};"w-withlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}};'"i"}};"and"[]{"all"[]{"Id"[]{};"x"."implies"[]{"not"[]{"ma-frame"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"x"}};"equal"[]{"ma-ds"[]{"d-m"[]{'"D";'"i"};'"x"};"w-s"[]{'"w";'"i";'"t";'"x"};"w-s"[]{'"w";'"i";"add"[]{'"t";"number"[1:n]{}};'"x"}}}};"all"[]{"IdLnk"[]{};"l"."all"[]{"Id"[]{};"tg"."implies"[]{"not"[]{"ma-sframe"[]{"d-m"[]{'"D";'"i"};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t"}};'"l";'"tg"}};"equal"[]{"list"[]{"w-Msg"[]{'"w"}};"w-tagged"[]{'"tg";"w-onlnk"[]{'"l";"w-m"[]{'"w";'"i";'"t"}}};"nil"[]{}}}}}}}}}}}};"all"[]{"Id"[]{};"i"."all"[]{"Id"[]{};"a"."all"[]{"nat"[]{};"t"."exists"[]{"nat"[]{};"t'"."and"[]{"le"[]{'"t";'"t'"};"or"[]{"cand"[]{"not"[]{"assert"[]{"w-isnull"[]{'"w";"w-a"[]{'"w";'"i";'"t'"}}}};"equal"[]{"Knd"[]{};"w-kind"[]{'"w";"w-a"[]{'"w";'"i";'"t'"}};"locl"[]{'"a"}}};"or"[]{"not"[]{"ma-decla"[]{"d-m"[]{'"D";'"i"};'"a"}};"ma-npre"[]{"d-m"[]{'"D";'"i"};'"a";"lambda"[]{"x"."w-s"[]{'"w";'"i";'"t'";'"x"}}}}}}}}}}}}}}}}


interactive nuprl_possible__world_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   sequent { <H> >- ("possible-world"[level:l]{'"D";'"w"} in "univ"[level':l]{}) }

interactive nuprl_d__feasible__world   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-feasible"[]{'"D"} }  -->
   sequent { <H> >- "exists"[]{"world"[level:l]{};"w"."possible-world"[level:l]{'"D";'"w"}} }

interactive nuprl_ma__ds__sub univ[level:l]  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "subtype"[]{"ma-ds"[]{'"M2";'"x"};"ma-ds"[]{'"M1";'"x"}} }

interactive nuprl_ma__da__sub univ[level:l]  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   sequent { <H> >- "subtype"[]{"ma-da"[]{'"M2";'"k"};"ma-da"[]{'"M1";'"k"}} }

interactive nuprl_ma__init__sub univ[level:l] '"M2" "lambda"[]{"x".'"V"['"x"]}  :
   [wf] sequent { <H>;"x": "Id"[]{} >- '"V"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H>; "x": "Id"[]{}  >- "subtype"[]{'"V"['"x"];"ma-ds"[]{'"M2";'"x"}} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"v" in '"V"['"x"] }  -->
   sequent { <H> >- "ma-init"[]{'"M2";'"x";'"v"} }  -->
   sequent { <H> >- "ma-init"[]{'"M1";'"x";'"v"} }

interactive nuprl_ma__pre__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M2"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M2";"locl"[]{'"a"}} }  -->
   sequent { <H> >- "ma-pre"[]{'"M2";'"a";'"s";'"v"} }  -->
   sequent { <H> >- "ma-pre"[]{'"M1";'"a";'"s";'"v"} }

interactive nuprl_ma__decla__sub univ[level:l] '"M1"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   sequent { <H> >- "ma-decla"[]{'"M1";'"a"} }  -->
   sequent { <H> >- "ma-decla"[]{'"M2";'"a"} }

interactive nuprl_ma__npre__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M2"} }  -->
   sequent { <H> >- "ma-decla"[]{'"M1";'"a"} }  -->
   sequent { <H> >- "ma-npre"[]{'"M2";'"a";'"s"} }  -->
   sequent { <H> >- "ma-npre"[]{'"M1";'"a";'"s"} }

interactive nuprl_ma__dout__sub univ[level:l]  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "subtype"[]{"ma-dout"[]{'"M1";'"l";'"tg"};"ma-dout"[]{'"M2";'"l";'"tg"}} }

interactive nuprl_ma__ef__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M2"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M2";'"k"} }  -->
   [wf] sequent { <H> >- '"w" in "ma-ds"[]{'"M2";'"x"} }  -->
   sequent { <H> >- "ma-ef"[]{'"M2";'"k";'"x";'"s";'"v";'"w"} }  -->
   sequent { <H> >- "ma-ef"[]{'"M1";'"k";'"x";'"s";'"v";'"w"} }

interactive nuprl_ma__send__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"s" in "ma-st"[]{'"M2"} }  -->
   [wf] sequent { <H> >- '"v" in "ma-da"[]{'"M2";'"k"} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ms" in "list"[]{"prod"[]{"Id"[]{};"tg"."ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"ma-da"[]{'"M2";"rcv"[]{'"l";'"tg"}};"top"[]{}}}} }  -->
   sequent { <H> >- "ma-send"[]{'"M2";'"k";'"l";'"s";'"v";'"ms";'"i"} }  -->
   sequent { <H> >- "ma-send"[]{'"M1";'"k";'"l";'"s";'"v";'"ms";'"i"} }

interactive nuprl_ma__frame__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-frame"[]{'"M2";'"k";'"x"} }  -->
   sequent { <H> >- "ma-frame"[]{'"M1";'"k";'"x"} }

interactive nuprl_ma__sframe__sub univ[level:l] '"M2"  :
   [wf] sequent { <H> >- '"M1" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M2" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M1";'"M2"} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "ma-sframe"[]{'"M2";'"k";'"l";'"tg"} }  -->
   sequent { <H> >- "ma-sframe"[]{'"M1";'"k";'"l";'"tg"} }

interactive nuprl_possible__world__monotonic  '"B"  :
   [wf] sequent { <H> >- '"A" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "dsys"[level:l]{} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"A";'"B"} }  -->
   [wf] sequent { <H> >- '"w" in "world"[level:l]{} }  -->
   sequent { <H> >- "possible-world"[level:l]{'"B";'"w"} }  -->
   sequent { <H> >- "possible-world"[level:l]{'"A";'"w"} }

define unfold_d__es : "d-es"[level:l]{'"D";'"es"} <-->
      "exists"[]{"world"[level:l]{};"w"."exists"[]{"fair-fifo"[]{'"w"};"p"."and"[]{"possible-world"[level:l]{'"D";'"w"};"equal"[]{"event_system"[level:l]{};'"es";"w-es"[level:l]{'"w";'"p"}}}}}


interactive nuprl_d__es_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"E" in "event_system"[level:l]{} }  -->
   sequent { <H> >- ("d-es"[level:l]{'"D";'"E"} in "univ"[level':l]{}) }

define unfold_d__realizes : "d-realizes"[level:l]{'"D";"es".'"P"['"es"]} <-->
      "all"[]{"dsys"[level:l]{};"D'"."implies"[]{"d-sub"[level:l]{'"D";'"D'"};"all"[]{"world"[level:l]{};"w"."all"[]{"fair-fifo"[]{'"w"};"p"."implies"[]{"possible-world"[level:l]{'"D'";'"w"};'"P"["w-es"[level:l]{'"w";'"p"}]}}}}}


interactive nuprl_d__realizes_wf {| intro[] |} univ[level':l] '"D" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"event_system"[level:l]{};"es"."d-es"[level:l]{'"D";'"es"}} >- '"P"['"x"] in "univ"[level':l]{} }  -->
   sequent { <H> >- ("d-realizes"[level:l]{'"D";"es".'"P"['"es"]} in "univ"[i'':l]{}) }




define unfold_d__realizes2 : "d-realizes2"[level:l]{'"D";"es".'"P"['"es"]} <-->
      "all"[]{"world"[level:l]{};"w"."all"[]{"fair-fifo"[]{'"w"};"p"."implies"[]{"possible-world"[level:l]{'"D";'"w"};'"P"["w-es"[level:l]{'"w";'"p"}]}}}


interactive nuprl_d__realizes2_wf {| intro[] |} univ[level':l] '"D" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"event_system"[level:l]{};"es"."d-es"[level:l]{'"D";'"es"}} >- '"P"['"x"] in "univ"[level':l]{} }  -->
   sequent { <H> >- ("d-realizes2"[level:l]{'"D";"es".'"P"['"es"]} in "univ"[i'':l]{}) }

interactive nuprl_d__realizes2__implies__realizes univ[level':l] '"D" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"event_system"[level:l]{};"es"."d-es"[level:l]{'"D";'"es"}} >- '"P"['"x"] in "univ"[level':l]{} }  -->
   sequent { <H> >- "d-realizes2"[level:l]{'"D";"es".'"P"['"es"]} }  -->
   sequent { <H> >- "d-realizes"[level:l]{'"D";"es".'"P"['"es"]} }

interactive nuprl_realizes__monotone__wrt__sub univ[level':l] '"D" "lambda"[]{"x".'"P"['"x"]} '"D'"  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"D'" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"event_system"[level:l]{};"es"."d-es"[level:l]{'"D";'"es"}} >- '"P"['"x"] in "univ"[level':l]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{'"D";"es".'"P"['"es"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"d-sub"[level:l]{'"D";'"D'"};"d-realizes"[level:l]{'"D'";"es".'"P"['"es"]}}} }

interactive nuprl_init__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"T" }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-init"[]{'"i";'"x";'"T";'"v"};"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};"equal"[]{'"T";"es-when"[]{'"es";'"x";'"e"};'"v"}}}}}} }

interactive nuprl_frame__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-frame"[]{'"i";'"L";'"T";'"x"};"es"."cand"[]{"subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};'"T"};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"not"[]{"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}};"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"implies"[]{"not"[]{"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}};"equal"[]{'"T";"es-after"[]{'"es";'"x";'"e"};"es-when"[]{'"es";'"x";'"e"}}}}}}}} }

interactive nuprl_sframe__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-sframe"[]{'"i";'"L";'"l";'"tg"};"es"."all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"not"[]{"assert"[]{"is_nil"[]{"es-tg-sends"[]{'"es";'"l";'"tg";'"e"}}}};"mem"[]{"es-kind"[]{'"es";'"e"};'"L";"Knd"[]{}}}}}} }

interactive nuprl_effect__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": "ma-valtype"[]{'"da";'"k"} >- '"f" '"x" '"x1" in "fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-effect"[]{'"i";'"ds";'"da";'"k";'"x";'"f"};"es"."cand"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"equal"[]{"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}};"es-after"[]{'"es";'"x";'"e"};(('"f" "lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}}) "es-val"[]{'"es";'"e"})}}}}}} }

interactive nuprl_sends__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"};"es"."cand"[]{"and"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"implies"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}}}};"subtype"[]{"set"[]{"es-Msg"[]{'"es"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};'"i"}};"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"top"[]{}}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"equal"[]{"list"[]{"Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"top"[]{}}}}}};"es-sends"[]{'"es";'"l";'"e"};"tagged-messages"[]{'"l";"lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}};"es-val"[]{'"es";'"e"};'"f"}}}}}}} }

interactive nuprl_better__sends__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";'"k"};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}}} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"lsrc"[]{'"l"};'"i"} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-sends"[]{'"i";'"ds";'"da";'"k";'"l";'"f"};"es"."cand"[]{"and"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"assert"[]{"es-isrcv"[]{'"es";'"e"}};"implies"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"};"subtype"[]{"es-valtype"[]{'"es";'"e"};"ma-valtype"[]{'"da";"es-kind"[]{'"es";'"e"}}}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};'"k"};"exists"[]{"list"[]{"set"[]{"es-E"[]{'"es"};"e'"."cand"[]{"assert"[]{"es-isrcv"[]{'"es";'"e'"}};"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e'"};'"l"}}}};"L"."and"[]{"all"[]{"es-E"[]{'"es"};"e'"."iff"[]{"mem"[]{'"e'";'"L";"es-E"[]{'"es"}};"cand"[]{"assert"[]{"es-isrcv"[]{'"es";'"e'"}};"and"[]{"equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e'"};'"l"};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}}}};"and"[]{"all"[]{"es-E"[]{'"es"};"e1"."all"[]{"es-E"[]{'"es"};"e2"."implies"[]{"l_before"[]{'"e1";'"e2";'"L";"es-E"[]{'"es"}};"es-locl"[]{'"es";'"e1";'"e2"}}}};"equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg"."ma-valtype"[]{'"da";"rcv"[]{'"l";'"tg"}}}};"map"[]{"lambda"[]{"e'"."pair"[]{"es-tag"[]{'"es";'"e'"};"es-val"[]{'"es";'"e'"}}};'"L"};"tagged-list-messages"[]{"lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}};"es-val"[]{'"es";'"e"};'"f"}}}}}}}}}} }

interactive nuprl_pre__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-pre"[]{'"i";'"ds";'"a";'"T";'"P"};"es"."cand"[]{"and"[]{"all"[]{"Id"[]{};"x"."subtype"[]{"es-vartype"[]{'"es";'"i";'"x"};"fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};"subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"}}}}};"all"[]{"es-E"[]{'"es"};"e"."implies"[]{"equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"};"and"[]{"implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e"};"locl"[]{'"a"}};(('"P" "lambda"[]{"z"."es-when"[]{'"es";'"z";'"e"}}) "es-val"[]{'"es";'"e"})};"exists"[]{"es-E"[]{'"es"};"e'"."cand"[]{"or"[]{"es-locl"[]{'"es";'"e";'"e'"};"equal"[]{"es-E"[]{'"es"};'"e";'"e'"}};"or"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"locl"[]{'"a"}};"all"[]{'"T";"v"."not"[]{(('"P" "lambda"[]{"z"."es-after"[]{'"es";'"z";'"e'"}}) '"v")}}}}}}}}}} }

interactive nuprl_pre__init__rule   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H>;"x": "ma-state"[]{'"ds"};"x1": '"T" >- '"P" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent { <H>; "x": "Id"[]{} ; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"ds"}}  >- "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}} }  -->
   sequent { <H> >- "d-realizes"[level:l]{"d-single-pre-init"[]{'"i";'"ds";'"init";'"a";'"T";'"P"};"es"."implies"[]{"exists"[]{'"T";"v".(('"P" "lambda"[]{"x"."fpf-cap"[]{'"init";"id-deq"[]{};'"x";"it"[]{}}}) '"v")};"exists"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}}} }


(**** display forms ****)


dform nuprl_possible__world_df : except_mode[src] :: "possible-world"[level:l]{'"D";'"w"} =
   `"PossibleWorld(" slot{'"D"} `";" slot{'"w"} `")"


dform nuprl_d__es_df : except_mode[src] :: "d-es"[level:l]{'"D";'"es"} =
   `"" slot{'"es"} `" is an event system of " slot{'"D"} `""


dform nuprl_d__realizes_df : except_mode[src] :: "d-realizes"[level:l]{'"D";"es".'"P"} =
   `"" slot{'"D"} `" " sbreak["",""] `"realizes " slot{'"es"} `"." pushm[0:n] `""
    slot{'"P"} `"" popm  `""


dform nuprl_d__realizes2_df : except_mode[src] :: "d-realizes2"[level:l]{'"D";"es".'"P"} =
   `"" slot{'"D"} `" realizes2 " slot{'"es"} `"." slot{'"P"} `""


