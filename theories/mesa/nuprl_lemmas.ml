extends Ma_special__theory

open Dtactic


interactive nuprl_member__ite   :
   [wf] sequent { <H> >- '"b" in "bool"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"A" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"B" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "iff"[]{"mem"[]{'"x";"ifthenelse"[]{'"b";'"A";'"B"};'"T"};"or"[]{"and"[]{"assert"[]{'"b"};"mem"[]{'"x";'"A";'"T"}};"and"[]{"not"[]{"assert"[]{'"b"}};"mem"[]{'"x";'"B";'"T"}}}} }

interactive nuprl_bool__inhabited   :
   sequent { <H> >- "bool"[]{} }

interactive nuprl_decidable__exists__finite  '"T" "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P"['"x"] } }  -->
   sequent { <H>; "x": '"T"  >- "decidable"[]{'"P"['"x"]} }  -->
   sequent { <H> >- "finite-type"[]{'"T"} }  -->
   sequent { <H> >- "decidable"[]{"exists"[]{'"T";"x".'"P"['"x"]}} }

interactive nuprl_decidable__ex_unit  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "unit"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "decidable"[]{'"P"["it"[]{}]} }  -->
   sequent { <H> >- "decidable"[]{"exists"[]{"unit"[]{};"x".'"P"['"x"]}} }

interactive_rw nuprl_ite__same   :
   ('"b" in "bool"[]{}) -->
   "ifthenelse"[]{'"b";'"x";'"x"} <--> '"x"

interactive nuprl_ma__component__types   :
   [wf] sequent { <H> >- '"M" in "msga"[level:l]{} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"and"[]{("fst"[]{'"M"} in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}});("fst"[]{"snd"[]{'"M"}} in "fpf"[]{"Knd"[]{};"k"."univ"[level:l]{}})};"and"[]{("fst"[]{"snd"[]{"snd"[]{'"M"}}} in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};'"x";"void"[]{}}});"and"[]{("fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}} in "fpf"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{"fst"[]{'"M"}};""."fun"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};""."univ"[level:l]{}}}});"and"[]{("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}} in "fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{"fst"[]{'"M"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M"}};"fst"[]{'"kx"}};""."fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}}});"and"[]{("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}} in "fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{"fst"[]{'"M"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M"}};"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}}});"and"[]{("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}} in "fpf"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}}});("fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}} in "fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}}})}}}}}}} }

define unfold_effect__type : "effect-type"[]{'"ds";'"ds'";'"da"} <-->
      "fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kx"}};""."fpf-cap"[]{'"ds'";"id-deq"[]{};"snd"[]{'"kx"};"top"[]{}}}}}


interactive nuprl_effect__type_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"ds1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds2" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- ("effect-type"[]{'"ds1";'"ds2";'"da"} in "univ"[level:l]{}) }

interactive nuprl_effect__type_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"ds1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds2" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "type"{"effect-type"[]{'"ds1";'"ds2";'"da"}} }

interactive nuprl_effect__type__subtype univ[level:l]  :
   [wf] sequent { <H> >- '"ds1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds1'" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds2" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"ds2'" in "fpf"[]{"Id"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da'" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds1";'"ds1'"} }  -->
   sequent { <H> >- "fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds2'";'"ds2"} }  -->
   sequent { <H> >- "fpf-sub"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"da'"} }  -->
   sequent { <H> >- "subtype"[]{"effect-type"[]{'"ds1";'"ds2";'"da"};"effect-type"[]{'"ds1'";'"ds2'";'"da'"}} }

interactive nuprl_proper__at__join univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-feasible"[]{'"A"} }  -->
   sequent { <H> >- "ma-feasible"[]{'"B"} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";'"B"} }  -->
   sequent { <H> >- "ma-feasible"[]{"ma-join"[]{'"A";'"B"}} }

interactive nuprl_m__sys__feasible   :
   [wf] sequent { <H> >- '"M" in "msystem"[level:l]{} }  -->
   sequent { <H>; "l": "IdLnk"[]{} ; "tg": "Id"[]{}  >- "subtype"[]{"ma-dout"[]{('"M" "lsrc"[]{'"l"});'"l";'"tg"};"ma-din"[]{('"M" "ldst"[]{'"l"});'"l";'"tg"}} }  -->
   sequent { <H>; "i": "Id"[]{}  >- "finite-type"[]{"set"[]{"IdLnk"[]{};"l"."and"[]{"equal"[]{"Id"[]{};"ldst"[]{'"l"};'"i"};"assert"[]{"ma-sends-on"[]{('"M" "lsrc"[]{'"l"});'"l"}}}}} }  -->
   sequent { <H> >- ('"M" in "set"[]{"dsys"[level:l]{};"D"."d-feasible"[]{'"D"}}) }

interactive nuprl_m__sys__at__feasible univ[level:l]  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- "ma-feasible"[]{'"A"} }  -->
   sequent { <H> >- "d-feasible"[]{"m-sys-at"[]{'"i";'"A"}} }

interactive nuprl_m__sys__at_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   sequent { <H> >- ("m-sys-at"[]{'"i";'"A"} in "fun"[]{"Id"[]{};"i"."msga"[level:l]{}}) }

interactive nuprl_isrcv__implies   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "assert"[]{"isrcv"[]{'"k"}} }  -->
   sequent { <H> >- "equal"[]{"Knd"[]{};'"k";"rcv"[]{"lnk"[]{'"k"};"tagof"[]{'"k"}}} }

interactive nuprl_es__Msg__subtype1 univ[level:l] '"tg" '"l"  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- "subtype"[]{"set"[]{"es-Msg"[]{'"es"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};"lsrc"[]{'"l"}}};"Msg"[]{"lambda"[]{"l'"."lambda"[]{"tg'"."ifthenelse"[]{"band"[]{"eq_lnk"[]{'"l'";'"l"};"eq_id"[]{'"tg'";'"tg"}};'"T";"top"[]{}}}}}} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   sequent { <H> >- "assert"[]{"es-isrcv"[]{'"es";'"e"}} }  -->
   sequent { <H> >- "equal"[]{"IdLnk"[]{};"es-lnk"[]{'"es";'"e"};'"l"} }  -->
   sequent { <H> >- "equal"[]{"Id"[]{};"es-tag"[]{'"es";'"e"};'"tg"} }  -->
   sequent { <H> >- "subtype"[]{"es-valtype"[]{'"es";'"e"};'"T"} }

interactive nuprl_es__sends1 univ[level:l]  :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"e" in "es-E"[]{'"es"} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"T" }  -->
   sequent { <H> >- "subtype"[]{"set"[]{"es-Msg"[]{'"es"};"m"."equal"[]{"Id"[]{};"lsrc"[]{"mlnk"[]{'"m"}};"lsrc"[]{'"l"}}};"Msg"[]{"lambda"[]{"l'"."lambda"[]{"tg'"."ifthenelse"[]{"band"[]{"eq_lnk"[]{'"l'";'"l"};"eq_id"[]{'"tg'";'"tg"}};'"T";"top"[]{}}}}}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"Msg"[]{"lambda"[]{"l'"."lambda"[]{"tg'"."ifthenelse"[]{"band"[]{"eq_lnk"[]{'"l'";'"l"};"eq_id"[]{'"tg'";'"tg"}};'"T";"top"[]{}}}}}};"es-sends"[]{'"es";'"l";'"e"};"cons"[]{"msg"[]{'"l";'"tg";'"v"};"nil"[]{}}} }  -->
   sequent { <H> >- "exists"[]{"es-E"[]{'"es"};"e'"."and"[]{"cand"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e'"};"rcv"[]{'"l";'"tg"}};"and"[]{"equal"[]{'"T";"es-val"[]{'"es";'"e'"};'"v"};"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e'"};'"e"}}};"all"[]{"es-E"[]{'"es"};"e''"."implies"[]{"equal"[]{"Knd"[]{};"es-kind"[]{'"es";'"e''"};"rcv"[]{'"l";'"tg"}};"implies"[]{"equal"[]{"es-E"[]{'"es"};"es-sender"[]{'"es";'"e''"};'"e"};"equal"[]{"es-E"[]{'"es"};'"e''";'"e'"}}}}}} }

interactive nuprl_msys__at__compatible__right   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{('"M" '"i");'"A"} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{('"M" '"i");'"A"} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{('"M" '"i");'"A"} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{'"M";"m-sys-at"[]{'"i";'"A"}} }

interactive nuprl_msys__at__compatible__left   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H> >- '"M" in "msystem"[level:l]{} }  -->
   sequent { <H> >- "ma-compatible"[level:l]{'"A";('"M" '"i")} }  -->
   sequent { <H> >- "ma-frame-compatible"[]{'"A";('"M" '"i")} }  -->
   sequent { <H> >- "ma-sframe-compatible"[]{'"A";('"M" '"i")} }  -->
   sequent { <H> >- "m-sys-compatible"[level:l]{"m-sys-at"[]{'"i";'"A"};'"M"} }

interactive_rw nuprl_msys__at__at   :
   ('"i" in "Id"[]{}) -->
   ("m-sys-at"[]{'"i";'"A"} '"i") <--> '"A"

interactive nuprl_m__sys__at__sub__lemma1  "lambda"[]{"x".'"P"['"x"]} "lambda"[]{"x".'"L"['"x"]} '"i" '"n" '"A"  :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"A" in "msga"[level:l]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"P"['"x"] in "bool"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"Id"[]{};"loc"."assert"[]{'"P"['"loc"]}} >- '"L"['"x"] in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H>; "loc": "Id"[]{}  >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};"ifthenelse"[]{'"P"['"loc"];'"L"['"loc"];"nil"[]{}}} }  -->
   sequent { <H> >- "assert"[]{'"P"['"i"]} }  -->
   [wf] sequent { <H> >- '"n" in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"['"i"]}} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"A";"select"[]{'"n";'"L"['"i"]}} }  -->
   sequent { <H> >- "d-sub"[level:l]{"m-sys-at"[]{'"i";'"A"};"lambda"[]{"loc"."ma-join-list"[]{"ifthenelse"[]{'"P"['"loc"];'"L"['"loc"];"nil"[]{}}}}} }

interactive nuprl_d__sub__lemma1  "lambda"[]{"x".'"L"['"x"]} '"n" '"m" '"D"  :
   [wf] sequent { <H> >- '"D" in "dsys"[level:l]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "Id"[]{} >- '"L"['"x"] in "list"[]{"msga"[level:l]{}} }  -->
   sequent { <H>; "loc": "Id"[]{}  >- "pairwise"[]{"A", "B"."ma-compat"[level:l]{'"A";'"B"};'"L"['"loc"]} }  -->
   sequent { <H>; "loc": "Id"[]{}  >- "equal"[]{"nat"[]{};"length"[]{'"L"['"loc"]};'"n"} }  -->
   [wf] sequent { <H> >- '"m" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D";"lambda"[]{"loc"."select"[]{'"m";'"L"['"loc"]}}} }  -->
   sequent { <H> >- "d-sub"[level:l]{'"D";"lambda"[]{"loc"."ma-join-list"[]{'"L"['"loc"]}}} }

interactive nuprl_ma__sub__join__mapl  '"L" '"l" "lambda"[]{"x".'"M"['"x"]}  :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H>;"x": "set"[]{"IdLnk"[]{};"l"."mem"[]{'"l";'"L";"IdLnk"[]{}}} >- '"M"['"x"] in "msga"[level:l]{} }  -->
   sequent { <H> >- "mem"[]{'"l";'"L";"IdLnk"[]{}} }  -->
   sequent { <H>; "x": "IdLnk"[]{} ; "y": "IdLnk"[]{} ; "mem"[]{'"x";'"L";"IdLnk"[]{}} ; "mem"[]{'"y";'"L";"IdLnk"[]{}} ; "not"[]{"equal"[]{"IdLnk"[]{};'"x";'"y"}}  >- "ma-compat"[level:l]{'"M"['"x"];'"M"['"y"]} }  -->
   sequent { <H> >- "ma-sub"[level:l]{'"M"['"l"];"ma-join-list"[]{"mapl"[]{"lambda"[]{"l".'"M"['"l"]};'"L"}}} }


(**** display forms ****)


dform nuprl_effect__type_df : except_mode[src] :: "effect-type"[]{'"ds";'"ds'";'"da"} =
   `"effect-type(" slot{'"ds"} `";" slot{'"ds'"} `";" slot{'"da"} `")"


