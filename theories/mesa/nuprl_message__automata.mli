extends Ma_worlds


define unfold_ma__state : "ma-state"[]{'"ds"} <-->
      "fun"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"top"[]{}}}


define unfold_ma__kind : "ma-kind"[]{'"da"} <-->
      "set"[]{"Knd"[]{};"k"."assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"k";'"da"}}}


define unfold_ma__valtype : "ma-valtype"[]{'"da";'"k"} <-->
      "fpf-cap"[]{'"da";"Kind-deq"[]{};'"k";"top"[]{}}


define unfold_ma__Msg : "ma-Msg"[]{'"da"} <-->
      "Msg"[]{"lambda"[]{"l"."lambda"[]{"tg"."fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}}}}


define unfold_msga : "msga"[level:l]{} <-->
      "prod"[]{"fpf"[]{"Id"[]{};"x"."univ"[level:l]{}};"ds"."prod"[]{"fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}};"da"."prod"[]{"fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}};"init"."prod"[]{"fpf"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"locl"[]{'"a"}};""."univ"[level:l]{}}}};"pre"."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kx"}};""."fpf-cap"[]{'"ds";"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}}};"ef"."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{'"ds"};""."fun"[]{"ma-valtype"[]{'"da";"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{'"da";"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}}};"send"."prod"[]{"fpf"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}}};"frame"."prod"[]{"fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}}};"sframe"."top"[]{}}}}}}}}}


define unfold_ma__X : "ma-X"[]{'"M"} <-->
      "set"[]{"Id"[]{};"x"."assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";"fst"[]{'"M"}}}}


define unfold_ma__A : "ma-A"[]{'"M"} <-->
      "set"[]{"Knd"[]{};"a"."assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"a";"fst"[]{"snd"[]{'"M"}}}}}


define unfold_ma__ds : "ma-ds"[]{'"M";'"x"} <-->
      "fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};'"x";"top"[]{}}


define unfold_ma__da : "ma-da"[]{'"M";'"a"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};'"a";"top"[]{}}


define unfold_ma__declx : "ma-declx"[]{'"M";'"x"} <-->
      "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";"fst"[]{'"M"}}}


define unfold_ma__declk : "ma-declk"[]{'"M";'"k"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"k";"fst"[]{"snd"[]{'"M"}}}}


define unfold_ma__decla : "ma-decla"[]{'"M";'"a"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};"locl"[]{'"a"};"fst"[]{"snd"[]{'"M"}}}}


define unfold_ma__declm : "ma-declm"[]{'"M";'"l";'"tg"} <-->
      "assert"[]{"fpf-dom"[]{"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"fst"[]{"snd"[]{'"M"}}}}


define unfold_da__outlink__f : "da-outlink-f"[]{'"da";'"k"} <-->
      "pair"[]{"lnk"[]{'"k"};"pair"[]{"tagof"[]{'"k"};"fpf-ap"[]{'"da";"Kind-deq"[]{};'"k"}}}


define unfold_da__outlinks : "da-outlinks"[]{'"da";'"i"} <-->
      "mapfilter"[]{"lambda"[]{"k"."da-outlink-f"[]{'"da";'"k"}};"lambda"[]{"k"."has-src"[]{'"i";'"k"}};"fpf-dom-list"[]{'"da"}}


define unfold_ma__outlinks : "ma-outlinks"[]{'"M";'"i"} <-->
      "da-outlinks"[]{"fst"[]{"snd"[]{'"M"}};'"i"}


define unfold_ma__din : "ma-din"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"top"[]{}}


define unfold_ma__tag__type : "ma-tag-type"[level:l]{'"M";'"tg";'"T"} <-->
      "all"[]{"IdLnk"[]{};"l"."implies"[]{"ma-declm"[]{'"M";'"l";'"tg"};"equal"[]{"univ"[level:l]{};"ma-din"[]{'"M";'"l";'"tg"};'"T"}}}


define unfold_ma__dout : "ma-dout"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}


define unfold_ma__init : "ma-init"[]{'"M";'"x";'"v"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M"}}};'"x";"a", "x0"."equal"[]{"fpf-cap"[]{"fst"[]{'"M"};"id-deq"[]{};'"x";"void"[]{}};'"v";'"x0"}}


define unfold_ma__init__val : "ma-init-val"[]{'"M";'"x";'"v"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{"snd"[]{'"M"}}};"id-deq"[]{};'"x";'"v"}


define unfold_ma__st : "ma-st"[]{'"M"} <-->
      "ma-state"[]{"fst"[]{'"M"}}


define unfold_ma__msg : "ma-msg"[]{'"M"} <-->
      "ma-Msg"[]{"fst"[]{"snd"[]{'"M"}}}


define unfold_ma__k : "ma-k"[]{'"M"} <-->
      "ma-kind"[]{"fst"[]{"snd"[]{'"M"}}}


define unfold_ma__v : "ma-v"[]{'"M";'"k"} <-->
      "ma-valtype"[]{"fst"[]{"snd"[]{'"M"}};'"k"}


define unfold_ma__npre : "ma-npre"[]{'"M";'"a";'"s"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};'"a";"a", "P"."all"[]{"ma-da"[]{'"M";"locl"[]{'"a"}};"v"."not"[]{(('"P" '"s") '"v")}}}


define unfold_ma__pre : "ma-pre"[]{'"M";'"a";'"s";'"v"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};'"a";"a", "P".(('"P" '"s") '"v")}


define unfold_ma__has__pre : "ma-has-pre"[]{'"M";'"a"} <-->
      "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"a";"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}


define unfold_ma__ef : "ma-ef"[]{'"M";'"k";'"x";'"s";'"v";'"w"} <-->
      "fpf-val"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"pair"[]{'"k";'"x"};"kx", "E"."equal"[]{"ma-ds"[]{'"M";'"x"};'"w";(('"E" '"s") '"v")}}


define unfold_ma__ef__val : "ma-ef-val"[]{'"M";'"k";'"x";'"s";'"v";'"w"} <-->
      (("fpf-cap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"pair"[]{'"k";'"x"};"lambda"[]{"s"."lambda"[]{"v".'"w"}}} '"s") '"v")


define unfold_tagged__list__messages : "tagged-list-messages"[]{'"s";'"v";'"L"} <-->
      "concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"s") '"v")}};'"L"}}


define unfold_tagged__messages : "tagged-messages"[]{'"l";'"s";'"v";'"L"} <-->
      "map"[]{"lambda"[]{"x"."pair"[]{'"l";'"x"}};"tagged-list-messages"[]{'"s";'"v";'"L"}}


define unfold_ma__send : "ma-send"[]{'"M";'"k";'"l";'"s";'"v";'"ms";'"i"} <-->
      "fpf-val"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"pair"[]{'"k";'"l"};"k", "L"."equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg"."ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"ma-da"[]{'"M";"rcv"[]{'"l";'"tg"}};"top"[]{}}}};'"ms";"ifthenelse"[]{"eq_id"[]{"lsrc"[]{'"l"};'"i"};"concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"s") '"v")}};'"L"}};"nil"[]{}}}}


define unfold_ma__send__val : "ma-send-val"[]{'"M";'"k";'"s";'"v"} <-->
      "concat"[]{"map"[]{"lambda"[]{"pL"."tagged-messages"[]{"snd"[]{"fst"[]{'"pL"}};'"s";'"v";"snd"[]{'"pL"}}};"fpf-vals"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"lambda"[]{"p".(("eqof"[]{"Kind-deq"[]{}} "fst"[]{'"p"}) '"k")};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}


define unfold_ma__sends__on : "ma-sends-on"[]{'"M";'"l"} <-->
      "deq-member"[]{"idlnk-deq"[]{};'"l";"map"[]{"lambda"[]{"p"."snd"[]{'"p"}};"fst"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}


define unfold_sends__on__pair : "sends-on-pair"[]{'"s";'"l";'"tg"} <-->
      "reduce"[]{"lambda"[]{"kl"."lambda"[]{"x"."bor"[]{"band"[]{(("eqof"[]{"idlnk-deq"[]{}} "snd"[]{'"kl"}) '"l");"deq-member"[]{"id-deq"[]{};'"tg";"map"[]{"lambda"[]{"z"."fst"[]{'"z"}};("snd"[]{'"s"} '"kl")}}};'"x"}}};"bfalse"[]{};"fst"[]{'"s"}}


define unfold_ma__dout2 : "ma-dout2"[]{'"M";'"l";'"tg"} <-->
      "fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"rcv"[]{'"l";'"tg"};"void"[]{}}


define unfold_ma__frame : "ma-frame"[]{'"M";'"k";'"x"} <-->
      "fpf-val"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};'"x";"x", "L"."assert"[]{"deq-member"[]{"Kind-deq"[]{};'"k";'"L"}}}


define unfold_ma__sframe : "ma-sframe"[]{'"M";'"k";'"l";'"tg"} <-->
      "fpf-val"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"pair"[]{'"l";'"tg"};"x", "L"."assert"[]{"deq-member"[]{"Kind-deq"[]{};'"k";'"L"}}}


define unfold_ma__sub : "ma-sub"[level:l]{'"M1";'"M2"} <-->
      "cand"[]{"and"[]{"fpf-sub"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-sub"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"x"."fpf-cap"[]{"fst"[]{'"M2"};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M2"}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};""."univ"[level:l]{}}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"and"[]{"fpf-sub"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M2"}};"fst"[]{'"kx"}};""."fpf-cap"[]{"fst"[]{'"M2"};"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"and"[]{"fpf-sub"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{"fst"[]{'"M2"}};""."fun"[]{"ma-valtype"[]{"fst"[]{"snd"[]{'"M2"}};"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M2"}};"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"and"[]{"fpf-sub"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-sub"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"ltg"."list"[]{"Knd"[]{}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}}}}}}


define unfold_mk__ma : "mk-ma"[]{'"ds";'"da";'"init";'"pre";'"ef";'"send";'"frame";'"sframe"} <-->
      "pair"[]{'"ds";"pair"[]{'"da";"pair"[]{'"init";"pair"[]{'"pre";"pair"[]{'"ef";"pair"[]{'"send";"pair"[]{'"frame";"pair"[]{'"sframe";"it"[]{}}}}}}}}}


define unfold_ma__empty : "ma-empty"[]{} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__is__empty : "ma-is-empty"[]{'"M"} <-->
      "band"[]{"fpf-is-empty"[]{"fst"[]{'"M"}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{'"M"}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{'"M"}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};"band"[]{"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"fpf-is-empty"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}}}}}}}}


define unfold_ma__compatible__decls : "ma-compatible-decls"[level:l]{'"M1";'"M2"} <-->
      "and"[]{"fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}}}


define unfold_ma__join : "ma-join"[]{'"M1";'"M2"} <-->
      "mk-ma"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"fpf-join"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"fpf-join"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"fpf-join"[]{"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-join"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}


define unfold_ma__compatible : "ma-compatible"[level:l]{'"M1";'"M2"} <-->
      "and"[]{"ma-compatible-decls"[level:l]{'"M1";'"M2"};"and"[]{"fpf-compatible"[]{"Id"[]{};"x"."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{'"M1"}}};"fst"[]{"snd"[]{"snd"[]{'"M2"}}}};"and"[]{"fpf-compatible"[]{"Id"[]{};"a"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"fpf-cap"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};""."univ"[level:l]{}}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}};"and"[]{"fpf-compatible"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"ma-valtype"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fst"[]{'"kx"}};""."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}};"id-deq"[]{};"snd"[]{'"kx"};"void"[]{}}}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}};"and"[]{"fpf-compatible"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{"ma-state"[]{"fpf-join"[]{"id-deq"[]{};"fst"[]{'"M1"};"fst"[]{'"M2"}}};""."fun"[]{"ma-valtype"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"fst"[]{'"kl"}};""."list"[]{"fpf-cap"[]{"fpf-join"[]{"Kind-deq"[]{};"fst"[]{"snd"[]{'"M1"}};"fst"[]{"snd"[]{'"M2"}}};"Kind-deq"[]{};"rcv"[]{"snd"[]{'"kl"};'"tg"};"void"[]{}}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}};"and"[]{"fpf-compatible"[]{"Id"[]{};"x"."list"[]{"Knd"[]{}};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}};"fpf-compatible"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"lt"."list"[]{"Knd"[]{}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M1"}}}}}}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M2"}}}}}}}}}}}}}}}


define unfold_ma__single__init : "ma-single-init"[]{'"x";'"t";'"v"} <-->
      "mk-ma"[]{"fpf-single"[]{'"x";'"t"};"fpf-empty"[]{};"fpf-single"[]{'"x";'"v"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__frame : "ma-single-frame"[]{'"L";'"t";'"x"} <-->
      "mk-ma"[]{"fpf-single"[]{'"x";'"t"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{'"x";'"L"};"fpf-empty"[]{}}


define unfold_ma__single__sframe : "ma-single-sframe"[]{'"L";'"l";'"tg"} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"l";'"tg"};'"L"}}


define unfold_ma__single__effect : "ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"} <-->
      "mk-ma"[]{'"ds";'"da";"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"k";'"x"};'"f"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__effect0 : "ma-single-effect0"[]{'"x";'"A";'"k";'"T";'"f"} <-->
      "ma-single-effect"[]{"fpf-single"[]{'"x";'"A"};"fpf-single"[]{'"k";'"T"};'"k";'"x";"lambda"[]{"s"."lambda"[]{"v".(('"f" ('"s" '"x")) '"v")}}}


define unfold_ma__single__effect1 : "ma-single-effect1"[]{'"x";'"A";'"y";'"B";'"k";'"T";'"f"} <-->
      "ma-single-effect"[]{"fpf-join"[]{"id-deq"[]{};"fpf-single"[]{'"x";'"A"};"fpf-single"[]{'"y";'"B"}};"fpf-single"[]{'"k";'"T"};'"k";'"x";"lambda"[]{"s"."lambda"[]{"v".((('"f" ('"s" '"x")) ('"s" '"y")) '"v")}}}


define unfold_ma__single__sends : "ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"} <-->
      "mk-ma"[]{'"ds";'"da";"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{"pair"[]{'"k";'"l"};'"f"};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__sends0 : "ma-single-sends0"[]{'"B";'"T";'"a";'"l";'"tg";'"f"} <-->
      "ma-single-sends"[]{"fpf-empty"[]{};"fpf-join"[]{"Kind-deq"[]{};"fpf-single"[]{'"a";'"B"};"fpf-single"[]{"rcv"[]{'"l";'"tg"};'"T"}};'"a";'"l";"cons"[]{"pair"[]{'"tg";"lambda"[]{"s"."lambda"[]{"v".('"f" '"v")}}};"nil"[]{}}}


define unfold_ma__single__sends1 : "ma-single-sends1"[]{'"A";'"B";'"T";'"x";'"a";'"l";'"tg";'"f"} <-->
      "ma-single-sends"[]{"fpf-single"[]{'"x";'"A"};"fpf-join"[]{"Kind-deq"[]{};"fpf-single"[]{'"a";'"B"};"fpf-single"[]{"rcv"[]{'"l";'"tg"};'"T"}};'"a";'"l";"cons"[]{"pair"[]{'"tg";"lambda"[]{"s"."lambda"[]{"v".(('"f" ('"s" '"x")) '"v")}}};"nil"[]{}}}


define unfold_ma__single__pre : "ma-single-pre"[]{'"ds";'"a";'"T";'"P"} <-->
      "mk-ma"[]{'"ds";"fpf-single"[]{"locl"[]{'"a"};'"T"};"fpf-empty"[]{};"fpf-single"[]{'"a";'"P"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__pre1 : "ma-single-pre1"[]{'"x";'"A";'"a";'"T";"y", "v".'"P"['"y";'"v"]} <-->
      "ma-single-pre"[]{"fpf-single"[]{'"x";'"A"};'"a";'"T";"lambda"[]{"s", "v".'"P"[('"s" '"x");'"v"]}}


define unfold_ma__single__pre__true : "ma-single-pre-true"[]{'"a"} <-->
      "mk-ma"[]{"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-single"[]{'"a";"lambda"[]{"s"."lambda"[]{"v"."true"[]{}}}};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__pre__init : "ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"} <-->
      "mk-ma"[]{'"ds";"fpf-single"[]{"locl"[]{'"a"};'"T"};'"init";"fpf-single"[]{'"a";'"P"};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{};"fpf-empty"[]{}}


define unfold_ma__single__pre__init1 : "ma-single-pre-init1"[]{'"x";'"T";'"c";'"a";'"T'";"y", "v".'"P"['"y";'"v"]} <-->
      "ma-single-pre-init"[]{"fpf-single"[]{'"x";'"T"};"fpf-single"[]{'"x";'"c"};'"a";'"T'";"lambda"[]{"s"."lambda"[]{"v".'"P"[('"s" '"x");'"v"]}}}


define unfold_ma__feasible : "ma-feasible"[]{'"M"} <-->
      "and"[]{"fpf-all"[]{"Id"[]{};"id-deq"[]{};"fst"[]{'"M"};"x", "T".'"T"};"and"[]{"fpf-all"[]{"Knd"[]{};"Kind-deq"[]{};"fst"[]{"snd"[]{'"M"}};"k", "T"."decidable"[]{'"T"}};"and"[]{"fpf-all"[]{"Id"[]{};"id-deq"[]{};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}};"a", "p"."all"[]{"ma-state"[]{"fst"[]{'"M"}};"s"."decidable"[]{"exists"[]{"fpf-cap"[]{"fst"[]{"snd"[]{'"M"}};"Kind-deq"[]{};"locl"[]{'"a"};"top"[]{}};"v".(('"p" '"s") '"v")}}}};"and"[]{"fpf-all"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}};"kx", "ef"."ma-frame"[]{'"M";"fst"[]{'"kx"};"snd"[]{'"kx"}}};"fpf-all"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"kl", "snd"."all"[]{"Id"[]{};"tg"."implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"snd"};"Id"[]{}};"ma-sframe"[]{'"M";"fst"[]{'"kl"};"snd"[]{'"kl"};'"tg"}}}}}}}}


define unfold_ma__frame__compatible : "ma-frame-compatible"[]{'"A";'"B"} <-->
      "all"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"kx"."and"[]{"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};'"kx";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kx"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}};"id-deq"[]{};"snd"[]{'"kx"}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};'"kx";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};"snd"[]{'"kx"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kx"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}};"id-deq"[]{};"snd"[]{'"kx"}}}}}}}}}


define unfold_ma__sframe__compatible : "ma-sframe-compatible"[]{'"A";'"B"} <-->
      "all"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"kl"."all"[]{"Id"[]{};"tg"."and"[]{"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}};"implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl"}};"Id"[]{}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kl"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl";"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}};"implies"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}};"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};'"kl"}};"Id"[]{}};"implies"[]{"not"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"B"}}}}}}}}}}};"implies"[]{"assert"[]{"fpf-dom"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}}}};"assert"[]{"deq-member"[]{"Kind-deq"[]{};"fst"[]{'"kl"};"fpf-ap"[]{"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"A"}}}}}}}};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"pair"[]{"snd"[]{'"kl"};'"tg"}}}}}}}}}}}


define unfold_ma__compat : "ma-compat"[level:l]{'"A";'"B"} <-->
      "and"[]{"ma-compatible"[level:l]{'"A";'"B"};"and"[]{"ma-frame-compatible"[]{'"A";'"B"};"ma-sframe-compatible"[]{'"A";'"B"}}}


define unfold_ma__join__list : "ma-join-list"[]{'"L"} <-->
      "reduce"[]{"lambda"[]{"A"."lambda"[]{"B"."ma-join"[]{'"A";'"B"}}};"ma-empty"[]{};'"L"}


define unfold_msg__form : "msg-form"[level:l]{} <-->
      "prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Knd"[]{};"x"."univ"[level:l]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"x"."top"[]{}};""."prod"[]{"fpf"[]{"Id"[]{};"x"."top"[]{}};""."prod"[]{"fpf"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"x"."top"[]{}};""."top"[]{}}}}}}}}}


define unfold_ma__rename : "ma-rename"[]{'"rx";'"ra";'"rt";'"M"} <-->
      "mk-ma"[]{"fpf-rename"[]{"id-deq"[]{};'"rx";"fst"[]{'"M"}};"fpf-rename"[]{"Kind-deq"[]{};"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};"fst"[]{"snd"[]{'"M"}}};"fpf-rename"[]{"id-deq"[]{};'"rx";"fst"[]{"snd"[]{"snd"[]{'"M"}}}};"fpf-rename"[]{"id-deq"[]{};'"ra";"fpf-compose"[]{"lambda"[]{"f"."lambda"[]{"s"."lambda"[]{"v".(('"f" "compose"[]{'"s";'"rx"}) '"v")}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}};"fpf-rename"[]{"product-deq"[]{"Knd"[]{};"Id"[]{};"Kind-deq"[]{};"id-deq"[]{}};"lambda"[]{"p"."pair"[]{"kind-rename"[]{'"ra";'"rt";"fst"[]{'"p"}};('"rx" "snd"[]{'"p"})}};"fpf-compose"[]{"lambda"[]{"f"."lambda"[]{"s"."lambda"[]{"v".(('"f" "compose"[]{'"s";'"rx"}) '"v")}}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}};"fpf-rename"[]{"product-deq"[]{"Knd"[]{};"IdLnk"[]{};"Kind-deq"[]{};"idlnk-deq"[]{}};"lambda"[]{"p"."pair"[]{"kind-rename"[]{'"ra";'"rt";"fst"[]{'"p"}};"snd"[]{'"p"}}};"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"p"."pair"[]{('"rt" "fst"[]{'"p"});"lambda"[]{"s"."lambda"[]{"v".(("snd"[]{'"p"} "compose"[]{'"s";'"rx"}) '"v")}}}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}};"fpf-rename"[]{"id-deq"[]{};'"rx";"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}};"fpf-rename"[]{"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"lambda"[]{"p"."pair"[]{"fst"[]{'"p"};('"rt" "snd"[]{'"p"})}};"fpf-compose"[]{"lambda"[]{"L"."map"[]{"lambda"[]{"k"."kind-rename"[]{'"ra";'"rt";'"k"}};'"L"}};"fst"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{"snd"[]{'"M"}}}}}}}}}}}


