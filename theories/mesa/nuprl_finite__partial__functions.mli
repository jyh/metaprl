extends Ma_event__systems


define unfold_fpf : "fpf"[]{'"A";"a".'"B"['"a"]} <-->
      "prod"[]{"list"[]{'"A"};"d"."fun"[]{"set"[]{'"A";"a"."mem"[]{'"a";'"d";'"A"}};"a".'"B"['"a"]}}


define unfold_fpf__dom : "fpf-dom"[]{'"eq";'"x";'"f"} <-->
      "deq-member"[]{'"eq";'"x";"fst"[]{'"f"}}


define unfold_fpf__empty : "fpf-empty"[]{} <-->
      "pair"[]{"nil"[]{};"lambda"[]{"x"."it"[]{}}}


define unfold_fpf__is__empty : "fpf-is-empty"[]{'"f"} <-->
      "beq_int"[]{"length"[]{"fst"[]{'"f"}};"number"[0:n]{}}


define unfold_fpf__ap : "fpf-ap"[]{'"f";'"eq";'"x"} <-->
      ("snd"[]{'"f"} '"x")


define unfold_fpf__cap : "fpf-cap"[]{'"f";'"eq";'"x";'"z"} <-->
      "ifthenelse"[]{"fpf-dom"[]{'"eq";'"x";'"f"};"fpf-ap"[]{'"f";'"eq";'"x"};'"z"}


define unfold_fpf__val : "fpf-val"[]{'"eq";'"f";'"x";"a", "z".'"P"['"a";'"z"]} <-->
      "implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};'"P"['"x";"fpf-ap"[]{'"f";'"eq";'"x"}]}


define unfold_fpf__sub : "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} <-->
      "all"[]{'"A";"x"."implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"cand"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}};"equal"[]{'"B"['"x"];"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}}}}


define unfold_fpf__compatible : "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} <-->
      "all"[]{'"A";"x"."implies"[]{"and"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}};"equal"[]{'"B"['"x"];"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}}}


define unfold_fpf__join : "fpf-join"[]{'"eq";'"f";'"g"} <-->
      "pair"[]{"append"[]{"fst"[]{'"f"};"filter"[]{"lambda"[]{"a"."bnot"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}};"fst"[]{'"g"}}};"lambda"[]{"a"."fpf-cap"[]{'"f";'"eq";'"a";"fpf-ap"[]{'"g";'"eq";'"a"}}}}


define unfold_fpf__const : "fpf-const"[]{'"L";'"v"} <-->
      "pair"[]{'"L";"lambda"[]{"x".'"v"}}


define unfold_fpf__single : "fpf-single"[]{'"x";'"v"} <-->
      "pair"[]{"cons"[]{'"x";"nil"[]{}};"lambda"[]{"x".'"v"}}


define unfold_fpf__add__single : "fpf-add-single"[]{'"eq";'"f";'"x";'"v"} <-->
      "fpf-join"[]{'"eq";'"f";"fpf-single"[]{'"x";'"v"}}


define unfold_fpf__vals : "fpf-vals"[]{'"eq";'"P";'"f"} <-->
      "let"[]{"filter"[]{'"P";"remove-repeats"[]{'"eq";"fst"[]{'"f"}}};"L"."zip"[]{'"L";"map"[]{"snd"[]{'"f"};'"L"}}}


define unfold_fpf__all : "fpf-all"[]{'"A";'"eq";'"f";"x", "v".'"P"['"x";'"v"]} <-->
      "all"[]{'"A";"x"."implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};'"P"['"x";"fpf-ap"[]{'"f";'"eq";'"x"}]}}


define unfold_fpf__rename : "fpf-rename"[]{'"eq";'"r";'"f"} <-->
      "pair"[]{"map"[]{'"r";"fst"[]{'"f"}};"lambda"[]{"x".("snd"[]{'"f"} "hd"[]{"filter"[]{"lambda"[]{"y".(("eqof"[]{'"eq"} ('"r" '"y")) '"x")};"fst"[]{'"f"}}})}}


define unfold_fpf__inv__rename : "fpf-inv-rename"[]{'"r";'"rinv";'"f"} <-->
      "pair"[]{"mapfilter"[]{"lambda"[]{"x"."outl"[]{('"rinv" '"x")}};"lambda"[]{"x"."is_inl"[]{('"rinv" '"x")}};"fst"[]{'"f"}};"compose"[]{"snd"[]{'"f"};'"r"}}


define unfold_fpf__compose : "fpf-compose"[]{'"g";'"f"} <-->
      "pair"[]{"fst"[]{'"f"};"compose"[]{'"g";"snd"[]{'"f"}}}


define unfold_mkfpf : "mkfpf"[]{'"a";'"b"} <-->
      "pair"[]{'"a";'"b"}


define unfold_fpf__dom__list : "fpf-dom-list"[]{'"f"} <-->
      "fst"[]{'"f"}


