extends Ma_messages__and__kinds


define unfold_deq : "deq"[]{'"T"} <-->
      "prod"[]{"fun"[]{'"T";""."fun"[]{'"T";""."bool"[]{}}};"eq"."all"[]{'"T";"x"."all"[]{'"T";"y"."iff"[]{"equal"[]{'"T";'"x";'"y"};"assert"[]{(('"eq" '"x") '"y")}}}}}


define unfold_eqof : "eqof"[]{'"d"} <-->
      "fst"[]{'"d"}


define unfold_nat__deq : "nat-deq"[]{} <-->
      "pair"[]{"lambda"[]{"a"."lambda"[]{"b"."beq_int"[]{'"a";'"b"}}};"termof"[]{}}


define unfold_atom__deq : "atom-deq"[]{} <-->
      "pair"[]{"lambda"[]{"a"."lambda"[]{"b"."eq_atom"[]{'"a";'"b"}}};"termof"[]{}}


define unfold_proddeq : "proddeq"[]{'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."band"[]{(("fst"[]{'"a"} "fst"[]{'"p"}) "fst"[]{'"q"});(("fst"[]{'"b"} "snd"[]{'"p"}) "snd"[]{'"q"})}}}


define unfold_prod__deq__aux : "prod-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."spread"[]{'"q";"q1", "q2"."spread"[]{'"p";"p1", "p2"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%3"."spread"[]{"decide"[]{(('"eq" '"p2") '"q2");"x"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}};"%5", "%6".('"%6" "pair"[]{"spread"[]{(('"a1" '"p1") '"q1");"%4", "%5".('"%4" "it"[]{})};"spread"[]{(('"b1" '"p2") '"q2");"%4", "%5".('"%4" "it"[]{})}})}};"lambda"[]{"%3"."spread"[]{"spread"[]{"decide"[]{(('"eq" '"p2") '"q2");"x"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}};"%5", "%6".('"%5" '"%3")};"%1", "%2"."it"[]{}}}}}}}}}}


define unfold_prod__deq : "prod-deq"[]{'"A";'"B";'"a";'"b"} <-->
      (((("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"p"."lambda"[]{"q"."spread"[]{'"q";"q1", "q2"."spread"[]{'"p";"p1", "p2"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1".("lambda"[]{"%1".('"%1" "pair"[]{"lambda"[]{"%"."pair"[]{("lambda"[]{"%1"."spread"[]{(('"%1" '"p1") '"q1");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} "it"[]{})))}} '"a1");("lambda"[]{"%1"."spread"[]{(('"%1" '"p2") '"q2");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} "it"[]{})))}} '"b1")}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."it"[]{}}}})} ("lambda"[]{"%1"."spread"[]{'"%1";"%2", "%3".'"%3"}} ("lambda"[]{"%1".(((((('"%1" "equal"[]{"prod"[]{'"A";"".'"B"};"pair"[]{'"p1";'"p2"};"pair"[]{'"q1";'"q2"}}) "equal"[]{"prod"[]{'"A";"".'"B"};"pair"[]{'"p1";'"p2"};"pair"[]{'"q1";'"q2"}}) "assert"[]{"band"[]{(('"e1" '"p1") '"q1");(('"eq" '"p2") '"q2")}}) "and"[]{"assert"[]{(('"e1" '"p1") '"q1")};"assert"[]{(('"eq" '"p2") '"q2")}}) ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."pair"[]{"lambda"[]{"%2".'"%2"};"lambda"[]{"%2".'"%2"}}} "it"[]{}))) ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".(('"%1" (('"e1" '"p1") '"q1")) (('"eq" '"p2") '"q2"))} "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{'"p";"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}}}})))} "lambda"[]{"P1"."lambda"[]{"P2"."lambda"[]{"Q1"."lambda"[]{"Q2"."lambda"[]{"%"."lambda"[]{"%1"."pair"[]{"lambda"[]{"%2"."pair"[]{"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%")))}} '"%2")))}} '"%1")};"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%1")))}} '"%2")))}} '"%")}}};"lambda"[]{"%2"."pair"[]{"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%")))}} '"%2")))}} '"%1")};"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%1")))}} '"%2")))}} '"%")}}}}}}}}}})))}}}}}}}}}} '"A") '"B") '"a") '"b")


define unfold_product__deq : "product-deq"[]{'"A";'"B";'"a";'"b"} <-->
      "pair"[]{"proddeq"[]{'"a";'"b"};"prod-deq"[]{'"A";'"B";'"a";'"b"}}


define unfold_sumdeq : "sumdeq"[]{'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"p";"pa"."decide"[]{'"q";"qa".(("fst"[]{'"a"} '"pa") '"qa");"qb"."bfalse"[]{}};"pb"."decide"[]{'"q";"qa"."bfalse"[]{};"qb".(("fst"[]{'"b"} '"pb") '"qb")}}}}


define unfold_sum__deq__aux : "sum-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."spread"[]{(('"a1" '"x1") '"x");"%4", "%5".('"%4" "it"[]{})}};"lambda"[]{"%"."it"[]{}}}}};"y"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."any"[]{"any"[]{"any"[]{"it"[]{}}}}};"lambda"[]{"%"."it"[]{}}}}}};"y"."decide"[]{'"p";"x"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."any"[]{"any"[]{"any"[]{"it"[]{}}}}};"lambda"[]{"%"."it"[]{}}}}};"y1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."spread"[]{(('"b1" '"y1") '"y");"%4", "%5".('"%4" "it"[]{})}};"lambda"[]{"%"."it"[]{}}}}}}}}}


define unfold_sum__deq : "sum-deq"[]{'"A";'"B";'"a";'"b"} <-->
      (((("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."spread"[]{(('"%1" '"x1") '"x");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"x1")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"x1"."lambda"[]{"x"."lambda"[]{"%".("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".("lambda"[]{"%2"."it"[]{}} "it"[]{})} '"%"))}}}}})))))))}} '"a1")};"lambda"[]{"%"."it"[]{}}}}};"y"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."any"[]{('"%1" "it"[]{})}} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"y"."lambda"[]{"x"."lambda"[]{"%".("lambda"[]{"%1"."decide"[]{'"%1";"%2"."any"[]{'"%2"};"%3".("lambda"[]{"%4"."any"[]{'"%4"}} ("lambda"[]{"%4".("lambda"[]{"%5".("lambda"[]{"%6"."any"[]{'"%6"}} "it"[]{})} "it"[]{})} '"%"))}} ("lambda"[]{"%1".'"%1"} "inr"[]{"lambda"[]{"%"."it"[]{}}}))}}}}})))))};"lambda"[]{"%"."it"[]{}}}}}};"y"."decide"[]{'"p";"x"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."any"[]{('"%1" "it"[]{})}} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%".("lambda"[]{"%1"."decide"[]{'"%1";"%2"."any"[]{'"%2"};"%3".("lambda"[]{"%4"."any"[]{'"%4"}} ("lambda"[]{"%4".("lambda"[]{"%5".("lambda"[]{"%6"."any"[]{'"%6"}} "it"[]{})} "it"[]{})} '"%"))}} ("lambda"[]{"%1".'"%1"} "inr"[]{"lambda"[]{"%"."it"[]{}}}))}}}}})))))};"lambda"[]{"%"."it"[]{}}}}};"y1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."spread"[]{(('"%1" '"y1") '"y");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"y1")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"y1"."lambda"[]{"y"."lambda"[]{"%".("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".("lambda"[]{"%2"."it"[]{}} "it"[]{})} '"%"))}}}}})))))))}} '"b1")};"lambda"[]{"%"."it"[]{}}}}}}}}}}}}} '"A") '"B") '"a") '"b")


define unfold_union__deq : "union-deq"[]{'"A";'"B";'"a";'"b"} <-->
      "pair"[]{"sumdeq"[]{'"a";'"b"};"sum-deq"[]{'"A";'"B";'"a";'"b"}}


define unfold_deq__member : "deq-member"[]{'"eq";'"x";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"b"."bor"[]{(("eqof"[]{'"eq"} '"a") '"x");'"b"}}};"bfalse"[]{};'"L"}


define unfold_discrete_struct : "discrete_struct"[level:l]{'"A"} <-->
      "prod"[]{"fun"[]{'"A";""."univ"[level:l]{}};"sort"."fun"[]{'"A";"a"."deq"[]{('"sort" '"a")}}}


define unfold_dstype : "dstype"[]{'"TypeNames";'"d";'"a"} <-->
      ("fst"[]{'"d"} '"a")


define unfold_dsdeq : "dsdeq"[]{'"d";'"a"} <-->
      ("snd"[]{'"d"} '"a")


define unfold_dseq : "dseq"[]{'"d";'"a"} <-->
      "eqof"[]{("snd"[]{'"d"} '"a")}


define unfold_eq_ds : "eq_ds"[]{'"d";'"a";'"x";'"y"} <-->
      (("dseq"[]{'"d";'"a"} '"x") '"y")


define unfold_insert : "insert"[]{'"eq";'"a";'"L"} <-->
      "ifthenelse"[]{"deq-member"[]{'"eq";'"a";'"L"};'"L";"cons"[]{'"a";'"L"}}


define unfold_remove__repeats : "remove-repeats"[]{'"eq";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"L"."insert"[]{'"eq";'"a";'"L"}}};"nil"[]{};'"L"}


define unfold_id__deq : "id-deq"[]{} <-->
      "product-deq"[]{"atom"[]{};"nat"[]{};"atom-deq"[]{};"nat-deq"[]{}}


define unfold_eq_id : "eq_id"[]{'"a";'"b"} <-->
      (("eqof"[]{"id-deq"[]{}} '"a") '"b")


define unfold_idlnk__deq : "idlnk-deq"[]{} <-->
      "product-deq"[]{"Id"[]{};"prod"[]{"Id"[]{};""."nat"[]{}};"id-deq"[]{};"product-deq"[]{"Id"[]{};"nat"[]{};"id-deq"[]{};"nat-deq"[]{}}}


define unfold_eq_lnk : "eq_lnk"[]{'"a";'"b"} <-->
      (("eqof"[]{"idlnk-deq"[]{}} '"a") '"b")


define unfold_Kind__deq : "Kind-deq"[]{} <-->
      "union-deq"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"Id"[]{};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"id-deq"[]{}}


define unfold_eq_knd : "eq_knd"[]{'"a";'"b"} <-->
      (("eqof"[]{"Kind-deq"[]{}} '"a") '"b")


define unfold_standard__ds : "standard-ds"[]{} <-->
      "pair"[]{"lambda"[]{"a"."ifthenelse"[]{"beq_int"[]{'"a";"number"[2:n]{}};"IdLnk"[]{};"Id"[]{}}};"lambda"[]{"a"."ifthenelse"[]{"beq_int"[]{'"a";"number"[2:n]{}};"idlnk-deq"[]{};"id-deq"[]{}}}}


define unfold_l_index : "l_index"[]{'"dT";'"L";'"x"} <-->
      "mu"[]{"lambda"[]{"i".(("eqof"[]{'"dT"} '"x") "select"[]{'"i";'"L"})}}


define unfold_has__src : "has-src"[]{'"i";'"k"} <-->
      "band"[]{"isrcv"[]{'"k"};"eq_id"[]{"lsrc"[]{"lnk"[]{'"k"}};'"i"}}


