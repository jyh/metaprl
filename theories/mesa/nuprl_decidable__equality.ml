extends Ma_messages__and__kinds

open Dtactic


define unfold_deq : "deq"[]{'"T"} <-->
      "prod"[]{"fun"[]{'"T";""."fun"[]{'"T";""."bool"[]{}}};"eq"."all"[]{'"T";"x"."all"[]{'"T";"y"."iff"[]{"equal"[]{'"T";'"x";'"y"};"assert"[]{(('"eq" '"x") '"y")}}}}}


interactive nuprl_deq_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("deq"[]{'"T"} in "univ"[level:l]{}) }

interactive nuprl_deq_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   sequent { <H> >- "type"{"deq"[]{'"T"}} }

define unfold_eqof : "eqof"[]{'"d"} <-->
      "fst"[]{'"d"}


interactive nuprl_eqof_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"d" in "deq"[]{'"T"} }  -->
   sequent { <H> >- ("eqof"[]{'"d"} in "fun"[]{'"T";""."fun"[]{'"T";""."bool"[]{}}}) }

interactive nuprl_deq_property   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"d" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"equal"[]{'"T";'"x";'"y"};"assert"[]{(("eqof"[]{'"d"} '"x") '"y")}} }

interactive_rw nuprl_eqof_eq_btrue  '"A"  :
   "type"{'"A"} -->
   ('"d" in "deq"[]{'"A"}) -->
   ('"i" in '"A") -->
   (("eqof"[]{'"d"} '"i") '"i") <--> "btrue"[]{}

interactive_rw nuprl_eqof_equal_btrue  '"A"  :
   "type"{'"A"} -->
   ('"d" in "deq"[]{'"A"}) -->
   ('"i" in '"A") -->
   ('"j" in '"A") -->
   "equal"[]{'"A";'"i";'"j"} -->
   (("eqof"[]{'"d"} '"i") '"j") <--> "btrue"[]{}

interactive nuprl_strong__subtype__deq  '"B"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"d" in "deq"[]{'"B"} }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- ('"d" in "deq"[]{'"A"}) }

interactive nuprl_strong__subtype__deq__subtype   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"B"} }  -->
   sequent { <H> >- "subtype"[]{"deq"[]{'"B"};"deq"[]{'"A"}} }

interactive nuprl_nat__deq__aux   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"nat"[]{};'"a";'"b"};"assert"[]{"beq_int"[]{'"a";'"b"}}} }

define unfold_nat__deq : "nat-deq"[]{} <-->
      "pair"[]{"lambda"[]{"a"."lambda"[]{"b"."beq_int"[]{'"a";'"b"}}};"termof"[]{}}


interactive nuprl_nat__deq_wf {| intro[] |}   :
   sequent { <H> >- ("nat-deq"[]{} in "deq"[]{"nat"[]{}}) }

interactive nuprl_atom__deq__aux   :
   [wf] sequent { <H> >- '"a" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "atom"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"atom"[]{};'"a";'"b"};"assert"[]{"eq_atom"[]{'"a";'"b"}}} }

define unfold_atom__deq : "atom-deq"[]{} <-->
      "pair"[]{"lambda"[]{"a"."lambda"[]{"b"."eq_atom"[]{'"a";'"b"}}};"termof"[]{}}


interactive nuprl_atom__deq_wf {| intro[] |}   :
   sequent { <H> >- ("atom-deq"[]{} in "deq"[]{"atom"[]{}}) }

define unfold_proddeq : "proddeq"[]{'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."band"[]{(("fst"[]{'"a"} "fst"[]{'"p"}) "fst"[]{'"q"});(("fst"[]{'"b"} "snd"[]{'"p"}) "snd"[]{'"q"})}}}


interactive nuprl_proddeq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("proddeq"[]{'"a";'"b"} in "fun"[]{"prod"[]{'"A";"".'"B"};""."fun"[]{"prod"[]{'"A";"".'"B"};""."bool"[]{}}}) }

interactive nuprl_proddeq__property   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   [wf] sequent { <H> >- '"p" in "prod"[]{'"A";"".'"B"} }  -->
   [wf] sequent { <H> >- '"q" in "prod"[]{'"A";"".'"B"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"prod"[]{'"A";"".'"B"};'"p";'"q"};"assert"[]{(("proddeq"[]{'"a";'"b"} '"p") '"q")}} }

define unfold_prod__deq__aux : "prod-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."spread"[]{'"q";"q1", "q2"."spread"[]{'"p";"p1", "p2"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%3"."spread"[]{"decide"[]{(('"eq" '"p2") '"q2");"x"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}};"%5", "%6".('"%6" "pair"[]{"spread"[]{(('"a1" '"p1") '"q1");"%4", "%5".('"%4" "it"[]{})};"spread"[]{(('"b1" '"p2") '"q2");"%4", "%5".('"%4" "it"[]{})}})}};"lambda"[]{"%3"."spread"[]{"spread"[]{"decide"[]{(('"eq" '"p2") '"q2");"x"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{(('"e1" '"p1") '"q1");"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}};"%5", "%6".('"%5" '"%3")};"%1", "%2"."it"[]{}}}}}}}}}}


interactive nuprl_prod__deq__aux_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("prod-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} in "all"[]{"prod"[]{'"A";"".'"B"};"p"."all"[]{"prod"[]{'"A";"".'"B"};"q"."iff"[]{"equal"[]{"prod"[]{'"A";"".'"B"};'"p";'"q"};"assert"[]{(("proddeq"[]{'"a";'"b"} '"p") '"q")}}}}) }

define unfold_prod__deq : "prod-deq"[]{'"A";'"B";'"a";'"b"} <-->
      (((("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"p"."lambda"[]{"q"."spread"[]{'"q";"q1", "q2"."spread"[]{'"p";"p1", "p2"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1".("lambda"[]{"%1".('"%1" "pair"[]{"lambda"[]{"%"."pair"[]{("lambda"[]{"%1"."spread"[]{(('"%1" '"p1") '"q1");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} "it"[]{})))}} '"a1");("lambda"[]{"%1"."spread"[]{(('"%1" '"p2") '"q2");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} "it"[]{})))}} '"b1")}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."it"[]{}}}})} ("lambda"[]{"%1"."spread"[]{'"%1";"%2", "%3".'"%3"}} ("lambda"[]{"%1".(((((('"%1" "equal"[]{"prod"[]{'"A";"".'"B"};"pair"[]{'"p1";'"p2"};"pair"[]{'"q1";'"q2"}}) "equal"[]{"prod"[]{'"A";"".'"B"};"pair"[]{'"p1";'"p2"};"pair"[]{'"q1";'"q2"}}) "assert"[]{"band"[]{(('"e1" '"p1") '"q1");(('"eq" '"p2") '"q2")}}) "and"[]{"assert"[]{(('"e1" '"p1") '"q1")};"assert"[]{(('"eq" '"p2") '"q2")}}) ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."pair"[]{"lambda"[]{"%2".'"%2"};"lambda"[]{"%2".'"%2"}}} "it"[]{}))) ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".(('"%1" (('"e1" '"p1") '"q1")) (('"eq" '"p2") '"q2"))} "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"it"[]{}}};"lambda"[]{"%"."it"[]{}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"it"[]{}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%1"}}}}};"y"."decide"[]{'"p";"x"."pair"[]{"lambda"[]{"%"."pair"[]{"it"[]{};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}};"y"."pair"[]{"lambda"[]{"%"."pair"[]{"any"[]{'"%"};"any"[]{'"%"}}};"lambda"[]{"%"."spread"[]{'"%";"%1", "%2"."any"[]{'"%2"}}}}}}}})))} "lambda"[]{"P1"."lambda"[]{"P2"."lambda"[]{"Q1"."lambda"[]{"Q2"."lambda"[]{"%"."lambda"[]{"%1"."pair"[]{"lambda"[]{"%2"."pair"[]{"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%")))}} '"%2")))}} '"%1")};"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%1")))}} '"%2")))}} '"%")}}};"lambda"[]{"%2"."pair"[]{"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%")))}} '"%2")))}} '"%1")};"lambda"[]{"%3".("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%6" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4"."spread"[]{'"%4";"%5", "%6".('"%5" ("lambda"[]{"%4".'"%4"} ("lambda"[]{"%4".'"%4"} '"%3")))}} '"%1")))}} '"%2")))}} '"%")}}}}}}}}}})))}}}}}}}}}} '"A") '"B") '"a") '"b")


interactive nuprl_prod__deq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("prod-deq"[]{'"A";'"B";'"a";'"b"} in "all"[]{"prod"[]{'"A";"".'"B"};"p"."all"[]{"prod"[]{'"A";"".'"B"};"q"."iff"[]{"equal"[]{"prod"[]{'"A";"".'"B"};'"p";'"q"};"assert"[]{(("proddeq"[]{'"a";'"b"} '"p") '"q")}}}}) }

define unfold_product__deq : "product-deq"[]{'"A";'"B";'"a";'"b"} <-->
      "pair"[]{"proddeq"[]{'"a";'"b"};"prod-deq"[]{'"A";'"B";'"a";'"b"}}


interactive nuprl_product__deq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("product-deq"[]{'"A";'"B";'"a";'"b"} in "deq"[]{"prod"[]{'"A";"".'"B"}}) }

define unfold_sumdeq : "sumdeq"[]{'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"p";"pa"."decide"[]{'"q";"qa".(("fst"[]{'"a"} '"pa") '"qa");"qb"."bfalse"[]{}};"pb"."decide"[]{'"q";"qa"."bfalse"[]{};"qb".(("fst"[]{'"b"} '"pb") '"qb")}}}}


interactive nuprl_sumdeq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("sumdeq"[]{'"a";'"b"} in "fun"[]{"union"[]{'"A";'"B"};""."fun"[]{"union"[]{'"A";'"B"};""."bool"[]{}}}) }

interactive nuprl_sumdeq__property   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   [wf] sequent { <H> >- '"p" in "union"[]{'"A";'"B"} }  -->
   [wf] sequent { <H> >- '"q" in "union"[]{'"A";'"B"} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"union"[]{'"A";'"B"};'"p";'"q"};"assert"[]{(("sumdeq"[]{'"a";'"b"} '"p") '"q")}} }

define unfold_sum__deq__aux : "sum-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} <-->
      "lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."spread"[]{(('"a1" '"x1") '"x");"%4", "%5".('"%4" "it"[]{})}};"lambda"[]{"%"."it"[]{}}}}};"y"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."any"[]{"any"[]{"any"[]{"it"[]{}}}}};"lambda"[]{"%"."it"[]{}}}}}};"y"."decide"[]{'"p";"x"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."any"[]{"any"[]{"any"[]{"it"[]{}}}}};"lambda"[]{"%"."it"[]{}}}}};"y1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%"."spread"[]{(('"b1" '"y1") '"y");"%4", "%5".('"%4" "it"[]{})}};"lambda"[]{"%"."it"[]{}}}}}}}}}


interactive nuprl_sum__deq__aux_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("sum-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} in "all"[]{"union"[]{'"A";'"B"};"p"."all"[]{"union"[]{'"A";'"B"};"q"."iff"[]{"equal"[]{"union"[]{'"A";'"B"};'"p";'"q"};"assert"[]{(("sumdeq"[]{'"a";'"b"} '"p") '"q")}}}}) }

define unfold_sum__deq : "sum-deq"[]{'"A";'"B";'"a";'"b"} <-->
      (((("lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"p"."lambda"[]{"q"."decide"[]{'"q";"x"."decide"[]{'"p";"x1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."spread"[]{(('"%1" '"x1") '"x");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"x1")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"x1"."lambda"[]{"x"."lambda"[]{"%".("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".("lambda"[]{"%2"."it"[]{}} "it"[]{})} '"%"))}}}}})))))))}} '"a1")};"lambda"[]{"%"."it"[]{}}}}};"y"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."any"[]{('"%1" "it"[]{})}} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"y"."lambda"[]{"x"."lambda"[]{"%".("lambda"[]{"%1"."decide"[]{'"%1";"%2"."any"[]{'"%2"};"%3".("lambda"[]{"%4"."any"[]{'"%4"}} ("lambda"[]{"%4".("lambda"[]{"%5".("lambda"[]{"%6"."any"[]{'"%6"}} "it"[]{})} "it"[]{})} '"%"))}} ("lambda"[]{"%1".'"%1"} "inr"[]{"lambda"[]{"%"."it"[]{}}}))}}}}})))))};"lambda"[]{"%"."it"[]{}}}}}};"y"."decide"[]{'"p";"x"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."any"[]{('"%1" "it"[]{})}} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"x")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"x"."lambda"[]{"y"."lambda"[]{"%".("lambda"[]{"%1"."decide"[]{'"%1";"%2"."any"[]{'"%2"};"%3".("lambda"[]{"%4"."any"[]{'"%4"}} ("lambda"[]{"%4".("lambda"[]{"%5".("lambda"[]{"%6"."any"[]{'"%6"}} "it"[]{})} "it"[]{})} '"%"))}} ("lambda"[]{"%1".'"%1"} "inr"[]{"lambda"[]{"%"."it"[]{}}}))}}}}})))))};"lambda"[]{"%"."it"[]{}}}}};"y1"."spread"[]{'"b";"eq", "b1"."spread"[]{'"a";"e1", "a1"."pair"[]{"lambda"[]{"%".("lambda"[]{"%1"."spread"[]{(('"%1" '"y1") '"y");"%4", "%5".('"%4" ("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1"."it"[]{}} ("lambda"[]{"%1".('"%1" '"y")} ("lambda"[]{"%1".('"%1" '"y1")} ("lambda"[]{"%1".('"%1" '"B")} ("lambda"[]{"%1".('"%1" '"A")} "lambda"[]{"A"."lambda"[]{"B"."lambda"[]{"y1"."lambda"[]{"y"."lambda"[]{"%".("lambda"[]{"%1".'"%1"} ("lambda"[]{"%1".("lambda"[]{"%2"."it"[]{}} "it"[]{})} '"%"))}}}}})))))))}} '"b1")};"lambda"[]{"%"."it"[]{}}}}}}}}}}}}} '"A") '"B") '"a") '"b")


interactive nuprl_sum__deq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("sum-deq"[]{'"A";'"B";'"a";'"b"} in "all"[]{"union"[]{'"A";'"B"};"p"."all"[]{"union"[]{'"A";'"B"};"q"."iff"[]{"equal"[]{"union"[]{'"A";'"B"};'"p";'"q"};"assert"[]{(("sumdeq"[]{'"a";'"b"} '"p") '"q")}}}}) }

interactive nuprl_subtype__deq   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H>; "x": '"A" ; "y": '"A" ; "equal"[]{'"B";'"x";'"y"}  >- "equal"[]{'"A";'"x";'"y"} }  -->
   sequent { <H> >- "subtype"[]{"deq"[]{'"B"};"deq"[]{'"A"}} }

interactive nuprl_subtype_rel__deq   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "subtype"[]{'"A";'"B"} }  -->
   sequent { <H>; "x": '"A" ; "y": '"A" ; "equal"[]{'"B";'"x";'"y"}  >- "equal"[]{'"A";'"x";'"y"} }  -->
   sequent { <H> >- "subtype"[]{"deq"[]{'"B"};"deq"[]{'"A"}} }

define unfold_union__deq : "union-deq"[]{'"A";'"B";'"a";'"b"} <-->
      "pair"[]{"sumdeq"[]{'"a";'"b"};"sum-deq"[]{'"A";'"B";'"a";'"b"}}


interactive nuprl_union__deq_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"a" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"b" in "deq"[]{'"B"} }  -->
   sequent { <H> >- ("union-deq"[]{'"A";'"B";'"a";'"b"} in "deq"[]{"union"[]{'"A";'"B"}}) }

define unfold_deq__member : "deq-member"[]{'"eq";'"x";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"b"."bor"[]{(("eqof"[]{'"eq"} '"a") '"x");'"b"}}};"bfalse"[]{};'"L"}


interactive nuprl_deq__member_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- ("deq-member"[]{'"eq";'"x";'"L"} in "bool"[]{}) }

interactive nuprl_assert__deq__member   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"deq-member"[]{'"eq";'"x";'"L"}};"mem"[]{'"x";'"L";'"A"}} }

define unfold_discrete_struct : "discrete_struct"[level:l]{'"A"} <-->
      "prod"[]{"fun"[]{'"A";""."univ"[level:l]{}};"sort"."fun"[]{'"A";"a"."deq"[]{('"sort" '"a")}}}


interactive nuprl_discrete_struct_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("discrete_struct"[level:l]{'"A"} in "univ"[level':l]{}) }

interactive nuprl_discrete_struct_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   sequent { <H> >- "type"{"discrete_struct"[level:l]{'"A"}} }

define unfold_dstype : "dstype"[]{'"TypeNames";'"d";'"a"} <-->
      ("fst"[]{'"d"} '"a")


interactive nuprl_dstype_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"TypeNames" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"TypeNames"} }  -->
   [wf] sequent { <H> >- '"a" in '"TypeNames" }  -->
   sequent { <H> >- ("dstype"[]{'"TypeNames";'"d";'"a"} in "univ"[level:l]{}) }

interactive nuprl_dstype_wf_type {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"TypeNames" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"TypeNames"} }  -->
   [wf] sequent { <H> >- '"a" in '"TypeNames" }  -->
   sequent { <H> >- "type"{"dstype"[]{'"TypeNames";'"d";'"a"}} }

interactive nuprl_decidable__dstype_equal univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in "dstype"[]{'"A";'"d";'"a"} }  -->
   [wf] sequent { <H> >- '"y" in "dstype"[]{'"A";'"d";'"a"} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"dstype"[]{'"A";'"d";'"a"};'"x";'"y"}} }

define unfold_dsdeq : "dsdeq"[]{'"d";'"a"} <-->
      ("snd"[]{'"d"} '"a")


interactive nuprl_dsdeq_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"A"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- ("dsdeq"[]{'"d";'"a"} in "deq"[]{"dstype"[]{'"A";'"d";'"a"}}) }

define unfold_dseq : "dseq"[]{'"d";'"a"} <-->
      "eqof"[]{("snd"[]{'"d"} '"a")}


interactive nuprl_dseq_wf {| intro[] |} univ[level:l]  :
   [wf] sequent { <H> >- '"TypeNames" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"TypeNames"} }  -->
   [wf] sequent { <H> >- '"a" in '"TypeNames" }  -->
   sequent { <H> >- ("dseq"[]{'"d";'"a"} in "fun"[]{"dstype"[]{'"TypeNames";'"d";'"a"};""."fun"[]{"dstype"[]{'"TypeNames";'"d";'"a"};""."bool"[]{}}}) }

define unfold_eq_ds : "eq_ds"[]{'"d";'"a";'"x";'"y"} <-->
      (("dseq"[]{'"d";'"a"} '"x") '"y")


interactive nuprl_eq_ds_wf {| intro[] |} univ[level:l] '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"A"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"x" in "dstype"[]{'"A";'"d";'"a"} }  -->
   [wf] sequent { <H> >- '"y" in "dstype"[]{'"A";'"d";'"a"} }  -->
   sequent { <H> >- ("eq_ds"[]{'"d";'"a";'"x";'"y"} in "bool"[]{}) }

interactive nuprl_ds_property univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "discrete_struct"[level:l]{'"A"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"x" in "dstype"[]{'"A";'"d";'"a"} }  -->
   [wf] sequent { <H> >- '"y" in "dstype"[]{'"A";'"d";'"a"} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"equal"[]{"dstype"[]{'"A";'"d";'"a"};'"x";'"y"};"assert"[]{"eq_ds"[]{'"d";'"a";'"x";'"y"}}}} }

define unfold_insert : "insert"[]{'"eq";'"a";'"L"} <-->
      "ifthenelse"[]{"deq-member"[]{'"eq";'"a";'"L"};'"L";"cons"[]{'"a";'"L"}}


interactive nuprl_insert_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("insert"[]{'"eq";'"a";'"L"} in "list"[]{'"T"}) }

interactive nuprl_insert_property   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"a" in '"T" }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "and"[]{"all"[]{'"T";"b"."iff"[]{"mem"[]{'"b";"insert"[]{'"eq";'"a";'"L"};'"T"};"or"[]{"equal"[]{'"T";'"b";'"a"};"mem"[]{'"b";'"L";'"T"}}}};"implies"[]{"no_repeats"[]{'"T";'"L"};"no_repeats"[]{'"T";"insert"[]{'"eq";'"a";'"L"}}}} }

define unfold_remove__repeats : "remove-repeats"[]{'"eq";'"L"} <-->
      "reduce"[]{"lambda"[]{"a"."lambda"[]{"L"."insert"[]{'"eq";'"a";'"L"}}};"nil"[]{};'"L"}


interactive nuprl_remove__repeats_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- ("remove-repeats"[]{'"eq";'"L"} in "list"[]{'"T"}) }

interactive nuprl_remove__repeats_property   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   sequent { <H> >- "and"[]{"no_repeats"[]{'"T";"remove-repeats"[]{'"eq";'"L"}};"all"[]{'"T";"a"."iff"[]{"mem"[]{'"a";"remove-repeats"[]{'"eq";'"L"};'"T"};"mem"[]{'"a";'"L";'"T"}}}} }

define unfold_id__deq : "id-deq"[]{} <-->
      "product-deq"[]{"atom"[]{};"nat"[]{};"atom-deq"[]{};"nat-deq"[]{}}


interactive nuprl_id__deq_wf {| intro[] |}   :
   sequent { <H> >- ("id-deq"[]{} in "deq"[]{"Id"[]{}}) }

define unfold_eq_id : "eq_id"[]{'"a";'"b"} <-->
      (("eqof"[]{"id-deq"[]{}} '"a") '"b")


interactive nuprl_eq_id_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Id"[]{} }  -->
   sequent { <H> >- ("eq_id"[]{'"a";'"b"} in "bool"[]{}) }

interactive_rw nuprl_eq_id_self   :
   ('"a" in "Id"[]{}) -->
   "eq_id"[]{'"a";'"a"} <--> "btrue"[]{}

interactive nuprl_assert__eq__id   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"eq_id"[]{'"a";'"b"}};"equal"[]{"Id"[]{};'"a";'"b"}} }

interactive nuprl_decidable__equal_Id   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Id"[]{} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"Id"[]{};'"a";'"b"}} }

define unfold_idlnk__deq : "idlnk-deq"[]{} <-->
      "product-deq"[]{"Id"[]{};"prod"[]{"Id"[]{};""."nat"[]{}};"id-deq"[]{};"product-deq"[]{"Id"[]{};"nat"[]{};"id-deq"[]{};"nat-deq"[]{}}}


interactive nuprl_idlnk__deq_wf {| intro[] |}   :
   sequent { <H> >- ("idlnk-deq"[]{} in "deq"[]{"IdLnk"[]{}}) }

define unfold_eq_lnk : "eq_lnk"[]{'"a";'"b"} <-->
      (("eqof"[]{"idlnk-deq"[]{}} '"a") '"b")


interactive nuprl_eq_lnk_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "IdLnk"[]{} }  -->
   sequent { <H> >- ("eq_lnk"[]{'"a";'"b"} in "bool"[]{}) }

interactive nuprl_assert__eq__lnk   :
   [wf] sequent { <H> >- '"a" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "IdLnk"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"eq_lnk"[]{'"a";'"b"}};"equal"[]{"IdLnk"[]{};'"a";'"b"}} }

interactive nuprl_decidable__equal_IdLnk   :
   [wf] sequent { <H> >- '"a" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "IdLnk"[]{} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"IdLnk"[]{};'"a";'"b"}} }

interactive nuprl_lconnects__transitive  '"j" '"p" '"q"  :
   [wf] sequent { <H> >- '"p" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"q" in "list"[]{"IdLnk"[]{}} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Id"[]{} }  -->
   sequent { <H> >- "lconnects"[]{'"p";'"i";'"j"} }  -->
   sequent { <H> >- "lconnects"[]{'"q";'"j";'"k"} }  -->
   sequent { <H> >- "exists"[]{"list"[]{"IdLnk"[]{}};"r"."lconnects"[]{'"r";'"i";'"k"}} }

interactive nuprl_decidable__l_member   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H>; "x": '"A" ; "y": '"A"  >- "decidable"[]{"equal"[]{'"A";'"x";'"y"}} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   sequent { <H> >- "decidable"[]{"mem"[]{'"x";'"L";'"A"}} }

define unfold_Kind__deq : "Kind-deq"[]{} <-->
      "union-deq"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"Id"[]{};"product-deq"[]{"IdLnk"[]{};"Id"[]{};"idlnk-deq"[]{};"id-deq"[]{}};"id-deq"[]{}}


interactive nuprl_Kind__deq_wf {| intro[] |}   :
   sequent { <H> >- ("Kind-deq"[]{} in "deq"[]{"Knd"[]{}}) }

define unfold_eq_knd : "eq_knd"[]{'"a";'"b"} <-->
      (("eqof"[]{"Kind-deq"[]{}} '"a") '"b")


interactive nuprl_eq_knd_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Knd"[]{} }  -->
   sequent { <H> >- ("eq_knd"[]{'"a";'"b"} in "bool"[]{}) }

interactive nuprl_assert__eq__knd   :
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Knd"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"eq_knd"[]{'"a";'"b"}};"equal"[]{"Knd"[]{};'"a";'"b"}} }

interactive nuprl_decidable__equal_Kind   :
   [wf] sequent { <H> >- '"a" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "Knd"[]{} }  -->
   sequent { <H> >- "decidable"[]{"equal"[]{"Knd"[]{};'"a";'"b"}} }

interactive nuprl_map__concat__filter__lemma1  '"B" '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{'"A";""."fun"[]{'"B";""."list"[]{"top"[]{}}}}}} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"prod"[]{"top"[]{};""."prod"[]{"Id"[]{};""."top"[]{}}}} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}};"map"[]{"lambda"[]{"x"."snd"[]{'"x"}};'"L"};"concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"a") '"b")}};'"L2"}}};"implies"[]{"not"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"L2"};"Id"[]{}}};"equal"[]{"list"[]{"prod"[]{"top"[]{};""."prod"[]{"Id"[]{};""."top"[]{}}}};"filter"[]{"lambda"[]{"ms"."eq_id"[]{"fst"[]{"snd"[]{'"ms"}};'"tg"}};'"L"};"nil"[]{}}}}} }

interactive nuprl_map__concat__filter__lemma2  "lambda"[]{"x".'"C"['"x"]} '"B" '"A" '"tg" '"L2" '"b" '"a" '"L"  :
   [wf] sequent { <H>;"x": "Id"[]{} >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L2" in "list"[]{"prod"[]{"Id"[]{};"tg"."fun"[]{'"A";""."fun"[]{'"B";""."list"[]{'"C"['"tg"]}}}}} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"prod"[]{"IdLnk"[]{};"l"."prod"[]{"Id"[]{};"t".'"C"['"t"]}}} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"b" in '"B" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"equal"[]{"list"[]{"prod"[]{"Id"[]{};"tg".'"C"['"tg"]}};"map"[]{"lambda"[]{"x"."snd"[]{'"x"}};'"L"};"concat"[]{"map"[]{"lambda"[]{"tgf"."map"[]{"lambda"[]{"x"."pair"[]{"fst"[]{'"tgf"};'"x"}};(("snd"[]{'"tgf"} '"a") '"b")}};'"L2"}}};"implies"[]{"not"[]{"mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"L2"};"Id"[]{}}};"equal"[]{"int"[]{};"length"[]{"filter"[]{"lambda"[]{"ms"."eq_id"[]{"fst"[]{"snd"[]{'"ms"}};'"tg"}};'"L"}};"number"[0:n]{}}}}} }

define unfold_standard__ds : "standard-ds"[]{} <-->
      "pair"[]{"lambda"[]{"a"."ifthenelse"[]{"beq_int"[]{'"a";"number"[2:n]{}};"IdLnk"[]{};"Id"[]{}}};"lambda"[]{"a"."ifthenelse"[]{"beq_int"[]{'"a";"number"[2:n]{}};"idlnk-deq"[]{};"id-deq"[]{}}}}


interactive nuprl_standard__ds_wf {| intro[] |}   :
   sequent { <H> >- ("standard-ds"[]{} in "discrete_struct"[level:l]{"int_seg"[]{"number"[1:n]{};"number"[6:n]{}}}) }

define unfold_l_index : "l_index"[]{'"dT";'"L";'"x"} <-->
      "mu"[]{"lambda"[]{"i".(("eqof"[]{'"dT"} '"x") "select"[]{'"i";'"L"})}}


interactive nuprl_l_index_wf {| intro[] |}  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"dT" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- ("l_index"[]{'"dT";'"L";'"x"} in "int_seg"[]{"number"[0:n]{};"length"[]{'"L"}}) }

interactive nuprl_select_l_index   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"dT" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "equal"[]{'"T";"select"[]{"l_index"[]{'"dT";'"L";'"x"};'"L"};'"x"} }

interactive nuprl_l_before_l_index  '"dT"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"dT" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"y";'"L";'"T"} }  -->
   sequent { <H> >- "lt"[]{"l_index"[]{'"dT";'"L";'"x"};"l_index"[]{'"dT";'"L";'"y"}} }  -->
   sequent { <H> >- "l_before"[]{'"x";'"y";'"L";'"T"} }

interactive nuprl_l_before_l_index_le  '"dT"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"dT" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "mem"[]{'"x";'"L";'"T"} }  -->
   sequent { <H> >- "mem"[]{'"y";'"L";'"T"} }  -->
   sequent { <H> >- "le"[]{"l_index"[]{'"dT";'"L";'"x"};"l_index"[]{'"dT";'"L";'"y"}} }  -->
   sequent { <H> >- "or"[]{"l_before"[]{'"x";'"y";'"L";'"T"};"equal"[]{'"T";'"x";'"y"}} }

define unfold_has__src : "has-src"[]{'"i";'"k"} <-->
      "band"[]{"isrcv"[]{'"k"};"eq_id"[]{"lsrc"[]{"lnk"[]{'"k"}};'"i"}}


interactive nuprl_has__src_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- ("has-src"[]{'"i";'"k"} in "bool"[]{}) }

interactive nuprl_assert__has__src   :
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"has-src"[]{'"i";'"k"}};"cand"[]{"assert"[]{"isrcv"[]{'"k"}};"equal"[]{"Id"[]{};"lsrc"[]{"lnk"[]{'"k"}};'"i"}}} }


(**** display forms ****)


dform nuprl_deq_df : except_mode[src] :: "deq"[]{'"T"} =
   `"EqDecider(" slot{'"T"} `")"


dform nuprl_eqof_df : except_mode[src] :: "eqof"[]{'"d"} =
   `"eqof(" slot{'"d"} `")"


dform nuprl_nat__deq_df : except_mode[src] :: "nat-deq"[]{} =
   `"NatDeq"


dform nuprl_atom__deq_df : except_mode[src] :: "atom-deq"[]{} =
   `"AtomDeq"


dform nuprl_proddeq_df : except_mode[src] :: "proddeq"[]{'"a";'"b"} =
   `"proddeq(" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_prod__deq__aux_df : except_mode[src] :: "prod-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} =
   `"prod-deq-aux{v:l,i:l}(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";"
    slot{'"b"} `")"


dform nuprl_prod__deq_df : except_mode[src] :: "prod-deq"[]{'"A";'"B";'"a";'"b"} =
   `"prod-deq(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_product__deq_df : except_mode[src] :: "product-deq"[]{'"A";'"B";'"a";'"b"} =
   `"product-deq(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_sumdeq_df : except_mode[src] :: "sumdeq"[]{'"a";'"b"} =
   `"sumdeq(" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_sum__deq__aux_df : except_mode[src] :: "sum-deq-aux"[v:l,level:l]{'"A";'"B";'"a";'"b"} =
   `"sum-deq-aux{v:l,i:l}(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";"
    slot{'"b"} `")"


dform nuprl_sum__deq_df : except_mode[src] :: "sum-deq"[]{'"A";'"B";'"a";'"b"} =
   `"sum-deq(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_union__deq_df : except_mode[src] :: "union-deq"[]{'"A";'"B";'"a";'"b"} =
   `"union-deq(" slot{'"A"} `";" slot{'"B"} `";" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_deq__member_df : except_mode[src] :: "deq-member"[]{'"eq";'"x";'"L"} =
   `"deq-member(" slot{'"eq"} `";" slot{'"x"} `";" slot{'"L"} `")"


dform nuprl_discrete_struct_df : except_mode[src] :: "discrete_struct"[level:l]{'"A"} =
   `"DS(" slot{'"A"} `")"


dform nuprl_dstype_df : except_mode[src] :: "dstype"[]{'"TypeNames";'"d";'"a"} =
   `"dstype(" slot{'"TypeNames"} `";" slot{'"d"} `";" slot{'"a"} `")"

dform nuprl_dstype_df : except_mode[src] :: '"d" =
   `"E"

dform nuprl_dstype_df : except_mode[src] :: '"d" =
   `"E"

dform nuprl_dstype_df : except_mode[src] :: "dstype"[]{"int_seg"[]{"number"[0:n]{};"number"[4:n]{}};'"d";"number"[0:n]{}} =
   `"E"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Loc"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Loc"

dform nuprl_dstype_df : except_mode[src] :: "dstype"[]{"int_seg"[]{"number"[0:n]{};"number"[4:n]{}};'"d";"number"[1:n]{}} =
   `"Loc"

dform nuprl_dstype_df : except_mode[src] :: "IdLnk"[]{} =
   `"Lnk"

dform nuprl_dstype_df : except_mode[src] :: "IdLnk"[]{} =
   `"Lnk"

dform nuprl_dstype_df : except_mode[src] :: "dstype"[]{"int_seg"[]{"number"[0:n]{};"number"[4:n]{}};'"d";"number"[2:n]{}} =
   `"Lnk"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"X"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"X"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"A"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Tag"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Loc"

dform nuprl_dstype_df : except_mode[src] :: "IdLnk"[]{} =
   `"Lnk"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"X"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"A"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Tag"

dform nuprl_dstype_df : except_mode[src] :: "IdLnk"[]{} =
   `"Lnk"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"X"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"A"

dform nuprl_dstype_df : except_mode[src] :: "Id"[]{} =
   `"Tag"


dform nuprl_dsdeq_df : except_mode[src] :: "dsdeq"[]{'"d";'"a"} =
   `"dsdeq(" slot{'"d"} `";" slot{'"a"} `")"


dform nuprl_dseq_df : except_mode[src] :: "dseq"[]{'"d";'"a"} =
   `"dseq(" slot{'"d"} `";" slot{'"a"} `")"


dform nuprl_eq_ds_df : except_mode[src] :: "eq_ds"[]{'"d";'"a";'"x";'"y"} =
   `"" slot{'"x"} `" = " slot{'"y"} `""


dform nuprl_insert_df : except_mode[src] :: "insert"[]{'"eq";'"a";'"L"} =
   `"insert(" slot{'"a"} `";" slot{'"L"} `")"


dform nuprl_remove__repeats_df : except_mode[src] :: "remove-repeats"[]{'"eq";'"L"} =
   `"remove-repeats(" slot{'"eq"} `";" slot{'"L"} `")"


dform nuprl_id__deq_df : except_mode[src] :: "id-deq"[]{} =
   `"IdDeq"


dform nuprl_eq_id_df : except_mode[src] :: "eq_id"[]{'"a";'"b"} =
   `"" slot{'"a"} `" = " slot{'"b"} `""


dform nuprl_idlnk__deq_df : except_mode[src] :: "idlnk-deq"[]{} =
   `"IdLnkDeq"


dform nuprl_eq_lnk_df : except_mode[src] :: "eq_lnk"[]{'"a";'"b"} =
   `"" slot{'"a"} `" = " slot{'"b"} `""


dform nuprl_Kind__deq_df : except_mode[src] :: "Kind-deq"[]{} =
   `"KindDeq"


dform nuprl_eq_knd_df : except_mode[src] :: "eq_knd"[]{'"a";'"b"} =
   `"" slot{'"a"} `" = " slot{'"b"} `""


dform nuprl_standard__ds_df : except_mode[src] :: "standard-ds"[]{} =
   `"StandardDS"


dform nuprl_l_index_df : except_mode[src] :: "l_index"[]{'"dT";'"L";'"x"} =
   `"index(" slot{'"L"} `";" slot{'"x"} `")"


dform nuprl_has__src_df : except_mode[src] :: "has-src"[]{'"i";'"k"} =
   `"has-src(" slot{'"i"} `";" slot{'"k"} `")"


