extends Ma_event__systems

open Dtactic


define unfold_fpf : "fpf"[]{'"A";"a".'"B"['"a"]} <-->
      "prod"[]{"list"[]{'"A"};"d"."fun"[]{"set"[]{'"A";"a"."mem"[]{'"a";'"d";'"A"}};"a".'"B"['"a"]}}


interactive nuprl_fpf_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("fpf"[]{'"A";"a".'"B"['"a"]} in "univ"[level:l]{}) }

interactive nuprl_fpf_wf_type {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   sequent { <H> >- "type"{"fpf"[]{'"A";"a".'"B"['"a"]}} }

interactive nuprl_subtype__fpf  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"P"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   sequent { <H> >- "subtype"[]{"fpf"[]{"set"[]{'"A";"a".'"P"['"a"]};"a".'"B"['"a"]};"fpf"[]{'"A";"a".'"B"['"a"]}} }

interactive nuprl_subtype__fpf2  '"A" "lambda"[]{"x".'"B2"['"x"]} "lambda"[]{"x".'"B1"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B1"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B2"['"x"] } }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B1"['"a"];'"B2"['"a"]} }  -->
   sequent { <H> >- "subtype"[]{"fpf"[]{'"A";"a".'"B1"['"a"]};"fpf"[]{'"A";"a".'"B2"['"a"]}} }

interactive nuprl_subtype__fpf3  '"A1" '"A2" "lambda"[]{"x".'"B2"['"x"]} "lambda"[]{"x".'"B1"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A1" } }  -->
   [wf] sequent { <H> >- "type"{'"A2" } }  -->
   [wf] sequent { <H>;"x": '"A1" >- "type"{'"B1"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A2" >- "type"{'"B2"['"x"] } }  -->
   sequent { <H> >- "subset"[]{'"A1";'"A2"} }  -->
   sequent { <H>; "a": '"A1"  >- "subtype"[]{'"B1"['"a"];'"B2"['"a"]} }  -->
   sequent { <H> >- "subtype"[]{"fpf"[]{'"A1";"a".'"B1"['"a"]};"fpf"[]{'"A2";"a".'"B2"['"a"]}} }

define unfold_fpf__dom : "fpf-dom"[]{'"eq";'"x";'"f"} <-->
      "deq-member"[]{'"eq";'"x";"fst"[]{'"f"}}


interactive nuprl_fpf__dom_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- ("fpf-dom"[]{'"eq";'"x";'"f"} in "bool"[]{}) }

interactive nuprl_fpf__trivial__subtype__set  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{"set"[]{'"A";"a".'"P"['"a"]};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- ('"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}}) }

interactive nuprl_fpf__trivial__subtype__top  "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- ('"f" in "fpf"[]{'"A";"a"."top"[]{}}) }

interactive nuprl_fpf__dom_functionality  '"A" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"fpf-dom"[]{'"eq1";'"x";'"f"};"fpf-dom"[]{'"eq2";'"x";'"f"}} }

interactive nuprl_fpf__dom_functionality2  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"assert"[]{"fpf-dom"[]{'"eq2";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq1";'"x";'"f"}}}} }

interactive nuprl_fpf__dom__type  '"Y" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"X" } }  -->
   [wf] sequent { <H> >- "type"{'"Y" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"Y"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"Y" }  -->
   sequent { <H> >- "subset"[]{'"X";'"Y"} }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}} }  -->
   sequent { <H> >- ('"x" in '"X") }

interactive nuprl_fpf__dom__type2  '"Y"  :
   [wf] sequent { <H> >- "type"{'"X" } }  -->
   [wf] sequent { <H> >- "type"{'"Y" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"Y"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"Y" }  -->
   sequent { <H> >- "subset"[]{'"X";'"Y"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};('"x" in '"X")}} }

define unfold_fpf__empty : "fpf-empty"[]{} <-->
      "pair"[]{"nil"[]{};"lambda"[]{"x"."it"[]{}}}


interactive nuprl_fpf__empty_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   sequent { <H> >- ("fpf-empty"[]{} in "fpf"[]{'"A";"x".'"B"['"x"]}) }

define unfold_fpf__is__empty : "fpf-is-empty"[]{'"f"} <-->
      "beq_int"[]{"length"[]{"fst"[]{'"f"}};"number"[0:n]{}}


interactive nuprl_fpf__is__empty_wf {| intro[] |}  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x"."top"[]{}} }  -->
   sequent { <H> >- ("fpf-is-empty"[]{'"f"} in "bool"[]{}) }

interactive nuprl_assert__fpf__is__empty  '"A" "lambda"[]{"x".'"B"['"x"]} '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x".'"B"['"x"]} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-is-empty"[]{'"f"}};"equal"[]{"fpf"[]{'"A";"x".'"B"['"x"]};'"f";"fpf-empty"[]{}}} }

define unfold_fpf__ap : "fpf-ap"[]{'"f";'"eq";'"x"} <-->
      ("snd"[]{'"f"} '"x")


interactive nuprl_fpf__ap_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"x" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}} }  -->
   sequent { <H> >- ("fpf-ap"[]{'"f";'"eq";'"x"} in '"B"['"x"]) }

interactive_rw nuprl_fpf__ap_functionality  '"eq1"  :
   "fpf-ap"[]{'"f";'"eq2";'"x"} <--> "fpf-ap"[]{'"f";'"eq1";'"x"}

define unfold_fpf__cap : "fpf-cap"[]{'"f";'"eq";'"x";'"z"} <-->
      "ifthenelse"[]{"fpf-dom"[]{'"eq";'"x";'"f"};"fpf-ap"[]{'"f";'"eq";'"x"};'"z"}


interactive nuprl_fpf__cap__wf__univ  '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("fpf-cap"[]{'"f";'"eq";'"x";'"z"} in "univ"[level:l]{}) }

interactive nuprl_fpf__cap__wf__univ_type univ[level:l] '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in "univ"[level:l]{} }  -->
   sequent { <H> >- "type"{"fpf-cap"[]{'"f";'"eq";'"x";'"z"}} }

interactive nuprl_fpf__cap_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"x" '"z" '"eq" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B"['"x"] }  -->
   sequent { <H> >- ("fpf-cap"[]{'"f";'"eq";'"x";'"z"} in '"B"['"x"]) }

define unfold_fpf__val : "fpf-val"[]{'"eq";'"f";'"x";"a", "z".'"P"['"a";'"z"]} <-->
      "implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};'"P"['"x";"fpf-ap"[]{'"f";'"eq";'"x"}]}


interactive nuprl_fpf__val_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"eq" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"x"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H>;"a": "set"[]{'"A";"a"."assert"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}};"x": '"B"['"a"] >- '"P"['"a";'"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("fpf-val"[]{'"eq";'"f";'"x";"x", "z".'"P"['"x";'"z"]} in "univ"[level:l]{}) }

define unfold_fpf__sub : "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} <-->
      "all"[]{'"A";"x"."implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"cand"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}};"equal"[]{'"B"['"x"];"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}}}}


interactive nuprl_fpf__sub_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- ("fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} in "univ"[level:l]{}) }

interactive nuprl_fpf__empty__sub  '"g" '"eq" "lambda"[]{"x".'"B"['"x"]} '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";"fpf-empty"[]{};'"g"} }

interactive nuprl_fpf__sub__functionality  '"A'" '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"g" '"f" '"eq" '"eq'"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"A'" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A'"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A'" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq'" in "deq"[]{'"A'"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"C"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"C"['"a"];'"eq'";'"f";'"g"} }

interactive nuprl_fpf__sub__functionality2  '"A'" '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"g" '"f" '"eq" '"eq'"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"A'" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A'"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A'" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq'" in "deq"[]{'"A'"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"C"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A'";"a".'"C"['"a"];'"eq'";'"f";'"g"} }

interactive nuprl_fpf__sub_functionality  '"A'" '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"eq'" '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"A'" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A'"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A'" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq'" in "deq"[]{'"A'"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"C"['"a"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"};"fpf-sub"[]{'"A";"a".'"C"['"a"];'"eq'";'"f";'"g"}}} }

interactive nuprl_fpf__sub_functionality2  '"A'" '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"eq'" '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"A'" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A'"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A'" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eq'" in "deq"[]{'"A'"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"C"['"a"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"};"fpf-sub"[]{'"A'";"a".'"C"['"a"];'"eq'";'"f";'"g"}}} }

interactive nuprl_fpf__sub_transitivity  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq" '"h"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"h"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"h"} }

interactive nuprl_fpf__sub_weakening  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "equal"[]{"fpf"[]{'"A";"a".'"B"['"a"]};'"f";'"g"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }

interactive nuprl_subtype__fpf__cap univ[level:l]  :
   [wf] sequent { <H> >- '"X" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"X"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-sub"[]{'"X";"x"."univ"[level:l]{};'"eq";'"g";'"f"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{'"X";"x"."subtype"[]{"fpf-cap"[]{'"f";'"eq";'"x";"top"[]{}};"fpf-cap"[]{'"g";'"eq";'"x";"top"[]{}}}}} }

interactive nuprl_subtype__fpf__cap__top univ[level:l] '"X"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"X"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"X" }  -->
   sequent { <H> >- "fpf-sub"[]{'"X";"x"."univ"[level:l]{};'"eq";'"g";'"f"} }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{'"f";'"eq";'"x";'"T"};"fpf-cap"[]{'"g";'"eq";'"x";"top"[]{}}} }

interactive nuprl_fpf__cap__void__subtype univ[level:l] '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{'"A";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{'"ds";'"eq";'"x";"void"[]{}};"fpf-cap"[]{'"ds";'"eq";'"x";"top"[]{}}} }

interactive nuprl_subtype__fpf__cap__void univ[level:l] '"X"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"X" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"X"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"X" }  -->
   sequent { <H> >- "fpf-sub"[]{'"X";"x"."univ"[level:l]{};'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{'"f";'"eq";'"x";"void"[]{}};"fpf-cap"[]{'"g";'"eq";'"x";'"T"}} }

interactive nuprl_fpf__cap_functionality  '"A" "lambda"[]{"x".'"B"['"x"]} '"x" '"d2" '"z" '"d1" '"f"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"d1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B"['"x"] }  -->
   sequent { <H> >- "equal"[]{'"B"['"x"];"fpf-cap"[]{'"f";'"d1";'"x";'"z"};"fpf-cap"[]{'"f";'"d2";'"x";'"z"}} }

interactive nuprl_fpf__cap__subtype_functionality univ[level:l] '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in "univ"[level:l]{} }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{'"f";'"d1";'"x";'"z"};"fpf-cap"[]{'"f";'"d2";'"x";'"z"}} }

interactive nuprl_fpf__cap_functionality_wrt_sub  '"A" "lambda"[]{"x".'"B"['"x"]} '"x" '"g" '"f" '"d4" '"d3" '"d2" '"z" '"d1"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"d1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d3" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d4" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B"['"x"] }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"d4";'"f";'"g"} }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"d3";'"x";'"f"}} }  -->
   sequent { <H> >- "equal"[]{'"B"['"x"];"fpf-cap"[]{'"f";'"d1";'"x";'"z"};"fpf-cap"[]{'"g";'"d2";'"x";'"z"}} }

interactive nuprl_fpf__cap__subtype_functionality_wrt_sub   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d1" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d2" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"d4" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-sub"[]{'"A";"a"."univ"[level:l]{};'"d4";'"f";'"g"};"subtype"[]{"fpf-cap"[]{'"g";'"d1";'"x";"top"[]{}};"fpf-cap"[]{'"f";'"d2";'"x";"top"[]{}}}}} }

interactive nuprl_fpf__cap__subtype_functionality_wrt_sub2  '"A3" '"A1"  :
   [wf] sequent { <H> >- '"A1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"A3" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d" in "deq"[]{'"A3"} }  -->
   [wf] sequent { <H> >- '"d'" in "deq"[]{'"A3"} }  -->
   [wf] sequent { <H> >- '"d2" in "deq"[]{'"A2"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A1";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A2";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A3" }  -->
   sequent { <H> >- "subset"[]{'"A1";'"A2"} }  -->
   sequent { <H> >- "subset"[]{'"A2";'"A3"} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-sub"[]{'"A2";"a"."univ"[level:l]{};'"d2";'"f";'"g"};"subtype"[]{"fpf-cap"[]{'"g";'"d";'"x";"top"[]{}};"fpf-cap"[]{'"f";'"d'";'"x";"top"[]{}}}}} }

define unfold_fpf__compatible : "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} <-->
      "all"[]{'"A";"x"."implies"[]{"and"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}};"equal"[]{'"B"['"x"];"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}}}


interactive nuprl_fpf__compatible_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- ("fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} in "univ"[level:l]{}) }

interactive nuprl_fpf__compatible__wf2  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"C"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   sequent { <H>; "x": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}} ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}  >- "subtype"[]{'"B"['"x"];'"C"['"x"]} }  -->
   sequent { <H> >- ("fpf-compatible"[]{'"A";"a".'"C"['"a"];'"eq";'"f";'"g"} in "univ"[level:l]{}) }

interactive nuprl_fpf__sub__compatible__left  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }

interactive nuprl_fpf__sub__compatible__right  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"g" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"f"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }

interactive nuprl_subtype__fpf__cap5 univ[level:l] '"X"  :
   [wf] sequent { <H> >- '"X" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"X"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"X" }  -->
   sequent { <H> >- "fpf-compatible"[]{'"X";"x"."univ"[level:l]{};'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{'"f";'"eq";'"x";"void"[]{}};"fpf-cap"[]{'"g";'"eq";'"x";"top"[]{}}} }

interactive nuprl_fpf__cap__compatible  '"X"  :
   [wf] sequent { <H> >- '"X" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"X"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"X";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"X" }  -->
   sequent { <H> >- "fpf-compatible"[]{'"X";"x"."univ"[level:l]{};'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-cap"[]{'"f";'"eq";'"x";"void"[]{}} }  -->
   sequent { <H> >- "fpf-cap"[]{'"g";'"eq";'"x";"void"[]{}} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};"fpf-cap"[]{'"f";'"eq";'"x";"void"[]{}};"fpf-cap"[]{'"g";'"eq";'"x";"void"[]{}}} }

define unfold_fpf__join : "fpf-join"[]{'"eq";'"f";'"g"} <-->
      "pair"[]{"append"[]{"fst"[]{'"f"};"filter"[]{"lambda"[]{"a"."bnot"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}};"fst"[]{'"g"}}};"lambda"[]{"a"."fpf-cap"[]{'"f";'"eq";'"a";"fpf-ap"[]{'"g";'"eq";'"a"}}}}


interactive nuprl_fpf__join_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   sequent { <H> >- ("fpf-join"[]{'"eq";'"f";'"g"} in "fpf"[]{'"A";"a".'"B"['"a"]}) }

interactive nuprl_fpf__join__wf  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} "lambda"[]{"x".'"D"['"x"]} '"f" '"eq" '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"D"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   sequent { <H>; "a": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}  >- "subtype"[]{'"B"['"a"];'"D"['"a"]} }  -->
   sequent { <H>; "a": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"a";'"g"}}  >- "subtype"[]{'"C"['"a"];'"D"['"a"]} }  -->
   sequent { <H> >- ("fpf-join"[]{'"eq";'"f";'"g"} in "fpf"[]{'"A";"a".'"D"['"a"]}) }

interactive nuprl_fpf__join__idempotent  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   sequent { <H> >- "equal"[]{"fpf"[]{'"A";"a".'"B"['"a"]};"fpf-join"[]{'"eq";'"f";'"f"};'"f"} }

interactive nuprl_fpf__join__assoc  '"A" "lambda"[]{"x".'"B"['"x"]} '"h" '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "equal"[]{"fpf"[]{'"A";"a".'"B"['"a"]};"fpf-join"[]{'"eq";'"f";"fpf-join"[]{'"eq";'"g";'"h"}};"fpf-join"[]{'"eq";"fpf-join"[]{'"eq";'"f";'"g"};'"h"}} }

interactive nuprl_fpf__join__dom  '"A" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";"fpf-join"[]{'"eq";'"f";'"g"}}};"or"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}}} }

interactive nuprl_fpf__join__dom2  '"A"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";"fpf-join"[]{'"eq";'"f";'"g"}}};"or"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}}} }

interactive_rw nuprl_fpf__join__is__empty  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"f" in "fpf"[]{'"A";"x"."top"[]{}}) -->
   ('"g" in "fpf"[]{'"A";"x"."top"[]{}}) -->
   "fpf-is-empty"[]{"fpf-join"[]{'"eq";'"f";'"g"}} <--> "band"[]{"fpf-is-empty"[]{'"f"};"fpf-is-empty"[]{'"g"}}

interactive nuprl_fpf__join__ap  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"x" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eq";'"x";"fpf-join"[]{'"eq";'"f";'"g"}}} }  -->
   sequent { <H> >- "equal"[]{'"B"['"x"];"fpf-ap"[]{"fpf-join"[]{'"eq";'"f";'"g"};'"eq";'"x"};"ifthenelse"[]{"fpf-dom"[]{'"eq";'"x";'"f"};"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}} }

interactive nuprl_fpf__join__ap__left  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"f" '"x" '"eq" '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}} }  -->
   sequent { <H> >- "equal"[]{'"B"['"x"];"fpf-ap"[]{"fpf-join"[]{'"eq";'"f";'"g"};'"eq";'"x"};"fpf-ap"[]{'"f";'"eq";'"x"}} }

interactive_rw nuprl_fpf__join__ap__sq  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"f" in "fpf"[]{'"A";"a"."top"[]{}}) -->
   ('"x" in '"A") -->
   "fpf-ap"[]{"fpf-join"[]{'"eq";'"f";'"g"};'"eq";'"x"} <--> "ifthenelse"[]{"fpf-dom"[]{'"eq";'"x";'"f"};"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}

interactive_rw nuprl_fpf__join__cap__sq  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"f" in "fpf"[]{'"A";"a"."top"[]{}}) -->
   ('"g" in "fpf"[]{'"A";"a"."top"[]{}}) -->
   ('"x" in '"A") -->
   "fpf-cap"[]{"fpf-join"[]{'"eq";'"f";'"g"};'"eq";'"x";'"z"} <--> "ifthenelse"[]{"fpf-dom"[]{'"eq";'"x";'"f"};"fpf-cap"[]{'"f";'"eq";'"x";'"z"};"fpf-cap"[]{'"g";'"eq";'"x";'"z"}}

interactive nuprl_fpf__join__range univ[level:l]  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"df" in "fpf"[]{'"A";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x"."fpf-cap"[]{'"df";'"eq";'"x";"top"[]{}}} }  -->
   [wf] sequent { <H> >- '"dg" in "fpf"[]{'"A";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"x"."fpf-cap"[]{'"dg";'"eq";'"x";"top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a"."univ"[level:l]{};'"eq";'"df";'"dg"} }  -->
   sequent { <H>; "x": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}}  >- "assert"[]{"fpf-dom"[]{'"eq";'"x";'"df"}} }  -->
   sequent { <H>; "x": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}  >- "assert"[]{"fpf-dom"[]{'"eq";'"x";'"dg"}} }  -->
   sequent { <H> >- ("fpf-join"[]{'"eq";'"f";'"g"} in "fpf"[]{'"A";"x"."fpf-cap"[]{"fpf-join"[]{'"eq";'"df";'"dg"};'"eq";'"x";"top"[]{}}}) }

interactive nuprl_fpf__sub__join__left  '"A" "lambda"[]{"x".'"B1"['"x"]} "lambda"[]{"x".'"B2"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B1"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B2"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B1"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B2"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B1"['"a"];'"eq";'"f";"fpf-join"[]{'"eq";'"f";'"g"}} }

interactive nuprl_fpf__sub__join__right  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";"fpf-join"[]{'"eq";'"f";'"g"}} }

interactive nuprl_fpf__sub__join__right2  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   sequent { <H>; "x": '"A" ; "and"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};"assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}}}  >- "cand"[]{"subtype"[]{'"B"['"x"];'"C"['"x"]};"equal"[]{'"C"['"x"];"fpf-ap"[]{'"f";'"eq";'"x"};"fpf-ap"[]{'"g";'"eq";'"x"}}} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"C"['"a"];'"eq";'"g";"fpf-join"[]{'"eq";'"f";'"g"}} }

interactive nuprl_fpf__sub__join  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";"fpf-join"[]{'"eq";'"f";'"g"}};"fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";"fpf-join"[]{'"eq";'"f";'"g"}}}} }

interactive nuprl_fpf__sub__val  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"g" '"eq" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"x"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H>;"a": '"A";"x": '"B"['"a"] >- "type"{'"P"['"a";'"x"] } }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"f"} }  -->
   sequent { <H> >- "fpf-val"[]{'"eq";'"f";'"x";"x", "z".'"P"['"x";'"z"]} }  -->
   sequent { <H> >- "fpf-val"[]{'"eq";'"g";'"x";"x", "z".'"P"['"x";'"z"]} }

interactive nuprl_fpf__sub__val2  '"A'" '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]} "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"f" '"g" '"eq" '"x"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"A'" } }  -->
   sequent { <H> >- "subset"[]{'"A";'"A'"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A'"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A'" }  -->
   [wf] sequent { <H>;"a": '"A";"x": '"B"['"a"] >- "type"{'"P"['"a";'"x"] } }  -->
   [wf] sequent { <H>;"a": '"A";"x": '"B"['"a"] >- "type"{'"Q"['"a";'"x"] } }  -->
   sequent { <H>; "x": '"A" ; "z": '"B"['"x"] ; '"P"['"x";'"z"]  >- '"Q"['"x";'"z"] }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"f"} }  -->
   sequent { <H> >- "fpf-val"[]{'"eq";'"f";'"x";"x", "z".'"P"['"x";'"z"]} }  -->
   sequent { <H> >- "fpf-val"[]{'"eq";'"g";'"x";"x", "z".'"Q"['"x";'"z"]} }

interactive nuprl_fpf__sub__val3  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} "lambda"[]{"x1", "x".'"Q"['"x1";'"x"]} "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"f" '"g" '"eq" '"x"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H>;"a": '"A";"x": '"B"['"a"] >- "type"{'"P"['"a";'"x"] } }  -->
   [wf] sequent { <H>;"a": '"A";"x": '"C"['"a"] >- "type"{'"Q"['"a";'"x"] } }  -->
   sequent { <H>; "x": '"A" ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"g"}} ; "assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}}  >- "cand"[]{"subtype"[]{'"C"['"x"];'"B"['"x"]};"implies"[]{'"P"['"x";"fpf-ap"[]{'"g";'"eq";'"x"}];'"Q"['"x";"fpf-ap"[]{'"g";'"eq";'"x"}]}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"f"};"implies"[]{"fpf-val"[]{'"eq";'"f";'"x";"y", "z".'"P"['"y";'"z"]};"fpf-val"[]{'"eq";'"g";'"x";"y", "z".'"Q"['"y";'"z"]}}}} }

define unfold_fpf__const : "fpf-const"[]{'"L";'"v"} <-->
      "pair"[]{'"L";"lambda"[]{"x".'"v"}}


interactive nuprl_fpf__const_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"v" in '"B" }  -->
   sequent { <H> >- ("fpf-const"[]{'"L";'"v"} in "fpf"[]{'"A";"a".'"B"}) }

define unfold_fpf__single : "fpf-single"[]{'"x";'"v"} <-->
      "pair"[]{"cons"[]{'"x";"nil"[]{}};"lambda"[]{"x".'"v"}}


interactive nuprl_fpf__single_wf {| intro[] |}  '"A" '"x" "lambda"[]{"x".'"B"['"x"]} '"v"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B"['"x"] }  -->
   sequent { <H> >- ("fpf-single"[]{'"x";'"v"} in "fpf"[]{'"A";"x".'"B"['"x"]}) }

interactive nuprl_fpf__single_wf2 {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B" }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   sequent { <H> >- ("fpf-single"[]{'"x";'"v"} in "fpf"[]{'"A";"a"."fpf-cap"[]{"fpf-single"[]{'"x";'"B"};'"eqa";'"a";"top"[]{}}}) }

interactive nuprl_fpf__single__sub__reflexive  '"A" '"x" "lambda"[]{"x".'"B"['"x"]} '"v" '"eqa"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B"['"x"] }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eqa";"fpf-single"[]{'"x";'"v"};"fpf-single"[]{'"x";'"v"}} }

interactive_rw nuprl_fpf__cap__single1  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"x" in '"A") -->
   "fpf-cap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"x";'"z"} <--> '"v"

interactive_rw nuprl_fpf__ap__single   :
   "fpf-ap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"x"} <--> '"v"

interactive_rw nuprl_fpf__cap__single  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"x" in '"A") -->
   ('"y" in '"A") -->
   "fpf-cap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"y";'"z"} <--> "ifthenelse"[]{(("eqof"[]{'"eq"} '"x") '"y");'"v";'"z"}

interactive_rw nuprl_fpf__val__single1  '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"v" '"x" '"eq"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"x" in '"A") -->
   "fpf-val"[]{'"eq";"fpf-single"[]{'"x";'"v"};'"x";"a", "z".'"P"['"a";'"z"]} <--> "implies"[]{"true"[]{};'"P"['"x";'"v"]}

define unfold_fpf__add__single : "fpf-add-single"[]{'"eq";'"f";'"x";'"v"} <-->
      "fpf-join"[]{'"eq";'"f";"fpf-single"[]{'"x";'"v"}}


interactive nuprl_fpf__add__single_wf {| intro[] |}  '"A" '"x" "lambda"[]{"x".'"B"['"x"]} '"v" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B"['"x"] }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x".'"B"['"x"]} }  -->
   sequent { <H> >- ("fpf-add-single"[]{'"eq";'"f";'"x";'"v"} in "fpf"[]{'"A";"x".'"B"['"x"]}) }

define unfold_fpf__vals : "fpf-vals"[]{'"eq";'"P";'"f"} <-->
      "let"[]{"filter"[]{'"P";"remove-repeats"[]{'"eq";"fst"[]{'"f"}}};"L"."zip"[]{'"L";"map"[]{"snd"[]{'"f"};'"L"}}}


interactive nuprl_fpf__vals_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"eq" '"P"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x".'"B"['"x"]} }  -->
   sequent { <H> >- ("fpf-vals"[]{'"eq";'"P";'"f"} in "list"[]{"prod"[]{"set"[]{'"A";"a"."assert"[]{('"P" '"a")}};"x".'"B"['"x"]}}) }

interactive_rw nuprl_filter__fpf__vals univ[level:l] '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"P" '"eq" "lambda"[]{"x".'"Q"['"x"]}  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ("lambda"[]{"x".'"B"['"x"]} in "fun"[]{'"A";""."univ"[level:l]{}}) -->
   ('"P" in "fun"[]{'"A";""."bool"[]{}}) -->
   ("lambda"[]{"x".'"Q"['"x"]} in "fun"[]{'"A";""."bool"[]{}}) -->
   ('"f" in "fpf"[]{'"A";"x".'"B"['"x"]}) -->
   "filter"[]{"lambda"[]{"pL".'"Q"["fst"[]{'"pL"}]};"fpf-vals"[]{'"eq";'"P";'"f"}} <--> "fpf-vals"[]{'"eq";"lambda"[]{"a"."band"[]{('"P" '"a");("lambda"[]{"x".'"Q"['"x"]} '"a")}};'"f"}

interactive nuprl_fpf__vals__singleton  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"a" '"eq" '"P"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- '"P" '"x" in "bool"[]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x".'"B"['"x"]} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eq";'"a";'"f"}} }  -->
   sequent { <H>; "b": '"A"  >- "iff"[]{"assert"[]{('"P" '"b")};"equal"[]{'"A";'"b";'"a"}} }  -->
   sequent { <H> >- "equal"[]{"list"[]{"prod"[]{'"A";"x".'"B"['"x"]}};"fpf-vals"[]{'"eq";'"P";'"f"};"cons"[]{"pair"[]{'"a";"fpf-ap"[]{'"f";'"eq";'"a"}};"nil"[]{}}} }

interactive_rw nuprl_fpf__vals__nil univ[level:l] '"A" "lambda"[]{"x".'"B"['"x"]} '"a"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ("lambda"[]{"x".'"B"['"x"]} in "fun"[]{'"A";""."univ"[level:l]{}}) -->
   ('"P" in "fun"[]{'"A";""."bool"[]{}}) -->
   ('"f" in "fpf"[]{'"A";"x".'"B"['"x"]}) -->
   ('"a" in '"A") -->
   "not"[]{"assert"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}} -->
   "all"[]{'"A";"b"."iff"[]{"assert"[]{('"P" '"b")};"equal"[]{'"A";'"b";'"a"}}} -->
   "fpf-vals"[]{'"eq";'"P";'"f"} <--> "nil"[]{}

define unfold_fpf__all : "fpf-all"[]{'"A";'"eq";'"f";"x", "v".'"P"['"x";'"v"]} <-->
      "all"[]{'"A";"x"."implies"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";'"f"}};'"P"['"x";"fpf-ap"[]{'"f";'"eq";'"x"}]}}


interactive nuprl_fpf__all_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"f" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B"['"x"] >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x".'"B"['"x"]} }  -->
   sequent { <H> >- ("fpf-all"[]{'"A";'"eq";'"f";"x", "v".'"P"['"x";'"v"]} in "univ"[level:l]{}) }

define unfold_fpf__rename : "fpf-rename"[]{'"eq";'"r";'"f"} <-->
      "pair"[]{"map"[]{'"r";"fst"[]{'"f"}};"lambda"[]{"x".("snd"[]{'"f"} "hd"[]{"filter"[]{"lambda"[]{"y".(("eqof"[]{'"eq"} ('"r" '"y")) '"x")};"fst"[]{'"f"}}})}}


interactive nuprl_fpf__rename_wf {| intro[] |} univ[level:l] '"A" '"C" "lambda"[]{"x".'"B"['"x"]} '"r" "lambda"[]{"x".'"D"['"x"]} '"f" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"C" >- '"D"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "equal"[]{"univ"[level:l]{};'"D"[('"r" '"a")];'"B"['"a"]} }  -->
   sequent { <H> >- ("fpf-rename"[]{'"eq";'"r";'"f"} in "fpf"[]{'"C";"c".'"D"['"c"]}) }

interactive nuprl_fpf__rename__dom  "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"c" in '"C" }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{'"eqc";'"c";"fpf-rename"[]{'"eqc";'"r";'"f"}}};"exists"[]{'"A";"a"."cand"[]{"assert"[]{"fpf-dom"[]{'"eqa";'"a";'"f"}};"equal"[]{'"C";'"c";('"r" '"a")}}}} }

interactive nuprl_fpf__rename__dom2  '"A" '"C"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"assert"[]{"fpf-dom"[]{'"eqa";'"a";'"f"}};"assert"[]{"fpf-dom"[]{'"eqc";('"r" '"a");"fpf-rename"[]{'"eqc'";'"r";'"f"}}}}} }

interactive nuprl_fpf__rename__ap  '"A" '"C" "lambda"[]{"x".'"B"['"x"]} '"r" '"f" '"a" '"eqa" '"eqc"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "inject"[]{'"A";'"C";'"r"} }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eqa";'"a";'"f"}} }  -->
   sequent { <H> >- "equal"[]{'"B"['"a"];"fpf-ap"[]{"fpf-rename"[]{'"eqc";'"r";'"f"};'"eqc";('"r" '"a")};"fpf-ap"[]{'"f";'"eqa";'"a"}} }

interactive nuprl_fpf__rename__ap2  '"A" '"C" "lambda"[]{"x".'"B"['"x"]} '"r" '"f" '"a" '"eqa" '"eqc'" '"eqc"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H> >- '"eqc'" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "inject"[]{'"A";'"C";'"r"} }  -->
   sequent { <H> >- "assert"[]{"fpf-dom"[]{'"eqa";'"a";'"f"}} }  -->
   sequent { <H> >- "equal"[]{'"B"['"a"];"fpf-ap"[]{"fpf-rename"[]{'"eqc";'"r";'"f"};'"eqc'";('"r" '"a")};"fpf-ap"[]{'"f";'"eqa";'"a"}} }

interactive nuprl_fpf__rename__cap  '"A" '"C"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B" }  -->
   sequent { <H> >- "inject"[]{'"A";'"C";'"r"} }  -->
   sequent { <H> >- "equal"[]{'"B";"fpf-cap"[]{"fpf-rename"[]{'"eqc";'"r";'"f"};'"eqc";('"r" '"a");'"z"};"fpf-cap"[]{'"f";'"eqa";'"a";'"z"}} }

interactive nuprl_fpf__rename__cap2  '"A" '"C"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H> >- '"eqc'" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B" }  -->
   sequent { <H> >- "inject"[]{'"A";'"C";'"r"} }  -->
   sequent { <H> >- "equal"[]{'"B";"fpf-cap"[]{"fpf-rename"[]{'"eqc";'"r";'"f"};'"eqc'";('"r" '"a");'"z"};"fpf-cap"[]{'"f";'"eqa";'"a";'"z"}} }

interactive nuprl_fpf__rename__cap3  '"A" '"C"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"C" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   [wf] sequent { <H> >- '"eqa" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"eqc" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H> >- '"eqc'" in "deq"[]{'"C"} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   [wf] sequent { <H> >- '"z" in '"B" }  -->
   [wf] sequent { <H> >- '"c" in '"C" }  -->
   sequent { <H> >- "inject"[]{'"A";'"C";'"r"} }  -->
   sequent { <H> >- "equal"[]{'"C";'"c";('"r" '"a")} }  -->
   sequent { <H> >- "equal"[]{'"B";"fpf-cap"[]{"fpf-rename"[]{'"eqc";'"r";'"f"};'"eqc'";'"c";'"z"};"fpf-cap"[]{'"f";'"eqa";'"a";'"z"}} }

define unfold_fpf__inv__rename : "fpf-inv-rename"[]{'"r";'"rinv";'"f"} <-->
      "pair"[]{"mapfilter"[]{"lambda"[]{"x"."outl"[]{('"rinv" '"x")}};"lambda"[]{"x"."is_inl"[]{('"rinv" '"x")}};"fst"[]{'"f"}};"compose"[]{"snd"[]{'"f"};'"r"}}


interactive nuprl_fpf__inv__rename_wf {| intro[] |} univ[level:l] '"A" '"C" "lambda"[]{"x".'"D"['"x"]} '"rinv" '"r" "lambda"[]{"x".'"B"['"x"]} '"f"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"C" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"B"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"C" >- '"D"['"x"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"C" >- '"rinv" '"x" in "union"[]{'"A";"unit"[]{}} }  -->
   [wf] sequent { <H>;"x": '"A" >- '"r" '"x" in '"C" }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"C";"c".'"D"['"c"]} }  -->
   sequent { <H> >- "inv-rel"[]{'"A";'"C";'"r";'"rinv"} }  -->
   sequent { <H>; "a": '"A"  >- "equal"[]{"univ"[level:l]{};'"D"[('"r" '"a")];'"B"['"a"]} }  -->
   sequent { <H> >- ("fpf-inv-rename"[]{'"r";'"rinv";'"f"} in "fpf"[]{'"A";"a".'"B"['"a"]}) }

define unfold_fpf__compose : "fpf-compose"[]{'"g";'"f"} <-->
      "pair"[]{"fst"[]{'"f"};"compose"[]{'"g";"snd"[]{'"f"}}}


interactive nuprl_fpf__compose_wf {| intro[] |}  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} '"f" '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "isect"[]{'"A";"a"."fun"[]{'"B"['"a"];"".'"C"['"a"]}} }  -->
   sequent { <H> >- ("fpf-compose"[]{'"g";'"f"} in "fpf"[]{'"A";"a".'"C"['"a"]}) }

interactive nuprl_fpf__sub__reflexive  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-sub"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"f"} }

define unfold_mkfpf : "mkfpf"[]{'"a";'"b"} <-->
      "pair"[]{'"a";'"b"}


interactive nuprl_mkfpf_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"a" in "list"[]{'"A"} }  -->
   [wf] sequent { <H>;"a": "set"[]{'"A";"a@0"."mem"[]{'"a@0";'"a";'"A"}} >- '"b" '"a" in "top"[]{} }  -->
   sequent { <H> >- ("mkfpf"[]{'"a";'"b"} in "fpf"[]{'"A";"a"."top"[]{}}) }

interactive nuprl_fpf__join__compatible__left  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"E"['"x"]} "lambda"[]{"x".'"F"['"x"]} "lambda"[]{"x".'"G"['"x"]} '"g" '"h" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"D"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"E"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"F"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"G"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"D"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"E"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"C"['"a"];'"F"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"D"['"a"];'"E"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"D"['"a"];'"F"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"F"['"a"];'"G"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"E"['"a"];'"G"['"a"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-compatible"[]{'"A";"a".'"E"['"a"];'"eq";'"f";'"h"};"implies"[]{"fpf-compatible"[]{'"A";"a".'"F"['"a"];'"eq";'"g";'"h"};"fpf-compatible"[]{'"A";"a".'"G"['"a"];'"eq";"fpf-join"[]{'"eq";'"f";'"g"};'"h"}}}} }

interactive nuprl_fpf__join__compatible__right  '"A" "lambda"[]{"x".'"B"['"x"]} "lambda"[]{"x".'"C"['"x"]} "lambda"[]{"x".'"D"['"x"]} "lambda"[]{"x".'"E"['"x"]} "lambda"[]{"x".'"F"['"x"]} "lambda"[]{"x".'"G"['"x"]} '"g" '"f" '"h" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"C"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"D"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"E"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"F"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"G"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"C"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"D"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"B"['"a"];'"E"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"C"['"a"];'"F"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"D"['"a"];'"E"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"D"['"a"];'"F"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"F"['"a"];'"G"['"a"]} }  -->
   sequent { <H>; "a": '"A"  >- "subtype"[]{'"E"['"a"];'"G"['"a"]} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"fpf-compatible"[]{'"A";"a".'"E"['"a"];'"eq";'"h";'"f"};"implies"[]{"fpf-compatible"[]{'"A";"a".'"F"['"a"];'"eq";'"h";'"g"};"fpf-compatible"[]{'"A";"a".'"G"['"a"];'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}}}}} }

interactive nuprl_fpf__compatible__self  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"f"} }

interactive nuprl_fpf__compatible__join  '"A" "lambda"[]{"x".'"B"['"x"]} '"f" '"h" '"eq" '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"h";'"f"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"h";'"g"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}} }

interactive nuprl_fpf__compatible__symmetry  '"A" "lambda"[]{"x".'"B"['"x"]} '"g" '"f" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"f"} }

interactive nuprl_fpf__compatible__join2  '"A" "lambda"[]{"x".'"B"['"x"]} '"h" '"f" '"eq" '"g"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"h"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"h"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";"fpf-join"[]{'"eq";'"f";'"g"};'"h"} }

interactive nuprl_fpf__compatible__singles  '"A" '"x" "lambda"[]{"x".'"B"['"x"]} '"y" '"u" '"v" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B"['"x"] }  -->
   [wf] sequent { <H> >- '"u" in '"B"['"y"] }  -->
   sequent { <H>; "equal"[]{'"A";'"x";'"y"}  >- "equal"[]{'"B"['"x"];'"v";'"u"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";"fpf-single"[]{'"x";'"v"};"fpf-single"[]{'"y";'"u"}} }

interactive nuprl_fpf__single__dom   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"y" in '"A" }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{'"eq";'"x";"fpf-single"[]{'"y";'"v"}}};"equal"[]{'"A";'"x";'"y"}} }

interactive_rw nuprl_fpf__single__dom__sq  '"A"  :
   "type"{'"A"} -->
   ('"eq" in "deq"[]{'"A"}) -->
   ('"x" in '"A") -->
   ('"y" in '"A") -->
   "fpf-dom"[]{'"eq";'"x";"fpf-single"[]{'"y";'"v"}} <--> (("eqof"[]{'"eq"} '"y") '"x")

interactive nuprl_fpf__join__dom__decl univ[level:l]  :
   [wf] sequent { <H> >- '"f" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";"fpf-join"[]{"id-deq"[]{};'"f";'"g"}}};"or"[]{"assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"f"}};"assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"g"}}}} }

interactive nuprl_fpf__join__dom__da univ[level:l]  :
   [wf] sequent { <H> >- '"f" in "fpf"[]{"Knd"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{"Knd"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Knd"[]{} }  -->
   sequent { <H> >- "iff"[]{"assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"x";"fpf-join"[]{"Kind-deq"[]{};'"f";'"g"}}};"or"[]{"assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"x";'"f"}};"assert"[]{"fpf-dom"[]{"Kind-deq"[]{};'"x";'"g"}}}} }

interactive nuprl_fpf__cap__join__subtype univ[level:l] '"A"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"a" in '"A" }  -->
   sequent { <H> >- "subtype"[]{"fpf-cap"[]{"fpf-join"[]{'"eq";'"f";'"g"};'"eq";'"a";"top"[]{}};"fpf-cap"[]{'"f";'"eq";'"a";"top"[]{}}} }

interactive nuprl_fpf__all__single  '"A" "lambda"[]{"x".'"B"['"x"]} '"x" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"v" '"eq"  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A" >- "type"{'"B"['"x"] } }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"B"['"x"] >- "type"{'"P"['"x";'"x1"] } }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in '"B"['"x"] }  -->
   sequent { <H> >- "iff"[]{"fpf-all"[]{'"A";'"eq";"fpf-single"[]{'"x";'"v"};"y", "w".'"P"['"y";'"w"]};'"P"['"x";'"v"]} }

interactive nuprl_fpf__all__single__decl univ[level:l] '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"v" '"x" '"eq"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "univ"[level:l]{} >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x" in '"A" }  -->
   [wf] sequent { <H> >- '"v" in "univ"[level:l]{} }  -->
   sequent { <H> >- "iff"[]{"fpf-all"[]{'"A";'"eq";"fpf-single"[]{'"x";'"v"};"y", "w".'"P"['"y";'"w"]};'"P"['"x";'"v"]} }

interactive nuprl_fpf__all__join__decl univ[level:l] '"A" "lambda"[]{"x1", "x".'"P"['"x1";'"x"]} '"f" '"eq" '"g"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": "univ"[level:l]{} >- '"P"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"A";"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-all"[]{'"A";'"eq";'"f";"y", "w".'"P"['"y";'"w"]} }  -->
   sequent { <H> >- "fpf-all"[]{'"A";'"eq";'"g";"y", "w".'"P"['"y";'"w"]} }  -->
   sequent { <H> >- "fpf-all"[]{'"A";'"eq";"fpf-join"[]{'"eq";'"f";'"g"};"y", "w".'"P"['"y";'"w"]} }

interactive nuprl_fpf__empty__compatible__right  '"A" '"f" '"eq" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";"fpf-empty"[]{}} }

interactive nuprl_fpf__empty__compatible__left  '"A" '"f" '"eq" "lambda"[]{"x".'"B"['"x"]}  :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";"fpf-empty"[]{};'"f"} }

interactive nuprl_fpf__compatible__triple   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"T"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"T";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"g" in "fpf"[]{'"T";"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"h" in "fpf"[]{'"T";"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"T";"x"."univ"[level:l]{};'"eq";'"f";'"g"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"T";"x"."univ"[level:l]{};'"eq";'"h";'"f"} }  -->
   sequent { <H> >- "fpf-compatible"[]{'"T";"x"."univ"[level:l]{};'"eq";'"h";'"g"} }  -->
   sequent { <H> >- "guard"[]{"and"[]{"and"[]{"fpf-sub"[]{'"T";"x"."univ"[level:l]{};'"eq";'"g";"fpf-join"[]{'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}}};"fpf-sub"[]{'"T";"x"."univ"[level:l]{};'"eq";'"f";"fpf-join"[]{'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}}}};"and"[]{"fpf-sub"[]{'"T";"x"."univ"[level:l]{};'"eq";"fpf-join"[]{'"eq";'"h";'"g"};"fpf-join"[]{'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}}};"fpf-sub"[]{'"T";"x"."univ"[level:l]{};'"eq";"fpf-join"[]{'"eq";'"h";'"f"};"fpf-join"[]{'"eq";'"h";"fpf-join"[]{'"eq";'"f";'"g"}}}}}} }

define unfold_fpf__dom__list : "fpf-dom-list"[]{'"f"} <-->
      "fst"[]{'"f"}


interactive nuprl_fpf__dom__list_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent { <H> >- '"f" in "fpf"[]{'"A";"a"."top"[]{}} }  -->
   sequent { <H> >- ("fpf-dom-list"[]{'"f"} in "list"[]{"set"[]{'"A";"a"."assert"[]{"fpf-dom"[]{'"eq";'"a";'"f"}}}}) }


(**** display forms ****)


dform nuprl_fpf_df : except_mode[src] :: "fpf"[]{'"A";"a".'"B"} =
   `"" slot{'"a"} `":" slot{'"A"} `" fp-> " slot{'"B"} `""


dform nuprl_fpf__dom_df : except_mode[src] :: "fpf-dom"[]{'"eq";'"x";'"f"} =
   `"" slot{'"x"} `" " member `" dom(" slot{'"f"} `")"


dform nuprl_fpf__empty_df : except_mode[src] :: "fpf-empty"[]{} =
   `""


dform nuprl_fpf__is__empty_df : except_mode[src] :: "fpf-is-empty"[]{'"f"} =
   `"fpf-is-empty(" slot{'"f"} `")"


dform nuprl_fpf__ap_df : except_mode[src] :: "fpf-ap"[]{'"f";'"eq";'"x"} =
   `"" slot{'"f"} `"(" slot{'"x"} `")"


dform nuprl_fpf__cap_df : except_mode[src] :: "fpf-cap"[]{'"f";'"eq";'"x";'"z"} =
   `"fpf-cap(" slot{'"f"} `";" slot{'"eq"} `";" slot{'"x"} `";" slot{'"z"} `")"

dform nuprl_fpf__cap_df : except_mode[src] :: "fpf-cap"[]{'"f";'"eq";'"x";'"z"} =
   `"" slot{'"f"} `"(" slot{'"x"} `")?" slot{'"z"} `""


dform nuprl_fpf__val_df : except_mode[src] :: "fpf-val"[]{'"eq";'"f";'"x";"a", "z".'"P"} =
   `"" slot{'"z"} `" != " slot{'"f"} `"(" slot{'"x"} `") ==> " slot{'"P"} `""


dform nuprl_fpf__sub_df : except_mode[src] :: "fpf-sub"[]{'"A";"a".'"B";'"eq";'"f";'"g"} =
   `"" slot{'"f"} `" " sqsubseteq `" " slot{'"g"} `""


dform nuprl_fpf__compatible_df : except_mode[src] :: "fpf-compatible"[]{'"A";"a".'"B";'"eq";'"f";'"g"} =
   `"" slot{'"f"} `" || " slot{'"g"} `""


dform nuprl_fpf__join_df : except_mode[src] :: "fpf-join"[]{'"eq";'"f";'"g"} =
   `"" slot{'"f"} `" " oplus `" " slot{'"g"} `""


dform nuprl_fpf__const_df : except_mode[src] :: "fpf-const"[]{'"L";'"v"} =
   `"" slot{'"L"} `" |-fpf-> " slot{'"v"} `""


dform nuprl_fpf__single_df : except_mode[src] :: "fpf-single"[]{'"x";'"v"} =
   `"" slot{'"x"} `" : " slot{'"v"} `""


dform nuprl_fpf__add__single_df : except_mode[src] :: "fpf-add-single"[]{'"eq";'"f";'"x";'"v"} =
   `"" slot{'"f"} `"" sbreak["",""] `"" slot{'"x"} `" : " slot{'"v"} `""


dform nuprl_fpf__vals_df : except_mode[src] :: "fpf-vals"[]{'"eq";'"P";'"f"} =
   `"fpf-vals(" slot{'"eq"} `";" slot{'"P"} `";" slot{'"f"} `")"


dform nuprl_fpf__all_df : except_mode[src] :: "fpf-all"[]{'"A";'"eq";'"f";"x", "v".'"P"} =
   `"" forall `"" slot{'"x"} `"" member `"dom(" slot{'"f"} `"). " szone sbreak["",""] ezone `""
    slot{'"v"} `"=" slot{'"f"} `"(" slot{'"x"} `") " Rightarrow `" " szone sbreak["",""]
    ezone `" " slot{'"P"} `""


dform nuprl_fpf__rename_df : except_mode[src] :: "fpf-rename"[]{'"eq";'"r";'"f"} =
   `"fpf-rename(" slot{'"eq"} `";" slot{'"r"} `";" slot{'"f"} `")"

dform nuprl_fpf__rename_df : except_mode[src] :: "fpf-rename"[]{'"eq";'"r";'"f"} =
   `"rename(" slot{'"r"} `";" szone sbreak["",""] ezone `"" slot{'"f"} `")"


dform nuprl_fpf__inv__rename_df : except_mode[src] :: "fpf-inv-rename"[]{'"r";'"rinv";'"f"} =
   `"fpf-inv-rename(" slot{'"r"} `";" slot{'"rinv"} `";" slot{'"f"} `")"


dform nuprl_fpf__compose_df : except_mode[src] :: "fpf-compose"[]{'"g";'"f"} =
   `"fpf-compose(" slot{'"g"} `";" slot{'"f"} `")"


dform nuprl_mkfpf_df : except_mode[src] :: "mkfpf"[]{'"a";'"b"} =
   `"mkfpf(" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_fpf__dom__list_df : except_mode[src] :: "fpf-dom-list"[]{'"f"} =
   `"fpf-dom-list(" slot{'"f"} `")"


