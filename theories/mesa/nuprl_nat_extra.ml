extends Ma_tree_1

open Dtactic


interactive nuprl_id_increasing   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   sequent { <H> >- "increasing"[]{"lambda"[]{"i".'"i"};'"k"} }

interactive nuprl_increasing_implies   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int"[]{} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"x"."all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"y"."implies"[]{"lt"[]{'"x";'"y"};"lt"[]{('"f" '"x");('"f" '"y")}}}}} }

interactive nuprl_increasing_implies_le   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int"[]{} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   sequent { <H> >- "guard"[]{"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"x"."all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"y"."implies"[]{"le"[]{'"x";'"y"};"le"[]{('"f" '"x");('"f" '"y")}}}}} }

interactive nuprl_compose_increasing  '"m"  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"m"} >- '"g" '"x" in "int"[]{} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   sequent { <H> >- "increasing"[]{'"g";'"m"} }  -->
   sequent { <H> >- "increasing"[]{"compose"[]{'"g";'"f"};'"k"} }

interactive nuprl_increasing_inj   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   sequent { <H> >- "inject"[]{"int_seg"[]{"number"[0:n]{};'"k"};"int_seg"[]{"number"[0:n]{};'"m"};'"f"} }

interactive nuprl_increasing_le   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"m"}};"f"."increasing"[]{'"f";'"k"}} }  -->
   sequent { <H> >- "le"[]{'"k";'"m"} }

interactive nuprl_increasing_is_id  '"k"  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};('"f" '"i");'"i"} }

interactive nuprl_increasing_lower_bound  '"k"  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"k"} }  -->
   sequent { <H> >- "le"[]{"add"[]{('"f" "number"[0:n]{});'"x"};('"f" '"x")} }

interactive nuprl_injection_le   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"m"}};"f"."inject"[]{"int_seg"[]{"number"[0:n]{};'"k"};"int_seg"[]{"number"[0:n]{};'"m"};'"f"}} }  -->
   sequent { <H> >- "le"[]{'"k";'"m"} }

interactive nuprl_disjoint_increasing_onto  '"f" '"g"  :
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"g" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"n"} }  -->
   sequent { <H> >- "increasing"[]{'"g";'"k"} }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};'"m"}  >- "or"[]{"exists"[]{"int_seg"[]{"number"[0:n]{};'"n"};"j"."equal"[]{"int"[]{};'"i";('"f" '"j")}};"exists"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."equal"[]{"int"[]{};'"i";('"g" '"j")}}} }  -->
   sequent { <H>; "j1": "int_seg"[]{"number"[0:n]{};'"n"} ; "j2": "int_seg"[]{"number"[0:n]{};'"k"}  >- "not"[]{"equal"[]{"int"[]{};('"f" '"j1");('"g" '"j2")}} }  -->
   sequent { <H> >- "equal"[]{"nat"[]{};'"m";"add"[]{'"n";'"k"}} }

interactive nuprl_bijection_restriction   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "biject"[]{"int_seg"[]{"number"[0:n]{};'"k"};"int_seg"[]{"number"[0:n]{};'"k"};'"f"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};('"f" "sub"[]{'"k";"number"[1:n]{}});"sub"[]{'"k";"number"[1:n]{}}} }  -->
   sequent { <H> >- "guard"[]{"and"[]{('"f" in "fun"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};""."int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}}});"biject"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};'"f"}}} }

define unfold_primrec : "primrec"[]{'"n";'"b";'"c"} <-->
      (("ycomb"[]{} "lambda"[]{"primrec"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};'"b";(('"c" "sub"[]{'"n";"number"[1:n]{}}) ('"primrec" "sub"[]{'"n";"number"[1:n]{}}))}}}) '"n")


interactive nuprl_primrec_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": '"T" >- '"c" '"x" '"x1" in '"T" }  -->
   sequent { <H> >- ("primrec"[]{'"n";'"b";'"c"} in '"T") }

interactive nuprl_primrec_add   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in '"T" }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"add"[]{'"n";'"m"}};"x1": '"T" >- '"c" '"x" '"x1" in '"T" }  -->
   sequent { <H> >- "equal"[]{'"T";"primrec"[]{"add"[]{'"n";'"m"};'"b";'"c"};"primrec"[]{'"n";"primrec"[]{'"m";'"b";'"c"};"lambda"[]{"i"."lambda"[]{"t".(('"c" "add"[]{'"i";'"m"}) '"t")}}}} }

define unfold_nondecreasing : "nondecreasing"[]{'"f";'"k"} <-->
      "all"[]{"int_seg"[]{"number"[0:n]{};"sub"[]{'"k";"number"[1:n]{}}};"i"."le"[]{('"f" '"i");('"f" "add"[]{'"i";"number"[1:n]{}})}}


interactive nuprl_nondecreasing_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f" '"x" in "int"[]{} }  -->
   sequent { <H> >- ("nondecreasing"[]{'"f";'"k"} in "univ"[level:l]{}) }

interactive nuprl_const_nondecreasing   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   sequent { <H> >- "nondecreasing"[]{"lambda"[]{"i".'"x"};'"k"} }

define unfold_fadd : "fadd"[]{'"f";'"g"} <-->
      "lambda"[]{"i"."add"[]{('"f" '"i");('"g" '"i")}}


interactive nuprl_fadd_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"g" '"x" in "int_seg"[]{"number"[0:n]{};"add"[]{'"k";"number"[1:n]{}}} }  -->
   sequent { <H> >- ("fadd"[]{'"f";'"g"} in "fun"[]{"int_seg"[]{"number"[0:n]{};'"n"};""."int_seg"[]{"number"[0:n]{};"add"[]{'"m";'"k"}}}) }

interactive nuprl_fadd_increasing   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"g" '"x" in "int"[]{} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"n"} }  -->
   sequent { <H> >- "nondecreasing"[]{'"g";'"n"} }  -->
   sequent { <H> >- "increasing"[]{"fadd"[]{'"f";'"g"};'"n"} }

define unfold_fshift : "fshift"[]{'"f";'"x"} <-->
      "lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"i";"number"[0:n]{}};'"x";('"f" "sub"[]{'"i";"number"[1:n]{}})}}


interactive nuprl_fshift_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- ("fshift"[]{'"f";'"x"} in "fun"[]{"int_seg"[]{"number"[0:n]{};"add"[]{'"n";"number"[1:n]{}}};""."int_seg"[]{"number"[0:n]{};'"k"}}) }

interactive nuprl_fshift_increasing   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int"[]{} }  -->
   sequent { <H> >- "increasing"[]{'"f";'"n"} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "lt"[]{'"x";('"f" "number"[0:n]{})} }  -->
   sequent { <H> >- "increasing"[]{"fshift"[]{'"f";'"x"};"add"[]{'"n";"number"[1:n]{}}} }

define unfold_finite : "finite"[]{'"T"} <-->
      "all"[]{"fun"[]{'"T";"".'"T"};"f"."implies"[]{"inject"[]{'"T";'"T";'"f"};"surject"[]{'"T";'"T";'"f"}}}


interactive nuprl_finite_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("finite"[]{'"T"} in "univ"[level:l]{}) }

interactive nuprl_nsub_finite   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "finite"[]{"int_seg"[]{"number"[0:n]{};'"n"}} }

define unfold_fappend : "fappend"[]{'"f";'"n";'"x"} <-->
      "lambda"[]{"i"."ifthenelse"[]{"beq_int"[]{'"i";'"n"};'"x";('"f" '"i")}}


interactive nuprl_fappend_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- ("fappend"[]{'"f";'"n";'"x"} in "fun"[]{"int_seg"[]{"number"[0:n]{};"add"[]{'"n";"number"[1:n]{}}};""."int_seg"[]{"number"[0:n]{};'"m"}}) }

interactive nuprl_increasing_split   :
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"m"} >- "type"{'"P" '"x" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};'"m"}  >- "decidable"[]{('"P" '"i")} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"n"."exists"[]{"nat"[]{};"k"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"n"};""."int_seg"[]{"number"[0:n]{};'"m"}};"f"."exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"m"}};"g"."and"[]{"increasing"[]{'"f";'"n"};"and"[]{"increasing"[]{'"g";'"k"};"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};'"n"};"i".('"P" ('"f" '"i"))};"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."not"[]{('"P" ('"g" '"j"))}};"all"[]{"int_seg"[]{"number"[0:n]{};'"m"};"i"."or"[]{"exists"[]{"int_seg"[]{"number"[0:n]{};'"n"};"j"."equal"[]{"int"[]{};'"i";('"f" '"j")}};"exists"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."equal"[]{"int"[]{};'"i";('"g" '"j")}}}}}}}}}}}} }

define unfold_sum : "sum"[]{'"k";"x".'"f"['"x"]} <-->
      "primrec"[]{'"k";"number"[0:n]{};"lambda"[]{"x"."lambda"[]{"n"."add"[]{'"n";'"f"['"x"]}}}}


interactive nuprl_sum_wf {| intro[] |}  '"n" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   sequent { <H> >- ("sum"[]{'"n";"x".'"f"['"x"]} in "int"[]{}) }

interactive nuprl_non_neg_sum  '"n" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"}  >- "le"[]{"number"[0:n]{};'"f"['"x"]} }  -->
   sequent { <H> >- "le"[]{"number"[0:n]{};"sum"[]{'"n";"x".'"f"['"x"]}} }

interactive nuprl_sum_linear  '"n" "lambda"[]{"x".'"g"['"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"g"['"x"] in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{"sum"[]{'"n";"x".'"f"['"x"]};"sum"[]{'"n";"x".'"g"['"x"]}};"sum"[]{'"n";"x"."add"[]{'"f"['"x"];'"g"['"x"]}}} }

interactive nuprl_sum_scalar_mult  '"n" "lambda"[]{"x".'"f"['"x"]} '"a"  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"a";"sum"[]{'"n";"x".'"f"['"x"]}};"sum"[]{'"n";"x"."mul"[]{'"a";'"f"['"x"]}}} }

interactive nuprl_sum_constant   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"a"};"mul"[]{'"a";'"n"}} }

interactive nuprl_sum_functionality  '"n" "lambda"[]{"x".'"g"['"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"g"['"x"] in "int"[]{} }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};'"n"}  >- "equal"[]{"int"[]{};'"f"['"i"];'"g"['"i"]} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"sum"[]{'"n";"x".'"g"['"x"]}} }

interactive nuprl_sum_difference  '"n" '"d" "lambda"[]{"x".'"g"['"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"g"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x"."sub"[]{'"f"['"x"];'"g"['"x"]}};'"d"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"add"[]{"sum"[]{'"n";"x".'"g"['"x"]};'"d"}} }

interactive nuprl_sum_le  '"k" "lambda"[]{"x".'"g"['"x"]} "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"g"['"x"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"k"}  >- "le"[]{'"f"['"x"];'"g"['"x"]} }  -->
   sequent { <H> >- "le"[]{"sum"[]{'"k";"x".'"f"['"x"]};"sum"[]{'"k";"x".'"g"['"x"]}} }

interactive nuprl_sum_bound  '"k" '"b" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f"['"x"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"k"}  >- "le"[]{'"f"['"x"];'"b"} }  -->
   sequent { <H> >- "le"[]{"sum"[]{'"k";"x".'"f"['"x"]};"mul"[]{'"b";'"k"}} }

interactive nuprl_sum_lower_bound  '"k" "lambda"[]{"x".'"f"['"x"]} '"b"  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f"['"x"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"k"}  >- "le"[]{'"b";'"f"['"x"]} }  -->
   sequent { <H> >- "le"[]{"mul"[]{'"b";'"k"};"sum"[]{'"k";"x".'"f"['"x"]}} }

interactive nuprl_sum__ite  '"k" "lambda"[]{"x".'"g"['"x"]} "lambda"[]{"x".'"f"['"x"]} "lambda"[]{"x".'"p"['"x"]}  :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"g"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"p"['"x"] in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"k";"i"."ifthenelse"[]{'"p"['"i"];"add"[]{'"f"['"i"];'"g"['"i"]};'"f"['"i"]}};"add"[]{"sum"[]{'"k";"i".'"f"['"i"]};"sum"[]{'"k";"i"."ifthenelse"[]{'"p"['"i"];'"g"['"i"];"number"[0:n]{}}}}} }

interactive nuprl_sum_arith1   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{"sum"[]{'"n";"i"."add"[]{'"a";"mul"[]{'"b";'"i"}}};"number"[2:n]{}};"mul"[]{'"n";"add"[]{'"a";"add"[]{'"a";"mul"[]{'"b";"sub"[]{'"n";"number"[1:n]{}}}}}}} }

interactive nuprl_sum_arith   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"i"."add"[]{'"a";"mul"[]{'"b";'"i"}}};"div"[]{"mul"[]{'"n";"add"[]{'"a";"add"[]{'"a";"mul"[]{'"b";"sub"[]{'"n";"number"[1:n]{}}}}}};"number"[2:n]{}}} }

interactive nuprl_finite__partition   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"c" '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "exists"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."list"[]{"nat"[]{}}};"p"."and"[]{"equal"[]{"int"[]{};"sum"[]{'"k";"j"."length"[]{('"p" '"j")}};'"n"};"and"[]{"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"p" '"j")}};"x"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"p" '"j")}};"y"."implies"[]{"lt"[]{'"x";'"y"};"gt"[]{"select"[]{'"x";('"p" '"j")};"select"[]{'"y";('"p" '"j")}}}}}};"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."all"[]{"int_seg"[]{"number"[0:n]{};"length"[]{('"p" '"j")}};"x"."cand"[]{"lt"[]{"select"[]{'"x";('"p" '"j")};'"n"};"equal"[]{"int"[]{};('"c" "select"[]{'"x";('"p" '"j")});'"j"}}}}}}} }

interactive nuprl_pigeon__hole  '"f"  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f" '"x" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- "inject"[]{"int_seg"[]{"number"[0:n]{};'"n"};"int_seg"[]{"number"[0:n]{};'"m"};'"f"} }  -->
   sequent { <H> >- "le"[]{'"n";'"m"} }

interactive nuprl_isolate_summand  '"n" '"m" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"add"[]{'"f"['"m"];"sum"[]{'"n";"x"."ifthenelse"[]{"beq_int"[]{'"x";'"m"};"number"[0:n]{};'"f"['"x"]}}}} }

interactive nuprl_empty_support  '"n" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"}  >- "equal"[]{"int"[]{};'"f"['"x"];"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"number"[0:n]{}} }

interactive nuprl_singleton_support_sum  '"n" "lambda"[]{"x".'"f"['"x"]} '"m"  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"} ; "not"[]{"equal"[]{"int"[]{};'"x";'"m"}}  >- "equal"[]{"int"[]{};'"f"['"x"];"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};'"f"['"m"]} }

interactive nuprl_pair_support  '"n" '"k" '"m" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   [wf] sequent { <H> >- '"k" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"int"[]{};'"m";'"k"}} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"} ; "not"[]{"equal"[]{"int"[]{};'"x";'"m"}} ; "not"[]{"equal"[]{"int"[]{};'"x";'"k"}}  >- "equal"[]{"int"[]{};'"f"['"x"];"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"add"[]{'"f"['"m"];'"f"['"k"]}} }

interactive nuprl_sum_split  '"n" '"m" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "int_seg"[]{"number"[0:n]{};"add"[]{'"n";"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"['"x"]};"add"[]{"sum"[]{'"m";"x".'"f"['"x"]};"sum"[]{"sub"[]{'"n";'"m"};"x".'"f"["add"[]{'"x";'"m"}]}}} }

define unfold_double_sum : "double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]} <-->
      "sum"[]{'"n";"x"."sum"[]{'"m";"y".'"f"['"x";'"y"]}}


interactive nuprl_double_sum_wf {| intro[] |}  '"m" '"n" "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"f"['"x";'"x1"] in "int"[]{} }  -->
   sequent { <H> >- ("double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]} in "int"[]{}) }

interactive nuprl_pair_support_double_sum  '"m" '"n" '"y2" '"y1" '"x2" '"x1" "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"f"['"x";'"x1"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x1" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   [wf] sequent { <H> >- '"x2" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   [wf] sequent { <H> >- '"y1" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   [wf] sequent { <H> >- '"y2" in "int_seg"[]{"number"[0:n]{};'"m"} }  -->
   sequent { <H> >- "or"[]{"not"[]{"equal"[]{"int"[]{};'"x1";'"x2"}};"not"[]{"equal"[]{"int"[]{};'"y1";'"y2"}}} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"} ; "y": "int_seg"[]{"number"[0:n]{};'"m"} ; "not"[]{"and"[]{"equal"[]{"int"[]{};'"x";'"x1"};"equal"[]{"int"[]{};'"y";'"y1"}}} ; "not"[]{"and"[]{"equal"[]{"int"[]{};'"x";'"x2"};"equal"[]{"int"[]{};'"y";'"y2"}}}  >- "equal"[]{"int"[]{};'"f"['"x";'"y"];"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]};"add"[]{'"f"['"x1";'"y1"];'"f"['"x2";'"y2"]}} }

interactive nuprl_double_sum_difference  '"m" '"n" '"d" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"f"['"x";'"x1"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"g"['"x";'"x1"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"d" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"double_sum"[]{'"n";'"m";"x", "y"."sub"[]{'"f"['"x";'"y"];'"g"['"x";'"y"]}};'"d"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]};"add"[]{"double_sum"[]{'"n";'"m";"x", "y".'"g"['"x";'"y"]};'"d"}} }

interactive nuprl_double_sum_functionality  '"m" '"n" "lambda"[]{"x1", "x".'"g"['"x1";'"x"]} "lambda"[]{"x1", "x".'"f"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"f"['"x";'"x1"] in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"m"} >- '"g"['"x";'"x1"] in "int"[]{} }  -->
   sequent { <H>; "x": "int_seg"[]{"number"[0:n]{};'"n"} ; "y": "int_seg"[]{"number"[0:n]{};'"m"}  >- "equal"[]{"int"[]{};'"f"['"x";'"y"];'"g"['"x";'"y"]} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"double_sum"[]{'"n";'"m";"x", "y".'"f"['"x";'"y"]};"double_sum"[]{'"n";'"m";"x", "y".'"g"['"x";'"y"]}} }

define unfold_rel_exp : "rel_exp"[]{'"T";'"R";'"n"} <-->
      (("ycomb"[]{} "lambda"[]{"rel_exp"."lambda"[]{"n"."ifthenelse"[]{"beq_int"[]{'"n";"number"[0:n]{}};"lambda"[]{"x"."lambda"[]{"y"."equal"[]{'"T";'"x";'"y"}}};"lambda"[]{"x"."lambda"[]{"y"."exists"[]{'"T";"z"."and"[]{"infix_ap"[]{'"R";'"x";'"z"};"infix_ap"[]{('"rel_exp" "sub"[]{'"n";"number"[1:n]{}});'"z";'"y"}}}}}}}}) '"n")


interactive nuprl_rel_exp_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_exp"[]{'"T";'"R";'"n"} in "fun"[]{'"T";""."fun"[]{'"T";""."univ"[level:l]{}}}) }

interactive nuprl_decidable__rel_exp   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"};"x1": "int_seg"[]{"number"[0:n]{};'"n"} >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H>; "i": "int_seg"[]{"number"[0:n]{};'"n"} ; "j": "int_seg"[]{"number"[0:n]{};'"n"}  >- "decidable"[]{"infix_ap"[]{'"R";'"i";'"j"}} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"n"} }  -->
   sequent { <H> >- "decidable"[]{"infix_ap"[]{"rel_exp"[]{"int_seg"[]{"number"[0:n]{};'"n"};'"R";'"k"};'"i";'"j"}} }

interactive nuprl_rel_exp_add  '"y"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_exp"[]{'"T";'"R";'"m"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"y";'"z"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_exp"[]{'"T";'"R";"add"[]{'"m";'"n"}};'"x";'"z"} }

define unfold_rel_implies : "rel_implies"[]{'"T";'"R1";'"R2"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}


interactive nuprl_rel_implies_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R1" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R2" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_implies"[]{'"T";'"R1";'"R2"} in "univ"[level:l]{}) }

interactive nuprl_rel_exp_monotone   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R1";'"R2"} }  -->
   sequent { <H> >- "rel_implies"[]{'"T";"rel_exp"[]{'"T";'"R1";'"n"};"rel_exp"[]{'"T";'"R2";'"n"}} }

define unfold_preserved_by : "preserved_by"[]{'"T";'"R";'"P"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{('"P" '"x");"implies"[]{"infix_ap"[]{'"R";'"x";'"y"};('"P" '"y")}}}}


interactive nuprl_preserved_by_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("preserved_by"[]{'"T";'"R";'"P"} in "univ"[level:l]{}) }

interactive nuprl_preserved_by_monotone  '"R2"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H>; "x": '"T" ; "y": '"T" ; "infix_ap"[]{'"R1";'"x";'"y"}  >- "infix_ap"[]{'"R2";'"x";'"y"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R2";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }

define unfold_cond_rel_implies : "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{('"P" '"x");"implies"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}}


interactive nuprl_cond_rel_implies_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R1" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R2" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} in "univ"[level:l]{}) }

interactive nuprl_cond_rel_exp_monotone   :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";"rel_exp"[]{'"T";'"R1";'"n"};"rel_exp"[]{'"T";'"R2";'"n"}} }

define unfold_rel_star : "rel_star"[]{'"T";'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."exists"[]{"nat"[]{};"n"."infix_ap"[]{"rel_exp"[]{'"T";'"R";'"n"};'"x";'"y"}}}}


interactive nuprl_rel_star_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_star"[]{'"T";'"R"} in "fun"[]{'"T";""."fun"[]{'"T";""."univ"[level:l]{}}}) }

interactive nuprl_rel_star_monotone   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R1";'"R2"} }  -->
   sequent { <H> >- "rel_implies"[]{'"T";"rel_star"[]{'"T";'"R1"};"rel_star"[]{'"T";'"R2"}} }

interactive nuprl_cond_rel_star_monotone   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";"rel_star"[]{'"T";'"R1"};"rel_star"[]{'"T";'"R2"}} }

interactive nuprl_rel_star_transitivity  '"y"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"y";'"z"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"z"} }

interactive nuprl_rel_star_monotonic  '"R1"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R1";'"R2"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R1"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R2"};'"x";'"y"} }

interactive nuprl_cond_rel_star_monotonic  '"R1" '"P"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- ('"P" '"x") }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R1"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R2"};'"x";'"y"} }

interactive nuprl_preserved_by_star   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";"rel_star"[]{'"T";'"R"};'"P"} }

interactive nuprl_rel_star_closure  '"T" "lambda"[]{"x1", "x".'"R2"['"x1";'"x"]} '"R" '"y" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2"['"x";'"x1"] } }  -->
   sequent { <H> >- "trans"[]{'"T";"_1", "_2".'"R2"['"_1";'"_2"]} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T" ; "infix_ap"[]{'"R";'"x";'"y"}  >- "infix_ap"[]{"lambda"[]{"x1"."lambda"[]{"x".'"R2"['"x1";'"x"]}};'"x";'"y"} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "or"[]{"infix_ap"[]{"lambda"[]{"x1"."lambda"[]{"x".'"R2"['"x1";'"x"]}};'"x";'"y"};"equal"[]{'"T";'"x";'"y"}} }

interactive nuprl_rel_star_closure2  '"T" "lambda"[]{"x1", "x".'"R2"['"x1";'"x"]} '"R" '"y" '"x"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2"['"x";'"x1"] } }  -->
   sequent { <H> >- "refl"[]{'"T";"_1", "_2".'"R2"['"_1";'"_2"]} }  -->
   sequent { <H> >- "trans"[]{'"T";"_1", "_2".'"R2"['"_1";'"_2"]} }  -->
   sequent { <H>; "x": '"T" ; "y": '"T" ; "infix_ap"[]{'"R";'"x";'"y"}  >- '"R2"['"x";'"y"] }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- '"R2"['"x";'"y"] }

interactive nuprl_rel_star_of_equiv  '"T"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"_1", "_2"."infix_ap"[]{'"E";'"_1";'"_2"}} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"E"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{'"E";'"x";'"y"} }

interactive nuprl_cond_rel_star_equiv   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"E" '"x" '"x1" } }  -->
   sequent { <H> >- "equiv_rel"[]{'"T";"_1", "_2"."infix_ap"[]{'"E";'"_1";'"_2"}} }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";'"R1";'"E"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }  -->
   sequent { <H> >- "cond_rel_implies"[]{'"T";'"P";"rel_star"[]{'"T";'"R1"};'"E"} }

interactive nuprl_rel_rel_star   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{'"R";'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }

interactive nuprl_rel_star_trans  '"y"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H> >- '"z" in '"T" }  -->
   sequent { <H> >- "infix_ap"[]{'"R";'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"y";'"z"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"z"} }

interactive nuprl_rel_star_weakening   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "equal"[]{'"T";'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }

define unfold_rel_inverse : "rel_inverse"[]{'"R"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."infix_ap"[]{'"R";'"y";'"x"}}}


interactive nuprl_rel_inverse_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T1";"x1": '"T2" >- '"R" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_inverse"[]{'"R"} in "fun"[]{'"T2";""."fun"[]{'"T1";""."univ"[level:l]{}}}) }

interactive nuprl_rel_inverse_exp   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_inverse"[]{"rel_exp"[]{'"T";'"R";'"n"}};'"x";'"y"};"infix_ap"[]{"rel_exp"[]{'"T";"rel_inverse"[]{'"R"};'"n"};'"x";'"y"}} }

interactive nuprl_rel_inverse_star   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "iff"[]{"infix_ap"[]{"rel_inverse"[]{"rel_star"[]{'"T";'"R"}};'"x";'"y"};"infix_ap"[]{"rel_star"[]{'"T";"rel_inverse"[]{'"R"}};'"x";'"y"}} }

interactive nuprl_rel_star_symmetric   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{'"R";'"x";'"y"}} }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"}} }

interactive nuprl_rel_star_symmetric_2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"y" in '"T" }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{'"R";'"x";'"y"}} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"x";'"y"} }  -->
   sequent { <H> >- "infix_ap"[]{"rel_star"[]{'"T";'"R"};'"y";'"x"} }

interactive nuprl_preserved_by_symmetric   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{'"R";'"x";'"y"}} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";"rel_inverse"[]{'"R"};'"P"} }

define unfold_rel_or : "rel_or"[]{'"R1";'"R2"} <-->
      "lambda"[]{"x"."lambda"[]{"y"."or"[]{"infix_ap"[]{'"R1";'"x";'"y"};"infix_ap"[]{'"R2";'"x";'"y"}}}}


interactive nuprl_rel_or_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R1" '"x" '"x1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"R2" '"x" '"x1" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("rel_or"[]{'"R1";'"R2"} in "fun"[]{'"T";""."fun"[]{'"T";""."univ"[level:l]{}}}) }

interactive nuprl_rel_implies_or_left   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R1";"rel_or"[]{'"R1";'"R2"}} }

interactive nuprl_rel_implies_or_right   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "rel_implies"[]{'"T";'"R2";"rel_or"[]{'"R1";'"R2"}} }

interactive nuprl_symmetric_rel_or   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{'"R1";'"x";'"y"}} }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{'"R2";'"x";'"y"}} }  -->
   sequent { <H> >- "sym"[]{'"T";"x", "y"."infix_ap"[]{"rel_or"[]{'"R1";'"R2"};'"x";'"y"}} }

interactive nuprl_preserved_by_or   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R1" '"x" '"x1" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R2" '"x" '"x1" } }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R1";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R2";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";"rel_or"[]{'"R1";'"R2"};'"P"} }

define unfold_as_strong : "as_strong"[]{'"T";'"Q";'"P"} <-->
      "all"[]{'"T";"x"."implies"[]{('"P" '"x");('"Q" '"x")}}


interactive nuprl_as_strong_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"Q" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("as_strong"[]{'"T";'"Q";'"P"} in "univ"[level:l]{}) }

interactive nuprl_as_strong_transitivity  '"Q"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"R" '"x" } }  -->
   sequent { <H> >- "as_strong"[]{'"T";'"Q";'"P"} }  -->
   sequent { <H> >- "as_strong"[]{'"T";'"R";'"Q"} }  -->
   sequent { <H> >- "as_strong"[]{'"T";'"R";'"P"} }

define unfold_fun_exp : "fun_exp"[]{'"f";'"n"} <-->
      "primrec"[]{'"n";"lambda"[]{"x".'"x"};"lambda"[]{"i"."lambda"[]{"g"."compose"[]{'"f";'"g"}}}}


interactive nuprl_fun_exp_wf {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- ("fun_exp"[]{'"f";'"n"} in "fun"[]{'"T";"".'"T"}) }

interactive nuprl_comb_for_fun_exp_wf   :
   sequent { <H> >- ("lambda"[]{"T"."lambda"[]{"n"."lambda"[]{"f"."lambda"[]{"z"."fun_exp"[]{'"f";'"n"}}}}} in "fun"[]{"univ"[level:l]{};"T"."fun"[]{"nat"[]{};"n"."fun"[]{"fun"[]{'"T";"".'"T"};"f"."fun"[]{"squash"[]{"true"[]{}};""."fun"[]{'"T";"".'"T"}}}}}) }

interactive nuprl_fun_exp_compose   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"h" '"x" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"T";"".'"T"};"compose"[]{"fun_exp"[]{'"f";'"n"};'"h"};"primrec"[]{'"n";'"h";"lambda"[]{"i"."lambda"[]{"g"."compose"[]{'"f";'"g"}}}}} }

interactive nuprl_fun_exp_add   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"m" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"T";"".'"T"};"fun_exp"[]{'"f";"add"[]{'"n";'"m"}};"compose"[]{"fun_exp"[]{'"f";'"n"};"fun_exp"[]{'"f";'"m"}}} }

interactive nuprl_fun_exp_add1   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "equal"[]{'"T";('"f" ("fun_exp"[]{'"f";'"n"} '"x"));("fun_exp"[]{'"f";"add"[]{'"n";"number"[1:n]{}}} '"x")} }

interactive nuprl_fun_exp_add1_sub   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "equal"[]{'"T";('"f" ("fun_exp"[]{'"f";"sub"[]{'"n";"number"[1:n]{}}} '"x"));("fun_exp"[]{'"f";'"n"} '"x")} }

interactive nuprl_iteration_terminates  '"m"  :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- '"f" '"x" in '"T" }  -->
   [wf] sequent { <H>;"x": '"T" >- '"m" '"x" in "nat"[]{} }  -->
   sequent { <H>; "x": '"T"  >- "and"[]{"le"[]{('"m" ('"f" '"x"));('"m" '"x")};"implies"[]{"equal"[]{"int"[]{};('"m" ('"f" '"x"));('"m" '"x")};"equal"[]{'"T";('"f" '"x");'"x"}}} }  -->
   [wf] sequent { <H> >- '"x" in '"T" }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"n"."equal"[]{'"T";('"f" ("fun_exp"[]{'"f";'"n"} '"x"));("fun_exp"[]{'"f";'"n"} '"x")}} }

define unfold_flip : "flip"[]{'"i";'"j"} <-->
      "lambda"[]{"x"."ifthenelse"[]{"beq_int"[]{'"x";'"i"};'"j";"ifthenelse"[]{"beq_int"[]{'"x";'"j"};'"i";'"x"}}}


interactive nuprl_flip_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- ("flip"[]{'"i";'"j"} in "fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"k"}}) }

interactive nuprl_sum_switch  '"n" '"i" "lambda"[]{"x".'"f"['"x"]}  :
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"n"} >- '"f"['"x"] in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};"sub"[]{'"n";"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"sum"[]{'"n";"x".'"f"[("flip"[]{'"i";"add"[]{'"i";"number"[1:n]{}}} '"x")]};"sum"[]{'"n";"x".'"f"['"x"]}} }

interactive nuprl_flip_symmetry   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "equal"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"k"}};"flip"[]{'"i";'"j"};"flip"[]{'"j";'"i"}} }

interactive nuprl_flip_bijection   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"j" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "biject"[]{"int_seg"[]{"number"[0:n]{};'"k"};"int_seg"[]{"number"[0:n]{};'"k"};"flip"[]{'"i";'"j"}} }

interactive nuprl_flip_inverse   :
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"y" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "equal"[]{"fun"[]{"int_seg"[]{"number"[0:n]{};'"k"};""."int_seg"[]{"number"[0:n]{};'"k"}};"compose"[]{"flip"[]{'"y";'"x"};"flip"[]{'"y";'"x"}};"lambda"[]{"x".'"x"}} }

interactive nuprl_flip_twice  '"k"  :
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"y" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   [wf] sequent { <H> >- '"i" in "int_seg"[]{"number"[0:n]{};'"k"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};("flip"[]{'"y";'"x"} ("flip"[]{'"y";'"x"} '"i"));'"i"} }

define unfold_search : "search"[]{'"k";'"P"} <-->
      "primrec"[]{'"k";"number"[0:n]{};"lambda"[]{"i"."lambda"[]{"j"."ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};'"j"};'"j";"ifthenelse"[]{('"P" '"i");"add"[]{'"i";"number"[1:n]{}};"number"[0:n]{}}}}}}


interactive nuprl_search_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- ("search"[]{'"k";'"P"} in "int_seg"[]{"number"[0:n]{};"add"[]{'"k";"number"[1:n]{}}}) }

interactive nuprl_search_property   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};'"k"} >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "and"[]{"iff"[]{"exists"[]{"int_seg"[]{"number"[0:n]{};'"k"};"i"."assert"[]{('"P" '"i")}};"lt"[]{"number"[0:n]{};"search"[]{'"k";'"P"}}};"implies"[]{"lt"[]{"number"[0:n]{};"search"[]{'"k";'"P"}};"and"[]{"assert"[]{('"P" "sub"[]{"search"[]{'"k";'"P"};"number"[1:n]{}})};"all"[]{"int_seg"[]{"number"[0:n]{};'"k"};"j"."implies"[]{"lt"[]{'"j";"sub"[]{"search"[]{'"k";'"P"};"number"[1:n]{}}};"not"[]{"assert"[]{('"P" '"j")}}}}}}} }

interactive nuprl_search_succ   :
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{"number"[0:n]{};"add"[]{'"k";"number"[1:n]{}}} >- '"P" '"x" in "bool"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"search"[]{"add"[]{'"k";"number"[1:n]{}};'"P"};"ifthenelse"[]{('"P" "number"[0:n]{});"number"[1:n]{};"ifthenelse"[]{"lt_bool"[]{"number"[0:n]{};"search"[]{'"k";"lambda"[]{"i".('"P" "add"[]{'"i";"number"[1:n]{}})}}};"add"[]{"search"[]{'"k";"lambda"[]{"i".('"P" "add"[]{'"i";"number"[1:n]{}})}};"number"[1:n]{}};"number"[0:n]{}}}} }

define unfold_prop_and : "prop_and"[]{'"P";'"Q"} <-->
      "lambda"[]{"L"."and"[]{('"P" '"L");('"Q" '"L")}}


interactive nuprl_prop_and_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"Q" '"x" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("prop_and"[]{'"P";'"Q"} in "fun"[]{'"T";""."univ"[level:l]{}}) }

interactive nuprl_and_preserved_by   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- "type"{'"R" '"x" '"x1" } }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R";'"P"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R";'"Q"} }  -->
   sequent { <H> >- "preserved_by"[]{'"T";'"R";"prop_and"[]{'"P";'"Q"}} }

define unfold_preserved_by2 : "preserved_by2"[]{'"T";'"R";'"P"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."all"[]{'"T";"z"."implies"[]{('"P" '"x");"implies"[]{('"P" '"y");"implies"[]{((('"R" '"x") '"y") '"z");('"P" '"z")}}}}}}


interactive nuprl_preserved_by2_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T" >- '"P" '"x" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T";"x2": '"T" >- '"R" '"x" '"x1" '"x2" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("preserved_by2"[]{'"T";'"R";'"P"} in "univ"[level:l]{}) }

interactive nuprl_and_preserved_by2   :
   [wf] sequent { <H> >- "type"{'"T" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"P" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T" >- "type"{'"Q" '"x" } }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T";"x2": '"T" >- "type"{'"R" '"x" '"x1" '"x2" } }  -->
   sequent { <H> >- "preserved_by2"[]{'"T";'"R";'"P"} }  -->
   sequent { <H> >- "preserved_by2"[]{'"T";'"R";'"Q"} }  -->
   sequent { <H> >- "preserved_by2"[]{'"T";'"R";"prop_and"[]{'"P";'"Q"}} }


(**** display forms ****)


dform nuprl_primrec_df : except_mode[src] :: "primrec"[]{'"n";'"b";'"c"} =
   `"primrec(" slot{'"n"} `";" slot{'"b"} `";" slot{'"c"} `")"


dform nuprl_nondecreasing_df : except_mode[src] :: "nondecreasing"[]{'"f";'"k"} =
   `"nondecreasing(" slot{'"f"} `";" slot{'"k"} `")"


dform nuprl_fadd_df : except_mode[src] :: "fadd"[]{'"f";'"g"} =
   `"fadd(" slot{'"f"} `";" slot{'"g"} `")"


dform nuprl_fshift_df : except_mode[src] :: "fshift"[]{'"f";'"x"} =
   `"fshift(" slot{'"f"} `";" slot{'"x"} `")"


dform nuprl_finite_df : except_mode[src] :: "finite"[]{'"T"} =
   `"finite(" slot{'"T"} `")"


dform nuprl_fappend_df : except_mode[src] :: "fappend"[]{'"f";'"n";'"x"} =
   `"" slot{'"f"} `"[" slot{'"n"} `":=" slot{'"x"} `"]"


dform nuprl_sum_df : except_mode[src] :: "sum"[]{'"k";"x".'"f"} =
   `"sum(" slot{'"k"} `";" slot{'"x"} `"." slot{'"f"} `")"

dform nuprl_sum_df : except_mode[src] :: "sum"[]{'"k";"x".'"f"} =
   `"sum(" slot{'"f"} `" | " slot{'"x"} `" < " slot{'"k"} `")"


dform nuprl_double_sum_df : except_mode[src] :: "double_sum"[]{'"n";'"m";"x", "y".'"f"} =
   `"double_sum(" slot{'"n"} `";" slot{'"m"} `";" slot{'"x"} `"," slot{'"y"} `"."
    slot{'"f"} `")"

dform nuprl_double_sum_df : except_mode[src] :: "double_sum"[]{'"n";'"m";"x", "y".'"f"} =
   `"sum(" slot{'"f"} `" | " slot{'"x"} `" < " slot{'"n"} `"; " slot{'"y"} `" < "
    slot{'"m"} `")"


dform nuprl_rel_exp_df1 : except_mode[src] :: "rel_exp"[]{'"T";'"R";'"n"} =
   `"rel_exp(" slot{'"T"} `";" slot{'"R"} `";" slot{'"n"} `")"


dform nuprl_rel_exp_df : except_mode[src] :: "rel_exp"[]{'"T";'"R";'"n"} =
   `"rel_exp(" slot{'"T"} `";" slot{'"R"} `";" slot{'"n"} `")"

dform nuprl_rel_exp_df : except_mode[src] :: "rel_exp"[]{'"T";'"R";'"n"} =
   `"" slot{'"R"} `""  `"" `""  `"" slot{'"n"} `""  `""  `""

dform nuprl_rel_exp_df : except_mode[src] :: "rel_exp"[]{'"T";'"R";'"n"} =
   `"" slot{'"R"} `"^"  `"" slot{'"n"} `""


dform nuprl_rel_implies_df : except_mode[src] :: "rel_implies"[]{'"T";'"R1";'"R2"} =
   `"rel_implies(" slot{'"T"} `";" slot{'"R1"} `";" slot{'"R2"} `")"

dform nuprl_rel_implies_df : except_mode[src] :: "rel_implies"[]{'"T";'"R1";'"R2"} =
   `"" slot{'"R1"} `" => " slot{'"R2"} `""


dform nuprl_preserved_by_df : except_mode[src] :: "preserved_by"[]{'"T";'"R";'"P"} =
   `"preserved_by(" slot{'"T"} `";" slot{'"R"} `";" slot{'"P"} `")"

dform nuprl_preserved_by_df : except_mode[src] :: "preserved_by"[]{'"T";'"R";'"P"} =
   `"" slot{'"R"} `" preserves " slot{'"P"} `""


dform nuprl_cond_rel_implies_df : except_mode[src] :: "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} =
   `"cond_rel_implies(" slot{'"T"} `";" slot{'"P"} `";" slot{'"R1"} `";"
    slot{'"R2"} `")"

dform nuprl_cond_rel_implies_df : except_mode[src] :: "cond_rel_implies"[]{'"T";'"P";'"R1";'"R2"} =
   `"when " slot{'"P"} `", " slot{'"R1"} `" => " slot{'"R2"} `""


dform nuprl_rel_star_df : except_mode[src] :: "rel_star"[]{'"T";'"R"} =
   `"rel_star(" slot{'"T"} `";" slot{'"R"} `")"

dform nuprl_rel_star_df : except_mode[src] :: "rel_star"[]{'"T";'"R"} =
   `"" slot{'"R"} `"" `""  `"" `"*" `""  `""  `""

dform nuprl_rel_star_df : except_mode[src] :: "rel_star"[]{'"T";'"R"} =
   `"" slot{'"R"} `"^*"


dform nuprl_rel_inverse_df : except_mode[src] :: "rel_inverse"[]{'"R"} =
   `"rel_inverse(" slot{'"R"} `")"

dform nuprl_rel_inverse_df : except_mode[src] :: "rel_inverse"[]{'"R"} =
   `"" slot{'"R"} `"^-1"


dform nuprl_rel_or_df : except_mode[src] :: "rel_or"[]{'"R1";'"R2"} =
   `"rel_or(" slot{'"R1"} `";" slot{'"R2"} `")"

dform nuprl_rel_or_df : except_mode[src] :: "rel_or"[]{'"P";'"Q"} =
   `"" szone `"" slot{'"P"} `"" sbreak[""," "] `"" vee `" " pushm[0:n] `"" slot{'"Q"}
    `"" popm  `"" ezone `""

dform nuprl_rel_or_df : except_mode[src] :: "rel_or"[]{'"P";'"#"} =
   `"" szone `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" vee `" "
    slot{'"#"} `"" ezone `""

dform nuprl_rel_or_df : except_mode[src] :: "rel_or"[]{'"P";'"Q"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" vee `" " pushm[0:n]
    `"" slot{'"Q"} `"" popm  `""

dform nuprl_rel_or_df : except_mode[src] :: "rel_or"[]{'"P";'"#"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" vee `" " slot{'"#"}
    `""


dform nuprl_as_strong_df : except_mode[src] :: "as_strong"[]{'"T";'"Q";'"P"} =
   `"as_strong(" slot{'"T"} `";" slot{'"Q"} `";" slot{'"P"} `")"

dform nuprl_as_strong_df : except_mode[src] :: "as_strong"[]{'"T";'"Q";'"P"} =
   `"" szone `"" pushm[0:n] `"" slot{'"P"} `"" sbreak[""," "] `"as strong as"
    sbreak[""," "] `"" slot{'"Q"} `"" popm ezone `" "


dform nuprl_fun_exp_df : except_mode[src] :: "fun_exp"[]{'"f";'"n"} =
   `"fun_exp(" slot{'"f"} `";" slot{'"n"} `")"

dform nuprl_fun_exp_df : except_mode[src] :: "fun_exp"[]{'"f";'"n"} =
   `"" slot{'"f"} `"^" slot{'"n"} `""


dform nuprl_flip_df : except_mode[src] :: "flip"[]{'"i";'"j"} =
   `"flip(" slot{'"i"} `";" slot{'"j"} `")"

dform nuprl_flip_df : except_mode[src] :: "flip"[]{'"i";'"j"} =
   `"(" slot{'"i"} `", " slot{'"j"} `")"


dform nuprl_search_df : except_mode[src] :: "search"[]{'"k";'"P"} =
   `"search(" slot{'"k"} `";" slot{'"P"} `")"


dform nuprl_prop_and_df : except_mode[src] :: "prop_and"[]{'"P";'"Q"} =
   `"" szone `"" slot{'"P"} `"" sbreak[""," "] `"" wedge `" " pushm[0:n] `"" slot{'"Q"}
    `"" popm  `"" ezone `""

dform nuprl_prop_and_df : except_mode[src] :: "prop_and"[]{'"P";'"#"} =
   `"" szone `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" wedge `" "
    slot{'"#"} `"" ezone `""

dform nuprl_prop_and_df : except_mode[src] :: "prop_and"[]{'"P";'"Q"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" wedge `" " pushm[0:n]
    `"" slot{'"Q"} `"" popm  `""

dform nuprl_prop_and_df : except_mode[src] :: "prop_and"[]{'"P";'"#"} =
   `"" pushm[0:n] `"" slot{'"P"} `"" popm  `"" sbreak[""," "] `"" wedge `" " slot{'"#"}
    `""


dform nuprl_preserved_by2_df : except_mode[src] :: "preserved_by2"[]{'"T";'"R";'"P"} =
   `"preserved_by2(" slot{'"T"} `";" slot{'"R"} `";" slot{'"P"} `")"

dform nuprl_preserved_by2_df : except_mode[src] :: "preserved_by2"[]{'"T";'"R";'"P"} =
   `"(ternary) " slot{'"R"} `" preserves " slot{'"P"} `" "


