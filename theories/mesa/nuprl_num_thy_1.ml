extends Ma_list_1

open Dtactic


define unfold_divides : "divides"[]{'"b";'"a"} <-->
      "exists"[]{"int"[]{};"c"."equal"[]{"int"[]{};'"a";"mul"[]{'"b";'"c"}}}


interactive nuprl_divides_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("divides"[]{'"a";'"b"} in "univ"[1:l]{}) }

interactive nuprl_comb_for_divides_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."divides"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

interactive nuprl_zero_divs_only_zero   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{"number"[0:n]{};'"a"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";"number"[0:n]{}} }

interactive nuprl_one_divs_any   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{"number"[1:n]{};'"a"} }

interactive nuprl_any_divs_zero   :
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"b";"number"[0:n]{}} }

interactive nuprl_divides_invar_1   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"a";'"b"};"divides"[]{"minus"[]{'"a"};'"b"}} }

interactive nuprl_divides_invar_2   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"a";'"b"};"divides"[]{'"a";"minus"[]{'"b"}}} }

interactive nuprl_divisors_bound   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "le"[]{'"a";'"b"} }

interactive nuprl_only_pm_one_divs_one   :
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"b";"number"[1:n]{}} }  -->
   sequent { <H> >- "pm_equal"[]{'"b";"number"[1:n]{}} }

interactive nuprl_divides_of_absvals   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{"absval"[]{'"a"};"absval"[]{'"b"}};"divides"[]{'"a";'"b"}} }

interactive nuprl_divides_reflexivity   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"a"} }

interactive nuprl_divides_transitivity  '"b"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"b";'"c"} }  -->
   sequent { <H> >- "divides"[]{'"a";'"c"} }

interactive nuprl_divides_preorder   :
   sequent { <H> >- "preorder"[]{"int"[]{};"x", "y"."divides"[]{'"x";'"y"}} }

interactive nuprl_divides_anti_sym_n   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"b";'"a"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";'"b"} }

interactive nuprl_divides_anti_sym   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"b";'"a"} }  -->
   sequent { <H> >- "pm_equal"[]{'"a";'"b"} }

interactive nuprl_assoc_reln   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"and"[]{"divides"[]{'"a";'"b"};"divides"[]{'"b";'"a"}};"pm_equal"[]{'"a";'"b"}} }

interactive nuprl_divisor_of_sum   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b2" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b1"} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b2"} }  -->
   sequent { <H> >- "divides"[]{'"a";"add"[]{'"b1";'"b2"}} }

interactive nuprl_divisor_of_minus   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"a";"minus"[]{'"b"}} }

interactive nuprl_divisor_of_mul   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"a";"mul"[]{'"b";'"c"}} }

interactive nuprl_divides_mul   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }

interactive nuprl_divisor_bound   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }  -->
   sequent { <H> >- "le"[]{'"a";'"b"} }

interactive nuprl_divides_iff_rem_zero   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"b";'"a"};"equal"[]{"int"[]{};"rem"[]{'"a";'"b"};"number"[0:n]{}}} }

interactive nuprl_divides_iff_div_exact   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"n";'"a"};"equal"[]{"int"[]{};"mul"[]{"div"[]{'"a";'"n"};'"n"};'"a"}} }

interactive nuprl_decidable__divides   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "decidable"[]{"divides"[]{'"a";'"b"}} }

interactive nuprl_divides_instance   :
   sequent { <H> >- "divides"[]{"number"[3:n]{};"number"[6:n]{}} }

define unfold_assoced : "assoced"[]{'"a";'"b"} <-->
      "and"[]{"divides"[]{'"a";'"b"};"divides"[]{'"b";'"a"}}


interactive nuprl_assoced_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("assoced"[]{'"a";'"b"} in "univ"[1:l]{}) }

interactive nuprl_comb_for_assoced_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."assoced"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}) }

interactive nuprl_assoced_equiv_rel   :
   sequent { <H> >- "equiv_rel"[]{"int"[]{};"x", "y"."assoced"[]{'"x";'"y"}} }

interactive nuprl_decidable__assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "decidable"[]{"assoced"[]{'"a";'"b"}} }

interactive nuprl_divides_functionality_wrt_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"a'" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b'" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"a'"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"b'"} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"a";'"b"};"divides"[]{'"a'";'"b'"}} }

interactive nuprl_divides_weakening   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"a";'"b"} }

interactive nuprl_assoced_weakening   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";'"b"} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"b"} }

interactive nuprl_assoced_transitivity  '"b"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"b"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"c"} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"c"} }

interactive nuprl_multiply_functionality_wrt_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"a'" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b'" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"a'"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"b'"} }  -->
   sequent { <H> >- "assoced"[]{"mul"[]{'"a";'"b"};"mul"[]{'"a'";'"b'"}} }

interactive nuprl_assoced_inversion   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"b"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"a"} }

interactive nuprl_assoced_functionality_wrt_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"a'" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b'" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"a'"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"b'"} }  -->
   sequent { <H> >- "iff"[]{"assoced"[]{'"a";'"b"};"assoced"[]{'"a'";'"b'"}} }

interactive nuprl_assoced_elim   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"assoced"[]{'"a";'"b"};"or"[]{"equal"[]{"int"[]{};'"a";'"b"};"equal"[]{"int"[]{};'"a";"minus"[]{'"b"}}}} }

interactive nuprl_mul_cancel_in_assoced  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "assoced"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"b"} }

interactive nuprl_neg_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{"minus"[]{'"a"};'"a"} }

interactive nuprl_absval_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{"absval"[]{'"a"};'"a"} }

interactive nuprl_unit_chars   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"a";"number"[1:n]{}};"assoced"[]{'"a";"number"[1:n]{}}} }

interactive nuprl_assoced_nelim   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"assoced"[]{'"a";'"b"};"equal"[]{"int"[]{};'"a";'"b"}} }

interactive nuprl_pdivisor_bound   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "iff"[]{"and"[]{"divides"[]{'"a";'"b"};"not"[]{"divides"[]{'"b";'"a"}}};"and"[]{"lt"[]{'"a";'"b"};"divides"[]{'"a";'"b"}}} }

interactive nuprl_divides_nchar   :
   [wf] sequent { <H> >- '"a" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "iff"[]{"divides"[]{'"a";'"b"};"exists"[]{"nat_plus"[]{};"c"."equal"[]{"nat_plus"[]{};'"b";"mul"[]{'"a";'"c"}}}} }

define unfold_gcd_p : "gcd_p"[]{'"a";'"b";'"y"} <-->
      "and"[]{"divides"[]{'"y";'"a"};"and"[]{"divides"[]{'"y";'"b"};"all"[]{"int"[]{};"z"."implies"[]{"and"[]{"divides"[]{'"z";'"a"};"divides"[]{'"z";'"b"}};"divides"[]{'"z";'"y"}}}}}


interactive nuprl_gcd_p_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- ("gcd_p"[]{'"a";'"b";'"y"} in "univ"[1:l]{}) }

interactive nuprl_comb_for_gcd_p_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"y"."lambda"[]{"z"."gcd_p"[]{'"a";'"b";'"y"}}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"int"[]{};"y"."fun"[]{"squash"[]{"true"[]{}};""."univ"[1:l]{}}}}}) }

interactive nuprl_gcd_p_functionality_wrt_assoced   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"a'" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b'" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y'" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{'"a";'"a'"} }  -->
   sequent { <H> >- "assoced"[]{'"b";'"b'"} }  -->
   sequent { <H> >- "assoced"[]{'"y";'"y'"} }  -->
   sequent { <H> >- "iff"[]{"gcd_p"[]{'"a";'"b";'"y"};"gcd_p"[]{'"a'";'"b'";'"y'"}} }

interactive nuprl_gcd_p_eq_args   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"a";'"a"} }

interactive nuprl_gcd_p_zero   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";"number"[0:n]{};'"a"} }

interactive nuprl_gcd_p_one   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";"number"[1:n]{};"number"[1:n]{}} }

interactive nuprl_gcd_p_zero_rel   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";"number"[0:n]{};'"b"} }  -->
   sequent { <H> >- "or"[]{"equal"[]{"int"[]{};'"a";'"b"};"equal"[]{"int"[]{};'"a";"minus"[]{'"b"}}} }

interactive nuprl_gcd_p_sym   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y"} }  -->
   sequent { <H> >- "gcd_p"[]{'"b";'"a";'"y"} }

interactive nuprl_gcd_p_sym_a   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y"} }  -->
   sequent { <H> >- "gcd_p"[]{'"b";'"a";'"y"} }

interactive nuprl_gcd_p_neg_arg   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y"} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";"minus"[]{'"b"};'"y"} }

interactive nuprl_gcd_p_neg_arg_a   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y"} }  -->
   sequent { <H> >- "gcd_p"[]{"minus"[]{'"a"};'"b";'"y"} }

interactive nuprl_gcd_p_neg_arg_2   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"gcd_p"[]{'"a";'"b";'"y"};"gcd_p"[]{'"a";"minus"[]{'"b"};'"y"}} }

interactive nuprl_gcd_p_shift   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y"} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";"add"[]{'"b";"mul"[]{'"k";'"a"}};'"y"} }

interactive nuprl_gcd_unique  '"b" '"a"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y2" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y1"} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"y2"} }  -->
   sequent { <H> >- "assoced"[]{'"y1";'"y2"} }

interactive nuprl_gcd_of_triple  '"x"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";'"x"} }  -->
   sequent { <H> >- "gcd_p"[]{'"x";'"c";'"y"} }  -->
   sequent { <H> >- "and"[]{"and"[]{"divides"[]{'"y";'"a"};"and"[]{"divides"[]{'"y";'"b"};"divides"[]{'"y";'"c"}}};"all"[]{"int"[]{};"z"."implies"[]{"divides"[]{'"z";'"a"};"implies"[]{"divides"[]{'"z";'"b"};"implies"[]{"divides"[]{'"z";'"c"};"divides"[]{'"z";'"y"}}}}}} }

define unfold_gcd : "gcd"[]{'"a";'"b"} <-->
      ((("ycomb"[]{} "lambda"[]{"gcd"."lambda"[]{"a"."lambda"[]{"b"."ifthenelse"[]{"beq_int"[]{'"b";"number"[0:n]{}};'"a";(('"gcd" '"b") "rem"[]{'"a";'"b"})}}}}) '"a") '"b")


interactive nuprl_gcd_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("gcd"[]{'"a";'"b"} in "int"[]{}) }

interactive nuprl_comb_for_gcd_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."gcd"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}}}) }

interactive nuprl_gcd_sat_gcd_p   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";"gcd"[]{'"a";'"b"}} }

interactive nuprl_gcd_sat_pred   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "gcd_p"[]{'"a";'"b";"gcd"[]{'"a";'"b"}} }

interactive nuprl_gcd_elim   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "exists"[]{"int"[]{};"y"."and"[]{"gcd_p"[]{'"a";'"b";'"y"};"equal"[]{"int"[]{};"gcd"[]{'"a";'"b"};'"y"}}} }

interactive nuprl_gcd_sym   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "assoced"[]{"gcd"[]{'"a";'"b"};"gcd"[]{'"b";'"a"}} }

interactive nuprl_gcd_is_divisor_1   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{"gcd"[]{'"a";'"b"};'"a"} }

interactive nuprl_gcd_is_divisor_2   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{"gcd"[]{'"a";'"b"};'"b"} }

interactive nuprl_gcd_is_gcd   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "divides"[]{'"c";'"a"} }  -->
   sequent { <H> >- "divides"[]{'"c";'"b"} }  -->
   sequent { <H> >- "divides"[]{'"c";"gcd"[]{'"a";'"b"}} }

interactive nuprl_quot_rem_exists_n   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"q"."exists"[]{"int_seg"[]{"number"[0:n]{};'"b"};"r"."equal"[]{"int"[]{};'"a";"add"[]{"mul"[]{'"q";'"b"};'"r"}}}} }

interactive nuprl_quot_rem_exists   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "exists"[]{"int"[]{};"q"."exists"[]{"int_seg"[]{"number"[0:n]{};'"b"};"r"."equal"[]{"int"[]{};'"a";"add"[]{"mul"[]{'"q";'"b"};'"r"}}}} }

interactive nuprl_gcd_exists_n   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "exists"[]{"int"[]{};"y"."gcd_p"[]{'"a";'"b";'"y"}} }

interactive nuprl_gcd_ex_n   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "sq_exists"[]{"int"[]{};"y"."gcd_p"[]{'"a";'"b";'"y"}} }

interactive nuprl_gcd_exists   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "exists"[]{"int"[]{};"y"."gcd_p"[]{'"a";'"b";'"y"}} }

interactive nuprl_bezout_ident_n   :
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "exists"[]{"int"[]{};"u"."exists"[]{"int"[]{};"v"."gcd_p"[]{'"a";'"b";"add"[]{"mul"[]{'"u";'"a"};"mul"[]{'"v";'"b"}}}}} }

