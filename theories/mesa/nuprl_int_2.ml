extends Ma_quot_1

open Dtactic


interactive nuprl_int_trichot   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "or"[]{"lt"[]{'"i";'"j"};"or"[]{"equal"[]{"int"[]{};'"i";'"j"};"gt"[]{'"i";'"j"}}} }

interactive nuprl_le_transitivity  '"j"  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }  -->
   sequent { <H> >- "le"[]{'"j";'"k"} }  -->
   sequent { <H> >- "le"[]{'"i";'"k"} }

interactive nuprl_lt_transitivity_1  '"j"  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }  -->
   sequent { <H> >- "le"[]{'"j";'"k"} }  -->
   sequent { <H> >- "lt"[]{'"i";'"k"} }

interactive nuprl_lt_transitivity_2  '"j"  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }  -->
   sequent { <H> >- "lt"[]{'"j";'"k"} }  -->
   sequent { <H> >- "lt"[]{'"i";'"k"} }

interactive nuprl_eq_to_le   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i";'"j"} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }

interactive nuprl_lt_to_le   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"lt"[]{'"i";'"j"};"le"[]{"add"[]{'"i";"number"[1:n]{}};'"j"}} }

interactive nuprl_le_to_lt_weaken   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }  -->
   sequent { <H> >- "le"[]{'"i";'"j"} }

interactive nuprl_lt_to_le_rw   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"lt"[]{'"i";'"j"};"le"[]{"add"[]{'"i";"number"[1:n]{}};'"j"}}} }

interactive nuprl_le_to_lt   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"i";'"j"};"lt"[]{'"i";"add"[]{'"j";"number"[1:n]{}}}} }

interactive nuprl_le_to_lt_rw   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"le"[]{'"i";'"j"};"lt"[]{'"i";"add"[]{'"j";"number"[1:n]{}}}}} }

interactive nuprl_add_ident   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i";"add"[]{'"i";"number"[0:n]{}}} }

interactive nuprl_add_com   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{'"a";'"b"};"add"[]{'"b";'"a"}} }

interactive nuprl_add_functionality_wrt_le   :
   [wf] sequent { <H> >- '"i1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i1";'"j1"} }  -->
   sequent { <H> >- "le"[]{'"i2";'"j2"} }  -->
   sequent { <H> >- "le"[]{"add"[]{'"i1";'"i2"};"add"[]{'"j1";'"j2"}} }

interactive nuprl_add_functionality_wrt_lt   :
   [wf] sequent { <H> >- '"i1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{'"i1";'"j1"} }  -->
   sequent { <H> >- "le"[]{'"i2";'"j2"} }  -->
   sequent { <H> >- "lt"[]{"add"[]{'"i1";'"i2"};"add"[]{'"j1";'"j2"}} }

interactive nuprl_add_functionality_wrt_eq   :
   [wf] sequent { <H> >- '"i1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i1";'"j1"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i2";'"j2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{'"i1";'"i2"};"add"[]{'"j1";'"j2"}} }

interactive nuprl_add_cancel_in_eq  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";'"b"} }

interactive nuprl_add_cancel_in_lt  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "lt"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}} }  -->
   sequent { <H> >- "lt"[]{'"a";'"b"} }

interactive nuprl_add_cancel_in_le  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}} }  -->
   sequent { <H> >- "le"[]{'"a";'"b"} }

interactive nuprl_add_mono_wrt_eq   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};'"a";'"b"};"equal"[]{"int"[]{};"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}} }

interactive nuprl_add_mono_wrt_eq_rw   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"equal"[]{"int"[]{};'"a";'"b"};"equal"[]{"int"[]{};"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}}} }

interactive nuprl_add_mono_wrt_lt   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"lt"[]{'"a";'"b"};"lt"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}} }

interactive nuprl_add_mono_wrt_lt_rw   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"lt"[]{'"a";'"b"};"lt"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}}} }

interactive nuprl_add_mono_wrt_le   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"a";'"b"};"le"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}} }

interactive nuprl_add_mono_wrt_le_rw   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "guard"[]{"iff"[]{"le"[]{'"a";'"b"};"le"[]{"add"[]{'"a";'"n"};"add"[]{'"b";'"n"}}}} }

interactive nuprl_minus_functionality_wrt_le   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "ge"[]{'"i";'"j"} }  -->
   sequent { <H> >- "le"[]{"minus"[]{'"i"};"minus"[]{'"j"}} }

interactive nuprl_minus_mono_wrt_le   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"ge"[]{'"i";'"j"};"le"[]{"minus"[]{'"i"};"minus"[]{'"j"}}} }

interactive nuprl_minus_functionality_wrt_eq   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i";'"j"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{'"i"};"minus"[]{'"j"}} }

interactive nuprl_minus_mono_wrt_eq   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};'"i";'"j"};"equal"[]{"int"[]{};"minus"[]{'"i"};"minus"[]{'"j"}}} }

interactive nuprl_minus_functionality_wrt_lt   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "gt"[]{'"i";'"j"} }  -->
   sequent { <H> >- "lt"[]{"minus"[]{'"i"};"minus"[]{'"j"}} }

interactive nuprl_minus_mono_wrt_lt   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"gt"[]{'"i";'"j"};"lt"[]{"minus"[]{'"i"};"minus"[]{'"j"}}} }

interactive nuprl_sub_functionality_wrt_le   :
   [wf] sequent { <H> >- '"i1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "int"[]{} }  -->
   sequent { <H> >- "le"[]{'"i1";'"j1"} }  -->
   sequent { <H> >- "ge"[]{'"i2";'"j2"} }  -->
   sequent { <H> >- "le"[]{"sub"[]{'"i1";'"i2"};"sub"[]{'"j1";'"j2"}} }

interactive nuprl_minus_minus_cancel   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{"minus"[]{'"a"}};'"a"} }

interactive nuprl_mul_ident   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i";"mul"[]{'"i";"number"[1:n]{}}} }

interactive nuprl_mul_com   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"a";'"b"};"mul"[]{'"b";'"a"}} }

interactive nuprl_zero_ann   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"number"[0:n]{};"mul"[]{'"i";"number"[0:n]{}}} }

interactive nuprl_zero_ann_a   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "or"[]{"equal"[]{"int"[]{};'"a";"number"[0:n]{}};"equal"[]{"int"[]{};'"b";"number"[0:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"a";'"b"};"number"[0:n]{}} }

interactive nuprl_zero_ann_b   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"int"[]{};"mul"[]{'"a";'"b"};"number"[0:n]{}}} }  -->
   sequent { <H> >- "and"[]{"not"[]{"equal"[]{"int"[]{};'"a";"number"[0:n]{}}};"not"[]{"equal"[]{"int"[]{};'"b";"number"[0:n]{}}}} }

interactive nuprl_minus_thru_mul   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{"mul"[]{'"a";'"b"}};"mul"[]{"minus"[]{'"a"};'"b"}} }

interactive nuprl_mul_preserves_eq   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";'"b"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }

interactive nuprl_mul_preserves_lt   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{'"a";'"b"} }  -->
   sequent { <H> >- "lt"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }

interactive nuprl_mul_preserves_le   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "le"[]{'"a";'"b"} }  -->
   sequent { <H> >- "le"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }

interactive nuprl_mul_cancel_in_eq  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";'"b"} }

interactive nuprl_mul_cancel_in_lt  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }  -->
   sequent { <H> >- "lt"[]{'"a";'"b"} }

interactive nuprl_mul_cancel_in_le  '"n"  :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "le"[]{"mul"[]{'"n";'"a"};"mul"[]{'"n";'"b"}} }  -->
   sequent { <H> >- "le"[]{'"a";'"b"} }

interactive nuprl_multiply_functionality_wrt_le   :
   [wf] sequent { <H> >- '"i1" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "nat"[]{} }  -->
   sequent { <H> >- "le"[]{'"i1";'"j1"} }  -->
   sequent { <H> >- "le"[]{'"i2";'"j2"} }  -->
   sequent { <H> >- "le"[]{"mul"[]{'"i1";'"i2"};"mul"[]{'"j1";'"j2"}} }

interactive nuprl_mul_functionality_wrt_eq   :
   [wf] sequent { <H> >- '"i1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"i2" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j1" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j2" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i1";'"j1"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i2";'"j2"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"i1";'"i2"};"mul"[]{'"j1";'"j2"}} }

interactive nuprl_int_entire   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"mul"[]{'"a";'"b"};"number"[0:n]{}} }  -->
   sequent { <H> >- "or"[]{"equal"[]{"int"[]{};'"a";"number"[0:n]{}};"equal"[]{"int"[]{};'"b";"number"[0:n]{}}} }

interactive nuprl_int_entire_a   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "nequal"[]{"int"[]{};'"a";"number"[0:n]{}} }  -->
   sequent { <H> >- "nequal"[]{"int"[]{};'"b";"number"[0:n]{}} }  -->
   sequent { <H> >- "nequal"[]{"int"[]{};"mul"[]{'"a";'"b"};"number"[0:n]{}} }

interactive nuprl_mul_bounds_1a   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   sequent { <H> >- "le"[]{"number"[0:n]{};"mul"[]{'"a";'"b"}} }

interactive nuprl_mul_bounds_1b   :
   [wf] sequent { <H> >- '"a" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{"number"[0:n]{};"mul"[]{'"a";'"b"}} }

interactive nuprl_pos_mul_arg_bounds   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"gt"[]{"mul"[]{'"a";'"b"};"number"[0:n]{}};"or"[]{"and"[]{"gt"[]{'"a";"number"[0:n]{}};"gt"[]{'"b";"number"[0:n]{}}};"and"[]{"lt"[]{'"a";"number"[0:n]{}};"lt"[]{'"b";"number"[0:n]{}}}}} }

interactive nuprl_neg_mul_arg_bounds   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"lt"[]{"mul"[]{'"a";'"b"};"number"[0:n]{}};"or"[]{"and"[]{"lt"[]{'"a";"number"[0:n]{}};"gt"[]{'"b";"number"[0:n]{}}};"and"[]{"gt"[]{'"a";"number"[0:n]{}};"lt"[]{'"b";"number"[0:n]{}}}}} }

interactive nuprl_add_nat_wf   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "nat"[]{} }  -->
   sequent { <H> >- ("add"[]{'"i";'"j"} in "nat"[]{}) }

interactive nuprl_multiply_nat_wf   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "nat"[]{} }  -->
   sequent { <H> >- ("mul"[]{'"i";'"j"} in "nat"[]{}) }

define unfold_absval : "absval"[]{'"i"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"i"};'"i";"minus"[]{'"i"}}


interactive nuprl_absval_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   sequent { <H> >- ("absval"[]{'"x"} in "nat"[]{}) }

interactive nuprl_comb_for_absval_wf   :
   sequent { <H> >- ("lambda"[]{"x"."lambda"[]{"z"."absval"[]{'"x"}}} in "fun"[]{"int"[]{};"x"."fun"[]{"squash"[]{"true"[]{}};""."nat"[]{}}}) }

interactive nuprl_absval_pos   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"absval"[]{'"i"};'"i"} }

interactive nuprl_absval_neg   :
   [wf] sequent { <H> >- '"i" in "int_lower"[]{"number"[0:n]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"absval"[]{'"i"};"minus"[]{'"i"}} }

define unfold_pm_equal : "pm_equal"[]{'"i";'"j"} <-->
      "or"[]{"equal"[]{"int"[]{};'"i";'"j"};"equal"[]{"int"[]{};'"i";"minus"[]{'"j"}}}


interactive nuprl_pm_equal_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("pm_equal"[]{'"a";'"b"} in "univ"[1:l]{}) }

interactive nuprl_absval_zero   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};"absval"[]{'"i"};"number"[0:n]{}};"equal"[]{"int"[]{};'"i";"number"[0:n]{}}} }

interactive nuprl_absval_ubound   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{"absval"[]{'"i"};'"n"};"and"[]{"le"[]{"minus"[]{'"n"};'"i"};"le"[]{'"i";'"n"}}} }

interactive nuprl_absval_lbound   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"gt"[]{"absval"[]{'"i"};'"n"};"or"[]{"lt"[]{'"i";"minus"[]{'"n"}};"gt"[]{'"i";'"n"}}} }

interactive nuprl_absval_eq   :
   [wf] sequent { <H> >- '"x" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};"absval"[]{'"x"};"absval"[]{'"y"}};"pm_equal"[]{'"x";'"y"}} }

interactive nuprl_absval_sym   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"absval"[]{'"i"};"absval"[]{"minus"[]{'"i"}}} }

interactive nuprl_absval_elim  "lambda"[]{"x".'"P"['"x"]}  :
   [wf] sequent { <H>;"x": "int"[]{} >- "type"{'"P"['"x"] } }  -->
   sequent { <H> >- "iff"[]{"all"[]{"int"[]{};"x".'"P"["absval"[]{'"x"}]};"all"[]{"nat"[]{};"x".'"P"['"x"]}} }

define unfold_imax : "imax"[]{'"a";'"b"} <-->
      "ifthenelse"[]{"le_bool"[]{'"a";'"b"};'"b";'"a"}


interactive nuprl_imax_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("imax"[]{'"a";'"b"} in "int"[]{}) }

interactive nuprl_comb_for_imax_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."imax"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}}}) }

define unfold_imin : "imin"[]{'"a";'"b"} <-->
      "ifthenelse"[]{"le_bool"[]{'"a";'"b"};'"a";'"b"}


interactive nuprl_imin_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("imin"[]{'"a";'"b"} in "int"[]{}) }

interactive nuprl_comb_for_imin_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."imin"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}}}) }

interactive nuprl_minus_imax   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{"imax"[]{'"a";'"b"}};"imin"[]{"minus"[]{'"a"};"minus"[]{'"b"}}} }

interactive nuprl_minus_imin   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{"imin"[]{'"a";'"b"}};"imax"[]{"minus"[]{'"a"};"minus"[]{'"b"}}} }

interactive nuprl_imax_lb   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{"imax"[]{'"a";'"b"};'"c"};"guard"[]{"and"[]{"le"[]{'"a";'"c"};"le"[]{'"b";'"c"}}}} }

interactive nuprl_imax_ub   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"a";"imax"[]{'"b";'"c"}};"or"[]{"le"[]{'"a";'"b"};"le"[]{'"a";'"c"}}} }

interactive nuprl_imax_add_r   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{"imax"[]{'"a";'"b"};'"c"};"imax"[]{"add"[]{'"a";'"c"};"add"[]{'"b";'"c"}}} }

interactive nuprl_imax_assoc   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"imax"[]{'"a";"imax"[]{'"b";'"c"}};"imax"[]{"imax"[]{'"a";'"b"};'"c"}} }

interactive nuprl_imax_com   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"imax"[]{'"a";'"b"};"imax"[]{'"b";'"a"}} }

interactive nuprl_imin_assoc   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"imin"[]{'"a";"imin"[]{'"b";'"c"}};"imin"[]{"imin"[]{'"a";'"b"};'"c"}} }

interactive nuprl_imin_com   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"imin"[]{'"a";'"b"};"imin"[]{'"b";'"a"}} }

interactive nuprl_imin_add_r   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{"imin"[]{'"a";'"b"};'"c"};"imin"[]{"add"[]{'"a";'"c"};"add"[]{'"b";'"c"}}} }

interactive nuprl_imin_lb   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{"imin"[]{'"a";'"b"};'"c"};"or"[]{"le"[]{'"a";'"c"};"le"[]{'"b";'"c"}}} }

interactive nuprl_imin_ub   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"a";"imin"[]{'"b";'"c"}};"guard"[]{"and"[]{"le"[]{'"a";'"b"};"le"[]{'"a";'"c"}}}} }

define unfold_ndiff : "ndiff"[]{'"a";'"b"} <-->
      "imax"[]{"sub"[]{'"a";'"b"};"number"[0:n]{}}


interactive nuprl_ndiff_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- ("ndiff"[]{'"a";'"b"} in "int"[]{}) }

interactive nuprl_comb_for_ndiff_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"b"."lambda"[]{"z"."ndiff"[]{'"a";'"b"}}}} in "fun"[]{"int"[]{};"a"."fun"[]{"int"[]{};"b"."fun"[]{"squash"[]{"true"[]{}};""."int"[]{}}}}) }

interactive nuprl_ndiff_id_r   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"ndiff"[]{'"a";"number"[0:n]{}};'"a"} }

interactive nuprl_ndiff_ann_l   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"ndiff"[]{"number"[0:n]{};'"a"};"number"[0:n]{}} }

interactive nuprl_ndiff_inv   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"ndiff"[]{"add"[]{'"a";'"b"};'"b"};'"a"} }

interactive nuprl_ndiff_ndiff   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"c" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"ndiff"[]{"ndiff"[]{'"a";'"b"};'"c"};"ndiff"[]{'"a";"add"[]{'"b";'"c"}}} }

interactive nuprl_ndiff_ndiff_eq_imin   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"ndiff"[]{'"a";"ndiff"[]{'"a";'"b"}};"imin"[]{'"a";'"b"}} }

interactive nuprl_ndiff_add_eq_imax   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"add"[]{"ndiff"[]{'"a";'"b"};'"b"};"imax"[]{'"a";'"b"}} }

interactive nuprl_ndiff_zero   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int"[]{} }  -->
   sequent { <H> >- "iff"[]{"equal"[]{"int"[]{};"ndiff"[]{'"a";'"b"};"number"[0:n]{}};"le"[]{'"a";'"b"}} }

interactive nuprl_div_rem_sum   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";"add"[]{"mul"[]{"div"[]{'"a";'"n"};'"n"};"rem"[]{'"a";'"n"}}} }

interactive nuprl_rem_to_div   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"sub"[]{'"a";"mul"[]{"div"[]{'"a";'"n"};'"n"}}} }

interactive nuprl_rem_bounds_1   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "and"[]{"le"[]{"number"[0:n]{};"rem"[]{'"a";'"n"}};"lt"[]{"rem"[]{'"a";'"n"};'"n"}} }

interactive nuprl_rem_bounds_2   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "and"[]{"ge"[]{"number"[0:n]{};"rem"[]{'"a";'"n"}};"gt"[]{"rem"[]{'"a";'"n"};"minus"[]{'"n"}}} }

interactive nuprl_rem_bounds_3   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"n" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "and"[]{"ge"[]{"number"[0:n]{};"rem"[]{'"a";'"n"}};"gt"[]{"rem"[]{'"a";'"n"};'"n"}} }

interactive nuprl_rem_bounds_4   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "and"[]{"le"[]{"number"[0:n]{};"rem"[]{'"a";'"n"}};"lt"[]{"rem"[]{'"a";'"n"};"minus"[]{'"n"}}} }

interactive nuprl_div_2_to_1   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"b" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"div"[]{'"a";'"b"};"minus"[]{"div"[]{"minus"[]{'"a"};'"b"}}} }

interactive nuprl_div_3_to_1   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"b" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"div"[]{'"a";'"b"};"div"[]{"minus"[]{'"a"};"minus"[]{'"b"}}} }

interactive nuprl_div_4_to_1   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"div"[]{'"a";'"b"};"minus"[]{"div"[]{'"a";"minus"[]{'"b"}}}} }

interactive nuprl_rem_2_to_1   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"minus"[]{"rem"[]{"minus"[]{'"a"};'"n"}}} }

interactive nuprl_rem_3_to_1   :
   [wf] sequent { <H> >- '"a" in "int_lower"[]{"number"[0:n]{}} }  -->
   [wf] sequent { <H> >- '"n" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"minus"[]{"rem"[]{"minus"[]{'"a"};"minus"[]{'"n"}}}} }

interactive nuprl_rem_4_to_1   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_lower"[]{"minus"[]{"number"[1:n]{}}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"rem"[]{'"a";"minus"[]{'"n"}}} }

interactive nuprl_rem_sym   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";"minus"[]{'"b"}};"rem"[]{'"a";'"b"}} }

interactive nuprl_rem_antisym   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{"minus"[]{'"a"};'"b"};"minus"[]{"rem"[]{'"a";'"b"}}} }

interactive nuprl_remainder_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- ("rem"[]{'"a";'"n"} in "nat"[]{}) }

interactive nuprl_comb_for_remainder_wf   :
   sequent { <H> >- ("lambda"[]{"a"."lambda"[]{"n"."lambda"[]{"z"."rem"[]{'"a";'"n"}}}} in "fun"[]{"nat"[]{};"a"."fun"[]{"nat_plus"[]{};"n"."fun"[]{"squash"[]{"true"[]{}};""."nat"[]{}}}}) }

interactive nuprl_rem_bounds_z   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "lt"[]{"absval"[]{"rem"[]{'"a";'"b"}};"absval"[]{'"b"}} }

interactive nuprl_rem_sym_1   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"minus"[]{"rem"[]{'"a";'"n"}};"rem"[]{"minus"[]{'"a"};'"n"}} }

interactive nuprl_rem_sym_1a   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"minus"[]{"rem"[]{"minus"[]{'"a"};'"n"}}} }

interactive nuprl_rem_sym_2   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"rem"[]{'"a";"minus"[]{'"n"}}} }

interactive nuprl_rem_mag_bound   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "lt"[]{"absval"[]{"rem"[]{'"a";'"n"}};"absval"[]{'"n"}} }

interactive nuprl_div_bounds_1   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "le"[]{"number"[0:n]{};"div"[]{'"a";'"n"}} }

interactive nuprl_divide_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- ("div"[]{'"a";'"n"} in "nat"[]{}) }

interactive nuprl_divide_wfa {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- ("div"[]{'"a";'"n"} in "int"[]{}) }

define unfold_div_nrel : "div_nrel"[]{'"a";'"n";'"q"} <-->
      "lelt"[]{"mul"[]{'"n";'"q"};'"a";"mul"[]{'"n";"add"[]{'"q";"number"[1:n]{}}}}


interactive nuprl_div_nrel_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"q" in "nat"[]{} }  -->
   sequent { <H> >- ("div_nrel"[]{'"a";'"n";'"q"} in "univ"[1:l]{}) }

interactive nuprl_div_fun_sat_div_nrel   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "div_nrel"[]{'"a";'"n";"div"[]{'"a";'"n"}} }

interactive nuprl_div_elim   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "exists"[]{"nat"[]{};"q"."and"[]{"div_nrel"[]{'"a";'"n";'"q"};"equal"[]{"int"[]{};"div"[]{'"a";'"n"};'"q"}}} }

interactive nuprl_div_unique  '"n" '"a"  :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"p" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"q" in "nat"[]{} }  -->
   sequent { <H> >- "div_nrel"[]{'"a";'"n";'"p"} }  -->
   sequent { <H> >- "div_nrel"[]{'"a";'"n";'"q"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"p";'"q"} }

interactive nuprl_div_lbound_1   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "nat"[]{} }  -->
   sequent { <H> >- "iff"[]{"le"[]{'"k";"div"[]{'"a";'"n"}};"le"[]{"mul"[]{'"k";'"n"};'"a"}} }

define unfold_rem_nrel : "rem_nrel"[]{'"a";'"n";'"r"} <-->
      "exists"[]{"nat"[]{};"q"."and"[]{"div_nrel"[]{'"a";'"n";'"q"};"equal"[]{"int"[]{};"add"[]{"mul"[]{'"q";'"n"};'"r"};'"a"}}}


interactive nuprl_rem_nrel_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   [wf] sequent { <H> >- '"r" in "nat"[]{} }  -->
   sequent { <H> >- ("rem_nrel"[]{'"a";'"n";'"r"} in "univ"[1:l]{}) }

interactive nuprl_rem_fun_sat_rem_nrel   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "rem_nrel"[]{'"a";'"n";"rem"[]{'"a";'"n"}} }

interactive nuprl_div_base_case   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{'"a";'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"div"[]{'"a";'"n"};"number"[0:n]{}} }

interactive nuprl_div_rec_case   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "ge"[]{'"a";'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"div"[]{'"a";'"n"};"add"[]{"div"[]{"sub"[]{'"a";'"n"};'"n"};"number"[1:n]{}}} }

interactive nuprl_rem_base_case   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "lt"[]{'"a";'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};'"a"} }

interactive nuprl_rem_gen_base_case   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "int_nzero"[]{} }  -->
   sequent { <H> >- "lt"[]{"absval"[]{'"a"};"absval"[]{'"n"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};'"a"} }

interactive nuprl_rem_rec_case   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "ge"[]{'"a";'"n"} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"n"};"rem"[]{"sub"[]{'"a";'"n"};'"n"}} }

interactive nuprl_rem_invariant   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{"add"[]{'"a";"mul"[]{'"b";'"n"}};'"n"};"rem"[]{'"a";'"n"}} }

interactive nuprl_rem_addition   :
   [wf] sequent { <H> >- '"i" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{"add"[]{"rem"[]{'"i";'"n"};"rem"[]{'"j";'"n"}};'"n"};"rem"[]{"add"[]{'"i";'"j"};'"n"}} }

interactive nuprl_rem_rem_to_rem   :
   [wf] sequent { <H> >- '"a" in "nat"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{"rem"[]{'"a";'"n"};'"n"};"rem"[]{'"a";'"n"}} }

interactive nuprl_rem_base_case_z   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "lt"[]{"absval"[]{'"a"};"absval"[]{'"b"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"b"};'"a"} }

interactive nuprl_rem_eq_args   :
   [wf] sequent { <H> >- '"a" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"a"};"number"[0:n]{}} }

interactive nuprl_rem_eq_args_z   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"b" in "int_nzero"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"absval"[]{'"a"};"absval"[]{'"b"}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};"rem"[]{'"a";'"b"};"number"[0:n]{}} }

define unfold_modulus : "modulus"[]{'"a";'"n"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"a"};"rem"[]{'"a";'"n"};"ifthenelse"[]{"beq_int"[]{"rem"[]{"minus"[]{'"a"};'"n"};"number"[0:n]{}};"number"[0:n]{};"sub"[]{'"n";"rem"[]{"minus"[]{'"a"};'"n"}}}}


interactive nuprl_modulus_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- ("modulus"[]{'"a";'"n"} in "nat"[]{}) }

define unfold_div_floor : "div_floor"[]{'"a";'"n"} <-->
      "ifthenelse"[]{"le_bool"[]{"number"[0:n]{};'"a"};"div"[]{'"a";'"n"};"ifthenelse"[]{"beq_int"[]{"rem"[]{"minus"[]{'"a"};'"n"};"number"[0:n]{}};"minus"[]{"div"[]{"minus"[]{'"a"};'"n"}};"add"[]{"minus"[]{"div"[]{"minus"[]{'"a"};'"n"}};"minus"[]{"number"[1:n]{}}}}}


interactive nuprl_div_floor_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- ("div_floor"[]{'"a";'"n"} in "int"[]{}) }

interactive nuprl_mod_bounds   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "and"[]{"le"[]{"number"[0:n]{};"modulus"[]{'"a";'"n"}};"lt"[]{"modulus"[]{'"a";'"n"};'"n"}} }

interactive nuprl_div_floor_mod_sum   :
   [wf] sequent { <H> >- '"a" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"n" in "nat_plus"[]{} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"a";"add"[]{"mul"[]{"div_floor"[]{'"a";'"n"};'"n"};"modulus"[]{'"a";'"n"}}} }

interactive nuprl_int_mag_well_founded   :
   sequent { <H> >- "well_founded"[level:l]{"int"[]{};"x", "y"."lt"[]{"absval"[]{'"x"};"absval"[]{'"y"}}} }

interactive nuprl_int_upper_well_founded   :
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "well_founded"[level:l]{"int_upper"[]{'"n"};"x", "y"."lt"[]{'"x";'"y"}} }

interactive nuprl_int_upper_ind  '"i" "lambda"[]{"x".'"E"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_upper"[]{'"i"} >- "type"{'"E"['"x"] } }  -->
   sequent { <H> >- '"E"['"i"] }  -->
   sequent { <H>; "k": "int_upper"[]{"add"[]{'"i";"number"[1:n]{}}} ; '"E"["sub"[]{'"k";"number"[1:n]{}}]  >- '"E"['"k"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"int_upper"[]{'"i"};"k".'"E"['"k"]}} }

interactive nuprl_int_lower_well_founded   :
   [wf] sequent { <H> >- '"n" in "int"[]{} }  -->
   sequent { <H> >- "well_founded"[level:l]{"int_lower"[]{'"n"};"x", "y"."gt"[]{'"x";'"y"}} }

interactive nuprl_int_lower_ind  '"i" "lambda"[]{"x".'"E"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_lower"[]{'"i"} >- "type"{'"E"['"x"] } }  -->
   sequent { <H> >- '"E"['"i"] }  -->
   sequent { <H>; "k": "int_lower"[]{"sub"[]{'"i";"number"[1:n]{}}} ; '"E"["add"[]{'"k";"number"[1:n]{}}]  >- '"E"['"k"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"int_lower"[]{'"i"};"k".'"E"['"k"]}} }

interactive nuprl_int_seg_well_founded_up   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int_upper"[]{'"i"} }  -->
   sequent { <H> >- "well_founded"[u:l]{"int_seg"[]{'"i";'"j"};"x", "y"."lt"[]{'"x";'"y"}} }

interactive nuprl_int_seg_ind  '"i" '"j" "lambda"[]{"x".'"E"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int_upper"[]{"add"[]{'"i";"number"[1:n]{}}} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{'"i";'"j"} >- "type"{'"E"['"x"] } }  -->
   sequent { <H> >- '"E"['"i"] }  -->
   sequent { <H>; "k": "int_seg"[]{"add"[]{'"i";"number"[1:n]{}};'"j"} ; '"E"["sub"[]{'"k";"number"[1:n]{}}]  >- '"E"['"k"] }  -->
   sequent { <H> >- "guard"[]{"all"[]{"int_seg"[]{'"i";'"j"};"k".'"E"['"k"]}} }

interactive nuprl_int_seg_well_founded_down   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int_upper"[]{'"i"} }  -->
   sequent { <H> >- "well_founded"[u:l]{"int_seg"[]{'"i";'"j"};"x", "y"."gt"[]{'"x";'"y"}} }

interactive nuprl_decidable__ex_int_seg  '"j" '"i" "lambda"[]{"x".'"F"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{'"i";'"j"} >- "type"{'"F"['"x"] } }  -->
   sequent { <H>; "k": "int_seg"[]{'"i";'"j"}  >- "decidable"[]{'"F"['"k"]} }  -->
   sequent { <H> >- "decidable"[]{"exists"[]{"int_seg"[]{'"i";'"j"};"k".'"F"['"k"]}} }

interactive nuprl_decidable__all_int_seg  '"j" '"i" "lambda"[]{"x".'"F"['"x"]}  :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   [wf] sequent { <H>;"x": "int_seg"[]{'"i";'"j"} >- "type"{'"F"['"x"] } }  -->
   sequent { <H>; "k": "int_seg"[]{'"i";'"j"}  >- "decidable"[]{'"F"['"k"]} }  -->
   sequent { <H> >- "decidable"[]{"all"[]{"int_seg"[]{'"i";'"j"};"k".'"F"['"k"]}} }


(**** display forms ****)


dform nuprl_absval_df : except_mode[src] :: "absval"[]{'"i"} =
   `"|" slot{'"i"} `"|"


dform nuprl_pm_equal_df : except_mode[src] :: "pm_equal"[]{'"i";'"j"} =
   `"" slot{'"i"} `" = " plusminus `" " slot{'"j"} `""


dform nuprl_imax_df : except_mode[src] :: "imax"[]{'"a";'"b"} =
   `"imax(" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_imin_df : except_mode[src] :: "imin"[]{'"a";'"b"} =
   `"imin(" slot{'"a"} `";" slot{'"b"} `")"


dform nuprl_ndiff_df : except_mode[src] :: "ndiff"[]{'"a";'"b"} =
   `"" slot{'"a"} `" -- " slot{'"b"} `""


dform nuprl_div_nrel_df : except_mode[src] :: "div_nrel"[]{'"a";'"n";'"q"} =
   `"Div(" slot{'"a"} `";" slot{'"n"} `";" slot{'"q"} `")"


dform nuprl_rem_nrel_df : except_mode[src] :: "rem_nrel"[]{'"a";'"n";'"r"} =
   `"Rem(" slot{'"a"} `";" slot{'"n"} `";" slot{'"r"} `")"


dform nuprl_modulus_df : except_mode[src] :: "modulus"[]{'"a";'"n"} =
   `"" slot{'"a"} `" mod " slot{'"n"} `""


dform nuprl_div_floor_df : except_mode[src] :: "div_floor"[]{'"a";'"n"} =
   `"" slot{'"a"} `" " div `"" downarrow `" " slot{'"n"} `""


