extends Ma_union

open Dtactic


define unfold_sq_type : "sq_type"[]{'"T"} <-->
      "all"[]{'"T";"x"."all"[]{'"T";"y"."implies"[]{"equal"[]{'"T";'"x";'"y"};"guard"[]{"rewrite"[]{'"x";'"y"}}}}}


interactive nuprl_int_sq   :
   sequent { <H> >- "sq_type"[]{"int"[]{}} }

interactive nuprl_nat_sq   :
   sequent { <H> >- "sq_type"[]{"nat"[]{}} }

interactive nuprl_bool_sq   :
   sequent { <H> >- "sq_type"[]{"bool"[]{}} }

interactive nuprl_atom_sq   :
   sequent { <H> >- "sq_type"[]{"atom"[]{}} }

interactive_rw nuprl_bool_sim_true   :
   ('"b" in "bool"[]{}) -->
   "equal"[]{"bool"[]{};'"b";"btrue"[]{}} -->
   '"b" <--> "btrue"[]{}

interactive_rw nuprl_bool_sim_false   :
   ('"b" in "bool"[]{}) -->
   "equal"[]{"bool"[]{};'"b";"bfalse"[]{}} -->
   '"b" <--> "bfalse"[]{}

interactive_rw nuprl_eq_int_eq_true_intro   :
   ('"i" in "int"[]{}) -->
   ('"j" in "int"[]{}) -->
   "equal"[]{"int"[]{};'"i";'"j"} -->
   "beq_int"[]{'"i";'"j"} <--> "btrue"[]{}

interactive_rw nuprl_eq_int_eq_false_intro   :
   ('"i" in "int"[]{}) -->
   ('"j" in "int"[]{}) -->
   "not"[]{"equal"[]{"int"[]{};'"i";'"j"}} -->
   "beq_int"[]{'"i";'"j"} <--> "bfalse"[]{}

interactive nuprl_lt_int_eq_true_elim   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"lt_bool"[]{'"i";'"j"};"btrue"[]{}} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }

interactive nuprl_lt_int_eq_false_elim   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"lt_bool"[]{'"i";'"j"};"bfalse"[]{}} }  -->
   sequent { <H> >- "not"[]{"lt"[]{'"i";'"j"}} }

interactive nuprl_eq_atom_eq_true_elim   :
   [wf] sequent { <H> >- '"x" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "atom"[]{} }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"eq_atom"[]{'"x";'"y"};"btrue"[]{}} }  -->
   sequent { <H> >- "equal"[]{"atom"[]{};'"x";'"y"} }

interactive nuprl_eq_atom_eq_false_elim   :
   [wf] sequent { <H> >- '"x" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "atom"[]{} }  -->
   sequent { <H> >- "equal"[]{"bool"[]{};"eq_atom"[]{'"x";'"y"};"bfalse"[]{}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"atom"[]{};'"x";'"y"}} }

interactive nuprl_eq_int_eq_true_elim_sqequal   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"beq_int"[]{'"i";'"j"};"btrue"[]{}} }  -->
   sequent { <H> >- "equal"[]{"int"[]{};'"i";'"j"} }

interactive nuprl_eq_int_eq_false_elim_sqequal   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"beq_int"[]{'"i";'"j"};"bfalse"[]{}} }  -->
   sequent { <H> >- "nequal"[]{"int"[]{};'"i";'"j"} }

interactive nuprl_lt_int_eq_true_elim_sqequal   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"lt_bool"[]{'"i";'"j"};"btrue"[]{}} }  -->
   sequent { <H> >- "lt"[]{'"i";'"j"} }

interactive nuprl_lt_int_eq_false_elim_sqequal   :
   [wf] sequent { <H> >- '"i" in "int"[]{} }  -->
   [wf] sequent { <H> >- '"j" in "int"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"lt_bool"[]{'"i";'"j"};"bfalse"[]{}} }  -->
   sequent { <H> >- "not"[]{"lt"[]{'"i";'"j"}} }

interactive nuprl_eq_atom_eq_true_elim_sqequal   :
   [wf] sequent { <H> >- '"x" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "atom"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"eq_atom"[]{'"x";'"y"};"btrue"[]{}} }  -->
   sequent { <H> >- "equal"[]{"atom"[]{};'"x";'"y"} }

interactive nuprl_eq_atom_eq_false_elim_sqequal   :
   [wf] sequent { <H> >- '"x" in "atom"[]{} }  -->
   [wf] sequent { <H> >- '"y" in "atom"[]{} }  -->
   sequent { <H> >- "rewrite"[]{"eq_atom"[]{'"x";'"y"};"bfalse"[]{}} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"atom"[]{};'"x";'"y"}} }

interactive nuprl_bool_cases_sqequal   :
   [wf] sequent { <H> >- '"b" in "bool"[]{} }  -->
   sequent { <H> >- "or"[]{"rewrite"[]{'"b";"btrue"[]{}};"rewrite"[]{'"b";"bfalse"[]{}}} }


(**** display forms ****)


dform nuprl_term_sq : except_mode[src] :: "term_sq"[]{} =
   `"term~"


dform nuprl_sqequal : except_mode[src] :: "rewrite"[]{'"a";'"b"} =
   `"" slot{'"a"} `" ~ " slot{'"b"} `""


dform nuprl_sq_type_df : except_mode[src] :: "sq_type"[]{'"T"} =
   `"SQType(" slot{'"T"} `")"


