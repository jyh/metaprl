extends Base_theory

(* MetaPRL doesn't allow to declare a variable twice  in one Context
so in rules w-s, ... we skip such things as "x not in H" *)

declare sequent_arg{'T}

declare le[i:l,j:l]  (* i is less or equal to j *)

declare WF (* hypothesises are well-formed *)
declare WF{'H}
declare Prop
declare Set
declare "type"[i:l]
declare of_some_sort{'P}    (* 'P has some sort *)
declare prop_set{'s} (* type 's, is sort Prop or sort Set *)
declare member{'t;'T} (* term 't has a type 'T*)
declare decl{'T}        (* declaration of some variable having type 'T (as assumption) *)
declare "let"{'t;'T}      (* declaration of some variable as definition (let it be 't:'T)*)
declare dfun{'T;x.'U['x]} (* product ('x:'T)'U, x-variable, T,U-terms *)

declare "fun"{'A;'B}

prim_rw unfold_fun :
	('A -> 'B) <--> (dfun{'A; x.'B})

declare lambda{'T;x.'t['x]}  (* the term ['x:'T]'t is a function which maps
                                   elements of 'T to 't - lambda_abstraction
                                   from lambda-calculus *)
declare let_in{'t;x.'u['x]} (* declaration of the let-in expressions -
                            in term 'u the var 'x is locally bound to term 't *)
declare apply{'t;'u} (* declaration of "term 't applied to term 'u" *)
declare subst{'u;'x;'t} (* declaration of substitution of a term 't to all
                            free occurrences of a variable 'x in a term 'u *)
declare bind{x.'T['x]}
declare bind{x,y.'T['x;'y]}

(*****************************************************
 * DISPLAY FORMS                                     *
 *****************************************************)

(*extends Nuprl_font*)

prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda
prec prec_equal
prec prec_equal < prec_apply

declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}

dform math_dfun_df1 : mode[tex] :: math_fun{'x; 'A; 'B} =
   'x
   izone `"\\colon " ezone
   'A
   izone `"\\rightarrow " ezone
   'B

dform math_fun_df1 : mode[tex] :: math_fun{'A; 'B} =
   'A
   izone `"\\rightarrow " ezone
   'B


dform it_df1 : except_mode[src] :: it = cdot
dform it_df2 : mode[src] :: it = `"it"

declare declaration{'decl;'term} (* Used only for display forms, such as let *)

dform declaration_df : declaration{'decl;'a}
   = 'decl `" := " slot{'a}

dform wf_df : except_mode[src] :: WF = `"WF"

dform wfh_df : except_mode[src] :: WF{'H} = `"WF{" slot{'H} `"}"

dform prop_df : except_mode[src] :: Prop = `"Prop"

dform set_df : except_mode[src] :: Set = `"Set"

dform type_df : except_mode[src] :: "type"[i:l] = `"Type(" slot[i:l] `")"

dform of_some_sort_df : except_mode[src] :: of_some_sort{'P} =
   slot{'P} space `"is of some sort"

dform prop_set_df : except_mode[src] :: prop_set{'s} =
   slot{'s} space `"is" space slot{Set} space `"or" space slot{Prop}

(* HACK! - this should be replaced with a proper I/O abstraction *)
dform member_df : except_mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space Nuprl_font!member hspace slot["le"]{'T} popm ezone

dform member_df2 : mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space `"in" hspace slot["le"]{'T} popm ezone

dform let_df : except_mode[src] :: "let"{'t;'T} = `"=" slot{'t} `":" slot{'T}

dform let_in_df : let_in{'t;x.'u} =
     szone pushm[3]  `"let " szone{declaration{'x;'t}} `" in" hspace
     szone{'u} popm ezone

dform fun_df1 : "fun"{'A; 'B} = math_fun{'A; 'B}
dform fun_df2 : "dfun"{'A; x. 'B} = math_fun{'x; 'A; 'B}

dform lambda_df : parens :: except_mode [src] :: "prec"[prec_lambda] :: lambda{'T;x. 'b} =
   Nuprl_font!lambda slot{'x} `":" slot{'T} `"." slot{'b}

dform apply_df : parens :: "prec"[prec_apply] :: apply{'t; 'u} =
   slot["lt"]{'t} " " slot["le"]{'u}

(*
dform subst_df : subst{'u;'x;'t} = slot{'u} `"{" slot{'x} `"}"
*)

dform bind1_df : except_mode[src] :: bind{x.'T} = `"bind{" slot{'x} `"." slot{'T} `"}"

dform bind2_df : except_mode[src] :: bind{x,y.'T} = `"bind{" slot{'x} `"," slot{'y} `"." slot{'T} `"}"



(*****************************************************
*   The type of a type is always a constant of the
*   language of CIC called a 'sort'.
*   Set, Prop, Type[i] are sorts.
******************************************************)

(* Prop is a sort *)
prim prop_a_sort:
   sequent { <H> >- member{'P;Prop} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* Set is a sort *)
prim set_a_sort:
   sequent { <H> >- member{'P;Set} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* Type[i] is a sort *)
prim type_a_sort "type"[i:l]:
   sequent { <H> >- member{'P;"type"[i:l]} } -->
   sequent { <H> >- of_some_sort{'P} } = it


(****************************************************
* Tentative axioms stating that type Prop (Set)
* is sort Prop or sort Set
*****************************************************)

prim prop_a_prop_set:
   sequent { <H> >- member{'P;Prop} } -->
   sequent { <H> >- prop_set{'P} } = it

prim set_a_prop_set:
   sequent { <H> >- member{'P;Set} } -->
   sequent { <H> >- prop_set{'P} } = it


(************************************************
*      RULES
*************************************************)

prim w_e :
   sequent { >- WF{it} } = it

(************************************************
*
*************************************************)

prim w_s_decl :
   sequent { <H> >- of_some_sort{'T} } -->
   sequent { <H>; x: decl{'T} >- WF } = it


(************************************************
*
*************************************************)

prim w_s_let :
   sequent { <H> >-  member{'t;'T} } -->
   sequent { <H>; x: "let"{'t;'T} >- WF } = it


(************************************************
 *                                              *
 ************************************************)


(************************************************
 *                                              *
 ************************************************)

prim ax_prop :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{Prop;"type"[i:l]}  } = it



prim ax_set :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{Set;"type"[i:l]}  } = it



prim ax_type :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{"type"[i:l];"type"[i':l]}  } = it


(************************************************
 *                                              *
 ************************************************)

prim var_decl 'H:
   sequent { <H>; x: decl{'T}; <J['x]> >- WF } -->
   sequent { <H>; x: decl{'T}; <J['x]> >- member{'x;'T}  } = it



prim var_let 'H:
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- WF } -->
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- member{'x;'T}  } = it


(************************************************
 *                                              *
 ************************************************)

prim prod_1 's1:
   sequent { <H> >- prop_set{'s1}  } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's2  }  } = it

prim prod_2 's1:
   sequent { <H>; x:decl{'T} >- prop_set{'s2}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's2  }  } = it

prim prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- member{'T;"type"[i:l]}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; "type"[j:l] }  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; "type"[k:l] } } = it


(************************************************
 *                                              *
 ************************************************)

prim lam 's:
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's }  } -->
   sequent { <H> >- of_some_sort{'s }  } -->
   sequent { <H>; x:decl{'T} >- member{ 't['x]; 'U['x] }  } -->
   sequent { <H> >- member{ lambda{'T;x.'t['x]}; dfun{'T;x.'U['x]} } } = it


(************************************************
 *                                              *
 ************************************************)

prim app dfun{'U; x.'T['x]} :
   sequent { <H> >- member{ 't; dfun{'U; x.'T['x]} }  } -->
   sequent { <H> >- member{ 'u;'U }  } -->
   sequent { <H> >- member{ apply{'t;'u}; 'T['u]  } } = it


(************************************************
 *                                              *
 ************************************************)

prim let_in 'T bind{x.'U['x]}:
   sequent { <H> >- member{'t;'T}  } -->
   sequent { <H>; x:"let"{'t;'T} >- member{'u['x];'U['x]} } -->
   sequent { <H> >- member{ let_in{'t;x.'u['x]}; 'U['t] }  } = it


(************************************************
*                CONVERSION RULES               *
*************************************************)

declare red {'x;'t} (* term 'x reduces to term 't in the context H *)


(*
prim beta :
   sequent { <H> >- red{ apply{ lambda{'T; x.'t['x]}; 'u }; 't['u] } } = it
*)

prim_rw beta :
   ( apply{ lambda{'T; x.'t['x]}; 'u } ) <--> ( 't['u] )

(*
prim delta_let 'H:
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- red{ 'x ; 't } } = it
*)

prim delta_let_concl 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] } = it

prim delta_let_hyp 'H 'J bind{x.'C['x]} bind{x.'D['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['t]; <K['x]> >- 'C['x] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['x]; <K['x]> >- 'C['x] } = it

prim delta_let_all 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['t]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] } = it

(*
prim zeta :
   sequent { <H> >- red{ let_in{ 'u; x.'t['x] }; 't['u] } } = it
*)

prim_rw zeta :
   let_in{ 'u; x.'t['x] } <--> 't['u]

(***************************************************
*                 CONVERTIBILITY                   *
****************************************************)

declare conv_le{ 't; 'u } (* extending equivalence relation into an order
                             which will be inductively defined *)

(* inductive defenition of conv_le *)

prim conv_le_1 :
   sequent { <H> >- conv_le{ 't; 't } } = it

prim conv_le_2 :
   sequent { >- le[i:l,j:l] } -->
   sequent { <H> >- conv_le{ "type"[i:l]; "type"[j:l] } } = it

prim conv_le_3 :
   sequent { <H> >- conv_le{ Prop; "type"[i:l] } } = it

prim conv_le_4 :
   sequent { <H> >- conv_le{ Set; "type"[i:l] } } = it

prim conv_le_5 :
   sequent { <H>; x:decl{'T} >- conv_le{ 'T1['x]; 'U1['x] } } -->
   sequent { <H> >- conv_le{ dfun{ 'T; x.'T1['x]}; dfun{ 'T; x.'U1['x] }}} = it

prim conv_rule 's 'T:
   sequent { <H> >- member{ 'U; 's } } -->
   sequent { <H> >- member{ 't; 'T } } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- member{ 't; 'U } } = it
