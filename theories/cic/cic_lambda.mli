extends Base_theory

open Tactic_type.Conversionals

(* MetaPRL doesn't allow to declare a variable twice  in one Context
so in rules w-s, ... we skip such things as "x not in H" *)

declare sequent_arg{'T}

declare le[i:l,j:l]  (* i is less or equal to j *)

declare WF (* hypothesises are well-formed *)
declare WF{'H}
declare "type"[i:l]
declare Prop
declare Set
declare of_some_sort{'P}    (* 'P has some sort *)
declare prop_set{'s} (* type 's, is sort Prop or sort Set *)
declare member{'t;'T} (* term 't has a type 'T*)
declare decl{'T}        (* declaration of some variable having type 'T (as assumption) *)
declare "let"{'t;'T}      (* declaration of some variable as definition (let it be 't:'T)*)
declare dfun{'T;x.'U['x]} (* product ('x:'T)'U, x-variable, T,U-terms *)

declare "fun"{'A;'B}

rewrite unfold_fun :
	('A -> 'B) <--> (dfun{'A; x.'B})

topval unfold_funC : conv

declare lambda{'T;x.'t['x]}  (* the term ['x:'T]'t is a function which maps
                                   elements of 'T to 't - lambda_abstraction
                                   from lambda-calculus *)
declare let_in{'t;x.'u['x]} (* declaration of the let-in expressions -
                            in term 'u the var 'x is locally bound to term 't *)
declare apply{'t;'u} (* declaration of "term 't applied to term 'u" *)
declare subst{'u;'x;'t} (* declaration of substitution of a term 't to all
                            free occurrences of a variable 'x in a term 'u *)

declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}


(*****************************************************
*   The type of a type is always a constant of the
*   language of CIC called a 'sort'.
*   Set, Prop, Type[i] are sorts.
******************************************************)

(* Prop is a sort *)
rule prop_a_sort:
   sequent { <H> >- member{'P;Prop} } -->
   sequent { <H> >- of_some_sort{'P} }

(* Set is a sort *)
rule set_a_sort:
   sequent { <H> >- member{'P;Set} } -->
   sequent { <H> >- of_some_sort{'P} }

(* Type[i] is a sort *)
rule type_a_sort "type"[i:l]:
   sequent { <H> >- member{'P;"type"[i:l]} } -->
   sequent { <H> >- of_some_sort{'P} }


(****************************************************
* Tentative axioms stating that type Prop (Set)
* is sort Prop or sort Set
*****************************************************)

rule prop_a_prop_set:
   sequent { <H> >- member{'P;Prop} } -->
   sequent { <H> >- prop_set{'P} }

rule set_a_prop_set:
   sequent { <H> >- member{'P;Set} } -->
   sequent { <H> >- prop_set{'P} }


(************************************************
*      RULES
*************************************************)

rule w_e :
   sequent { >- WF{it} }

(************************************************
*
*************************************************)

rule w_s_decl :
   sequent { <H> >- of_some_sort{'T} } -->
   sequent { <H>; x: decl{'T} >- WF }


(************************************************
*
*************************************************)

rule w_s_let :
   sequent { <H> >-  member{'t;'T} } -->
   sequent { <H>; x: "let"{'t;'T} >- WF }


(************************************************
 *                                              *
 ************************************************)


(************************************************
 *                                              *
 ************************************************)

rule ax_prop :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{Prop;"type"[i:l]}  }



rule ax_set :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{Set;"type"[i:l]}  }



rule ax_type :
   sequent { <H> >- WF } -->
   sequent { <H> >- member{"type"[i:l];"type"[i':l]}  }


(************************************************
 *                                              *
 ************************************************)

rule var_decl 'H:
   sequent { <H>; x: decl{'T}; <J['x]> >- WF } -->
   sequent { <H>; x: decl{'T}; <J['x]> >- member{'x;'T}  }



rule var_let 'H:
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- WF } -->
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- member{'x;'T}  }


(************************************************
 *                                              *
 ************************************************)

rule prod_1 's1:
   sequent { <H> >- prop_set{'s1}  } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's2  }  }

rule prod_2 's1:
   sequent { <H>; x:decl{'T} >- prop_set{'s2}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's2  }  }

rule prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- member{'T;"type"[i:l]}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; "type"[j:l] }  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; "type"[k:l] } }


(************************************************
 *                                              *
 ************************************************)

rule lam 's:
   sequent { <H> >- member{ dfun{'T;x.'U['x]}; 's }  } -->
   sequent { <H> >- of_some_sort{'s }  } -->
   sequent { <H>; x:decl{'T} >- member{ 't['x]; 'U['x] }  } -->
   sequent { <H> >- member{ lambda{'T;x.'t['x]}; dfun{'T;x.'U['x]} } }


(************************************************
 *                                              *
 ************************************************)

rule app dfun{'U; x.'T['x]} :
   sequent { <H> >- member{ 't; dfun{'U; x.'T['x]} }  } -->
   sequent { <H> >- member{ 'u;'U }  } -->
   sequent { <H> >- member{ apply{'t;'u}; 'T['u]  } }


(************************************************
 *                                              *
 ************************************************)

rule let_in 'T bind{x.'U['x]}:
   sequent { <H> >- member{'t;'T}  } -->
   sequent { <H>; x:"let"{'t;'T} >- member{'u['x];'U['x]} } -->
   sequent { <H> >- member{ let_in{'t;x.'u['x]}; 'U['t] }  }


(************************************************
*                CONVERSION RULES               *
*************************************************)

declare red {'x;'t} (* term 'x reduces to term 't in the context H *)


(*
rule beta :
   sequent { <H> >- red{ apply{ lambda{'T; x.'t['x]}; 'u }; 't['u] } }
*)

rewrite beta :
   ( apply{ lambda{'T; x.'t['x]}; 'u } ) <--> ( 't['u] )

(*
rule delta_let 'H:
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- red{ 'x ; 't } }
*)

rule delta_let_concl 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] }

rule delta_let_hyp 'H 'J bind{x.'C['x]} bind{x.'D['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['t]; <K['x]> >- 'C['x] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['x]; <K['x]> >- 'C['x] }

rule delta_let_all 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['t]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] }

(*
rule zeta :
   sequent { <H> >- red{ let_in{ 'u; x.'t['x] }; 't['u] } }
*)

rewrite zeta :
   let_in{ 'u; x.'t['x] } <--> 't['u]

(***************************************************
*                 CONVERTIBILITY                   *
****************************************************)

declare conv_le{ 't; 'u } (* extending equivalence relation into an order
                             which will be inductively defined *)

(* inductive defenition of conv_le *)

rule conv_le_1 :
   sequent { <H> >- conv_le{ 't; 't } }

rule conv_le_2 :
   sequent { >- le[i:l,j:l] } -->
   sequent { <H> >- conv_le{ "type"[i:l]; "type"[j:l] } }

rule conv_le_3 :
   sequent { <H> >- conv_le{ Prop; "type"[i:l] } }

rule conv_le_4 :
   sequent { <H> >- conv_le{ Set; "type"[i:l] } }

rule conv_le_5 :
   sequent { <H>; x:decl{'T} >- conv_le{ 'T1['x]; 'U1['x] } } -->
   sequent { <H> >- conv_le{ dfun{ 'T; x.'T1['x]}; dfun{ 'T; x.'U1['x] }}}

rule conv_rule 's 'T:
   sequent { <H> >- member{ 'U; 's } } -->
   sequent { <H> >- member{ 't; 'T } } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- member{ 't; 'U } }
