extends Base_theory

open Basic_tactics

(* MetaPRL doesn't allow to declare a variable twice  in one Context
so in rules w-s, ... we skip such things as "x not in H" *)

declare sequent_arg{'T}

declare le[i:l,j:l]  (* i is less or equal to j *)

(*
declare WF (* hypothesises are well-formed *)
declare WF{'H}
*)
declare "type"[i:l]
declare Prop
declare Set
declare of_some_sort{'P}    (* 'P has some sort *)
declare prop_set{'s} (* type 's, is sort Prop or sort Set *)
declare member{'t;'T} (* term 't has a type 'T*)
(*
declare decl{'T}        (* declaration of some variable having type 'T (as assumption) *)
declare "let"{'t;'T}      (* declaration of some variable as definition (let it be 't:'T)*)
*)
declare "fun"{'T;x.'U['x]} (* product ('x:'T)'U, x-variable, T,U-terms *)

declare "fun"{'A;'B}

rewrite unfold_fun :
	('A -> 'B) <--> (x:'A -> 'B)

topval unfold_funC : conv

declare lambda{'T;x.'t['x]}  (* the term ['x:'T]'t is a function which maps
                                   elements of 'T to 't - lambda_abstraction
                                   from lambda-calculus *)
(*
declare let_in{'t;x.'u['x]} (* declaration of the let-in expressions -
                            in term 'u the var 'x is locally bound to term 't *)
*)
declare apply{'t;'u} (* declaration of "term 't applied to term 'u" *)
declare subst{'u;'x;'t} (* declaration of substitution of a term 't to all
                            free occurrences of a variable 'x in a term 'u *)

declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}

val dfun_term : term
val is_dfun_term : term -> bool
val dest_dfun : term -> var * term * term
val mk_dfun_term : var -> term -> term -> term

val fun_term : term
val is_fun_term : term -> bool
val dest_fun : term -> term * term
val mk_fun_term : term -> term -> term

val apply_term : term
val is_apply_term : term -> bool
val dest_apply : term -> term * term
val mk_apply_term : term -> term -> term

(*****************************************************
*   The type of a type is always a constant of the
*   language of CIC called a 'sort'.
*   Set, Prop, Type[i] are sorts.
******************************************************)

rule ax_prop :
   sequent { <H> >- member{Prop;"type"[i:l]}  }

rule ax_set :
   sequent { <H> >- member{Set;"type"[i:l]}  }

rule ax_type :
   sequent { <H> >- member{"type"[i:l];"type"[i':l]}  }

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
   sequent { <H> >- prop_set{Prop} }

rule set_a_prop_set:
   sequent { <H> >- prop_set{Set} }


(************************************************
*      RULES
*************************************************)

rule var 'H :
   sequent { <H>; <J> >- of_some_sort{'T} } -->
   sequent { <H>; x: 'T; <J> >- 'x in 'T }

rule weak 'H :
	sequent { <H>; <J> >- 'A in 'B } -->
	sequent { <H>; <J> >- of_some_sort{'C} } -->
	sequent { <H>; x: 'C; <J> >- 'A in 'B }

rule prod_1 's1:
   sequent { <H> >- prop_set{'s1}  } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H>; x:'T >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ (x:'T -> 'U['x]); 's2  }  }

rule prod_2 's1:
   sequent { <H>; x:'T >- prop_set{'s2}  } -->
   sequent { <H>; x:'T >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H> >- member{ (x:'T -> 'U['x]); 's2  }  }

rule prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- member{'T;"type"[i:l]}  } -->
   sequent { <H>; x:'T >- member{ 'U['x]; "type"[j:l] }  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- member{ (x:'T -> 'U['x]); "type"[k:l] } }


(************************************************
 *                                              *
 ************************************************)

rule lam 's:
   sequent { <H> >- member{ (x:'T -> 'U['x]); 's }  } -->
   sequent { <H> >- of_some_sort{'s }  } -->
   sequent { <H>; x:'T >- member{ 't['x]; 'U['x] }  } -->
   sequent { <H> >- member{ lambda{'T;x.'t['x]}; (x:'T -> 'U['x]) } }


(************************************************
 *                                              *
 ************************************************)

rule app (x:'T -> 'U['x]) :
   sequent { <H> >- member{ 'u; (x:'T -> 'U['x]) }  } -->
   sequent { <H> >- member{ 't;'T }  } -->
   sequent { <H> >- member{ apply{'u;'t}; 'U['t]  } }


(************************************************
 *                                              *
 ************************************************)

(*
rule let_in 'T bind{x.'U['x]}:
   sequent { <H> >- member{'t;'T}  } -->
   sequent { <H>; x:"let"{'t;'T} >- member{'u['x];'U['x]} } -->
   sequent { <H> >- member{ let_in{'t;x.'u['x]}; 'U['t] }  }
*)

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

rule delta_let_concl 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] }

rule delta_let_hyp 'H 'J bind{x.'C['x]} bind{x.'D['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['t]; <K['x]> >- 'C['x] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['x]; <K['x]> >- 'C['x] }

rule delta_let_all 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['t]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] }

rule zeta :
   sequent { <H> >- red{ let_in{ 'u; x.'t['x] }; 't['u] } }

rewrite zeta :
   let_in{ 'u; x.'t['x] } <--> 't['u]
*)

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
   sequent { <H>; x:'T >- conv_le{ 'T1['x]; 'U1['x] } } -->
   sequent { <H> >- conv_le{ (x:'T -> 'T1['x]); (x:'T -> 'U1['x]) }}

rule conv_rule 's 'T:
   sequent { <H> >- member{ 'U; 's } } -->
   sequent { <H> >- member{ 't; 'T } } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- member{ 't; 'U } }
