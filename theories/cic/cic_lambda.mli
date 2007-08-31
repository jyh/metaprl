extends Base_theory

open Basic_tactics

(* MetaPRL doesn't allow to declare a variable twice  in one Context
so in rules w-s, ... we skip such things as "x not in H" *)

(*
declare WF (* hypothesises are well-formed *)
declare WF{'H}
*)
declare "type"[i:l]
declare Prop
declare Set
declare of_some_sort{'P}    (* 'P has some sort *)
declare is_sort{'s}
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
topval fold_funC : conv

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

declare "true"
declare "false"

define unfold_level_le :
	level_le[i:l, j:l] <--> meta_lt[j:l, i:l]{"false"; "true"}

prec prec_fun
prec prec_apply
prec prec_lambda

declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}

val member_term : term
val is_member_term : term -> bool
val dest_member : term -> term * term
val mk_member_term : term -> term -> term

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
   sequent { <H> >- Prop in "type"[i:l] }

rule ax_set :
   sequent { <H> >- Set in"type"[i:l] }

rule ax_type :
   sequent { <H> >- "type"[i:l] in "type"[i':l] }

(* if P:Prop then P is of some sort *)
rule prop_a_sort:
   sequent { <H> >- 'P in Prop } -->
   sequent { <H> >- of_some_sort{'P} }

(* if P:Set then P is of some sort *)
rule set_a_sort:
   sequent { <H> >- 'P in Set } -->
   sequent { <H> >- of_some_sort{'P} }

(* if P:Type(i) then P is of some sort *)
rule type_a_sort "type"[i:l]:
   sequent { <H> >- 'P in "type"[i:l] } -->
   sequent { <H> >- of_some_sort{'P} }

(* Set is a sort *)
rule set_is_sort :
	sequent { <H> >- is_sort{Set} }

(* Prop is a sort *)
rule prop_is_sort :
	sequent { <H> >- is_sort{Prop} }

(* Type[i] is a sort *)
rule type_is_sort :
	sequent { <H> >- is_sort{"type"[i:l]} }


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

rule introduction 't :
   sequent { <H> >- 't in 'T } -->
   sequent { <H> >- 'T }

rule var 'H :
   (*sequent { <H>; <J> >- of_some_sort{'T} } -->*)
   sequent { <H> >- of_some_sort{'T} } -->
   sequent { <H>; x: 'T; <J['x]> >- 'x in 'T }

rule hypothesis 'H :
   sequent { <H> >- of_some_sort{'T} } -->
   sequent { <H>; x: 'T; <J['x]> >- 'T }

rule thin_many 'H 'J :
   sequent { <H>; <K> >- 'C } -->
   sequent { <H>; <J>; < K<|H|> > >- 'C<|H;K|> }

rule thin 'H :
	sequent { <H>; <J> >- 'B } -->
	sequent { <H>; <J> >- of_some_sort{'C} } -->
	sequent { <H>; x: 'C; <J> >- 'B }

(*
rule weak 'H :
	sequent { <H>; <J> >- 'A in 'B } -->
	sequent { <H>; <J> >- of_some_sort{'C} } -->
	sequent { <H>; x: 'C; <J> >- 'A in 'B }
*)

rule cut 'H 'S :
   sequent { <H>; <J> >- 'S } -->
   sequent { <H>; x: 'S; <J> >- 'T } -->
   sequent { <H>; <J> >- 'T }

rule prod_1 's1:
   sequent { <H> >- prop_set{'s1} } -->
   sequent { <H> >- 'T in 's1 } -->
   sequent { <H>; x:'T >- 'U['x] in 's2 } -->
   sequent { <H> >- (x:'T -> 'U['x]) in 's2 }

rule prod_2 's1:
   sequent { <H>; x:'T >- prop_set{'s2} } -->
   sequent { <H>; x:'T >- 'U['x] in 's2 } -->
   sequent { <H> >- 'T in 's1 } -->
   sequent { <H> >- (x:'T -> 'U['x]) in 's2 }

rule prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- 'T in "type"[i:l] } -->
   sequent { <H>; x:'T >- 'U['x] in "type"[j:l] } -->
   sequent { >- level_le[i:l,k:l] } -->
   sequent { >- level_le[j:l,k:l] } -->
   sequent { <H> >- (x:'T -> 'U['x]) in "type"[k:l] }


(************************************************
 *                                              *
 ************************************************)

rule lam 's:
   sequent { <H> >- (x:'T -> 'U['x]) in 's } -->
   sequent { <H> >- is_sort{'s } } -->
   sequent { <H>; x:'T >- 't['x] in 'U['x] } -->
   sequent { <H> >- lambda{'T;x.'t['x]} in (x:'T -> 'U['x]) }

rule lambdaFormation 's :
   sequent { <H> >- (x:'T -> 'U['x]) in 's } -->
   sequent { <H> >- is_sort{'s } } -->
   sequent { <H>; x:'T >- 'U['x] } -->
   sequent { <H> >- (x:'T -> 'U['x]) }

(************************************************
 *                                              *
 ************************************************)

rule app (x:'T -> 'U['x]) :
   sequent { <H> >- 'u in (x:'T -> 'U['x]) } -->
   sequent { <H> >- 't in 'T } -->
   sequent { <H> >- apply{'u;'t} in 'U['t] }

rule appFormation (x:'T -> 'U['x]) :
   sequent { <H> >- x:'T -> 'U['x] } -->
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'U['t] }

(************************************************
 *                                              *
 ************************************************)

(*
rule let_in 'T bind{x.'U['x]}:
   sequent { <H> >- 't in 'T } -->
   sequent { <H>; x:"let"{'t;'T} >- 'u['x] in 'U['x] } -->
   sequent { <H> >- let_in{'t;x.'u['x]} in 'U['t] }
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
   sequent { >- level_le[i:l,j:l] } -->
   sequent { <H> >- conv_le{ "type"[i:l]; "type"[j:l] } }

rule conv_le_3 :
   sequent { <H> >- conv_le{ Prop; "type"[i:l] } }

rule conv_le_4 :
   sequent { <H> >- conv_le{ Set; "type"[i:l] } }

rule conv_le_5 :
   sequent { <H>; x:'T >- conv_le{ 'T1['x]; 'U1['x] } } -->
   sequent { <H> >- conv_le{ (x:'T -> 'T1['x]); (x:'T -> 'U1['x]) }}

rule conv_rule 's 'T:
   sequent { <H> >- 'U in 's } -->
   sequent { <H> >- 't in 'T } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- 't in 'U }
