extends Base_theory

open Basic_tactics

(* MetaPRL doesn't allow to declare a variable twice  in one Context
so in rules w-s, ... we skip such things as "x not in H"
!!!!!!!! no, it's not enforced by MetaPRL :( !!!!!!!!!!!!!!!
*)

declare le[i:l,j:l]  (* i is less or equal to j *)

(*
declare WF (* hypothesises are well-formed *)
declare WF{'H}
*)
declare Prop
declare Set
declare "type"[i:l]
declare of_some_sort{'P}    (* 'P has some sort *)
declare is_sort{'s}  (* 's is some sort*)
declare prop_set{'s} (* type 's, is sort Prop or sort Set *)
declare member{'t;'T} (* term 't has a type 'T*)
(*
declare decl{'T}        (* declaration of some variable having type 'T (as assumption) *)
declare "let"{'t;'T}      (* declaration of some variable as definition (let it be 't:'T)*)
*)
declare "fun"{'T;x.'U['x]} (* product ('x:'T)'U, x-variable, T,U-terms *)

declare "fun"{'A;'B}

prim_rw unfold_fun :
	('A -> 'B) <--> (x:'A -> 'B)

let unfold_funC = unfold_fun

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

let member_term = << 'a in 'c >>
let member_opname = opname_of_term member_term
let is_member_term = is_dep0_dep0_term member_opname
let dest_member = dest_dep0_dep0_term member_opname
let mk_member_term = mk_dep0_dep0_term member_opname

let apply_term = << apply{'f; 'a} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

let dfun_term = << x:'T -> 'U['x] >>
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

let fun_term = << 'A -> 'B >>
let fun_opname = opname_of_term fun_term
let is_fun_term = is_dep0_dep0_term fun_opname
let dest_fun = dest_dep0_dep0_term fun_opname
let mk_fun_term = mk_dep0_dep0_term fun_opname

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

dform fun_df1 : parens :: "prec"[prec_fun] :: except_mode[tex] :: math_fun{'A; 'B} =
   slot["le"]{'A} " " rightarrow " " slot["lt"]{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: except_mode[tex] :: math_fun{'x; 'A; 'B} =
   slot{bvar{'x}} `":" slot{'A} " " rightarrow " " slot{'B}

dform it_df1 : except_mode[src] :: it = cdot
dform it_df2 : mode[src] :: it = `"it"

declare declaration{'decl : Dform; 'term : Dform} : Dform

dform declaration_df : declaration{'decl;'a}
   = 'decl `" := " slot{'a}

dform prop_df : except_mode[src] :: Prop = `"Prop"

dform set_df : except_mode[src] :: Set = `"Set"

dform type_df : except_mode[src] :: "type"[i:l] = `"Type(" slot[i:l] `")"

dform of_some_sort_df : except_mode[src] :: of_some_sort{'P} =
   slot{'P} space `"is of some sort"

dform is_sort_df : except_mode[src] :: is_sort{'P} =
   `"is_sort{" slot{'P} `"}"

dform prop_set_df : except_mode[src] :: prop_set{'s} =
   slot{'s} space `"is" space slot{Set} space `"or" space slot{Prop}

(* HACK! - this should be replaced with a proper I/O abstraction *)
dform member_df : except_mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space Nuprl_font!member hspace slot["le"]{'T} popm ezone

dform member_df2 : mode[src] :: parens :: "prec"[prec_equal] :: ('x in 'T) =
   szone pushm slot["le"]{'x} space `"in" hspace slot["le"]{'T} popm ezone

(*
dform let_df : except_mode[src] :: "let"{'t;'T} = `"=" slot{'t} `":" slot{'T}

dform let_in_df : let_in{'t;x.'u} =
     szone pushm[3]  `"let " szone{declaration{'x;'t}} `" in" hspace
     szone{'u} popm ezone
*)

dform fun_df1 : "fun"{'A; 'B} = math_fun{'A; 'B}
dform fun_df2 : "fun"{'A; x. 'B} = math_fun{'x; 'A; 'B}

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

prim ax_prop {| intro [] |} :
   sequent { <H> >- member{Prop;"type"[i:l]}  } = it

prim ax_set {| intro [] |} :
   sequent { <H> >- member{Set;"type"[i:l]}  } = it

prim ax_type {| intro [] |} :
   sequent { <H> >- member{"type"[i:l];"type"[i':l]}  } = it

(* if P:Prop then P is of some sort *)
prim prop_a_sort {| intro [] |} :
   sequent { <H> >- member{'P;Prop} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* if P:Set then P is of some sort *)
prim set_a_sort {| intro [] |} :
   sequent { <H> >- member{'P;Set} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* if P:Type(i) then P is of some sort *)
prim type_a_sort {| intro [] |} "type"[i:l] :
   sequent { <H> >- member{'P;"type"[i:l]} } -->
   sequent { <H> >- of_some_sort{'P} } = it

interactive propHasSort {| intro [] |} :
   sequent { <H> >- of_some_sort{Prop} }

interactive setHasSort {| intro [] |} :
   sequent { <H> >- of_some_sort{Set} }

interactive typeHasSort {| intro [] |} :
   sequent { <H> >- of_some_sort{"type"[i:l]} }

(* Set is a sort *)
prim set_is_sort {| intro [] |} :
	sequent { <H> >- is_sort{Set} } = it

(* Prop is a sort *)
prim prop_is_sort {| intro [] |} :
	sequent { <H> >- is_sort{Prop} } = it

(* Type[i] is a sort *)
prim type_is_sort {| intro [] |} :
	sequent { <H> >- is_sort{"type"[i:l]} } = it

(****************************************************
* Tentative axioms stating that type Prop (Set)
* is sort Prop or sort Set
*****************************************************)

prim prop_a_prop_set {| intro [] |} :
   sequent { <H> >- prop_set{Prop} } = it

prim set_a_prop_set {| intro [] |} :
   sequent { <H> >- prop_set{Set} } = it


(************************************************
*      RULES
*************************************************)

prim var {| intro [] |} 'H :
   sequent { <H> >- of_some_sort{'T} } -->
   sequent { <H>; x: 'T; <J['x]> >- 'x in 'T } = it

prim weak 'H :
	sequent { <H>; <J> >- 'A in 'B } -->
	sequent { <H>; <J> >- of_some_sort{'C} } -->
	sequent { <H>; x: 'C; <J> >- 'A in 'B } = it

prim prod_1 's1 :
   sequent { <H> >- prop_set{'s1}  } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H>; x:'T >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- (x:'T -> 'U['x]) in 's2  } = it

prim prod_2 's1 :
   sequent { <H>; x:'T >- prop_set{'s2}  } -->
   sequent { <H>; x:'T >- 'U['x] in 's2 } -->
   sequent { <H> >- 'T in 's1 } -->
   sequent { <H> >- (x:'T -> 'U['x]) in 's2  } = it

prim prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- 'T in "type"[i:l]  } -->
   sequent { <H>; x:'T >- 'U['x] in "type"[j:l]  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- (x:'T -> 'U['x]) in "type"[k:l] } = it


(************************************************
 *                                              *
 ************************************************)

prim lam {| intro [] |} 's :
   sequent { <H> >- (x:'T -> 'U['x]) in 's  } -->
   sequent { <H> >- is_sort{'s }  } -->
   sequent { <H>; x:'T >- 't['x] in 'U['x]  } -->
   sequent { <H> >- lambda{'T;x.'t['x]} in (x:'T -> 'U['x]) } = it


(************************************************
 *                                              *
 ************************************************)

prim app {| intro [] |} (x:'T -> 'U['x]) :
   sequent { <H> >- 'u in (x:'T -> 'U['x])  } -->
   sequent { <H> >- 't in 'T  } -->
   sequent { <H> >- apply{'u;'t} in 'U['t] } = it


(************************************************
 *                                              *
 ************************************************)

(*
prim let_in 'T bind{x.'U['x]}:
   sequent { <H> >- 't in 'T  } -->
   sequent { <H>; x:"let"{'t;'T} >- 'u['x] in 'U['x] } -->
   sequent { <H> >- let_in{'t;x.'u['x]} in 'U['t]  } = it
*)

(************************************************
*                CONVERSION RULES               *
*************************************************)

declare red {'x;'t} (* term 'x reduces to term 't in the context H *)


(*
prim beta :
   sequent { <H> >- red{ apply{ lambda{'T; x.'t['x]}; 'u }; 't['u] } } = it
*)

prim_rw beta {| reduce |} :
   ( apply{ lambda{'T; x.'t['x]}; 'u } ) <--> ( 't['u] )

(*
prim delta_let 'H:
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- red{ 'x ; 't } } = it

prim delta_let_concl 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] } = it

prim delta_let_hyp 'H 'J bind{x.'C['x]} bind{x.'D['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['t]; <K['x]> >- 'C['x] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]>; 'D['x]; <K['x]> >- 'C['x] } = it

prim delta_let_all 'H bind{x.'C['x]} :
   sequent { <H>; x:"let"{'t;'T} ; <J['t]> >- 'C['t] } -->
	sequent { <H>; x:"let"{'t;'T} ; <J['x]> >- 'C['x] } = it

prim zeta :
   sequent { <H> >- red{ let_in{ 'u; x.'t['x] }; 't['u] } } = it

prim_rw zeta {| reduce |} :
   let_in{ 'u; x.'t['x] } <--> 't['u]
*)

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
   sequent { <H>; x:'T >- conv_le{ 'T1['x]; 'U1['x] } } -->
   sequent { <H> >- conv_le{ (x:'T -> 'T1['x]); (x:'T -> 'U1['x]) }} = it

prim conv_rule 's 'T:
   sequent { <H> >- 'U in 's } -->
   sequent { <H> >- 't in 'T } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- 't in 'U } = it
