extends Base_theory
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
declare product{'T;x.'U['x]} (* product ('x:'T)'U, x-variable, T,U-terms *)
declare lambda{'T;x.'t['x]}  (* the term ['x:'T]'t is a function which maps
                                   elements of 'T to 't - lambda_abstraction
                                   from lambda-calculus *)
declare let_in{'t;x.'u['x]} (* declaration of the let-in expressions -
                            in term 'u the var 'x is locally bound to term 't *)
declare app{'t;'u} (* declaration of "term 't applied to term 'u" *)
declare subst{'u;'x;'t} (* declaration of substitution of a term 't to all
                            free occurrences of a variable 'x in a term 'u *)
declare bind{x.'T['x]}
declare bind{x,y.'T['x;'y]}

prim collapse_base :
	sequent { <H> >- 'C } -->
	sequent { <H> >- sequent { >- 'C } } = it

prim collapse_step :
	sequent { <H>; x:'T >- sequent { <J['x]> >- 'C['x] } } -->
	sequent { <H> >- sequent { x: 'T; <J['x]> >- 'C['x] } } = it

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
   sequent { <H> >- member{ product{'T;x.'U['x]}; 's2  }  } = it

prim prod_2 's1:
   sequent { <H>; x:decl{'T} >- prop_set{'s2}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; 's2 } } -->
   sequent { <H> >- member{ 'T; 's1 } } -->
   sequent { <H> >- member{ product{'T;x.'U['x]}; 's2  }  } = it

prim prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- member{'T;"type"[i:l]}  } -->
   sequent { <H>; x:decl{'T} >- member{ 'U['x]; "type"[j:l] }  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- member{ product{'T;x.'U['x]}; "type"[k:l] } } = it


(************************************************
 *                                              *
 ************************************************)

prim lam 's:
   sequent { <H> >- member{ product{'T;x.'U['x]}; 's }  } -->
   sequent { <H> >- of_some_sort{'s }  } -->
   sequent { <H>; x:decl{'T} >- member{ 't['x]; 'U['x] }  } -->
   sequent { <H> >- member{ lambda{'T;x.'t['x]}; product{'T;x.'U['x]} } } = it


(************************************************
 *                                              *
 ************************************************)

prim app product{'U; x.'T['x]} :
   sequent { <H> >- member{ 't; product{'U; x.'T['x]} }  } -->
   sequent { <H> >- member{ 'u;'U }  } -->
   sequent { <H> >- member{ app{'t;'u}; 'T['u]  } } = it


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
   sequent { <H> >- red{ app{ lambda{'T; x.'t['x]}; 'u }; 't['u] } } = it
*)

prim_rw beta :
   ( app{ lambda{'T; x.'t['x]}; 'u } ) <--> ( 't['u] )

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
   sequent { <H> >- conv_le{ product{ 'T; x.'T1['x]}; product{ 'T; x.'U1['x] }}} = it

prim conv_rule 's 'T:
   sequent { <H> >- member{ 'U; 's } } -->
   sequent { <H> >- member{ 't; 'T } } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- member{ 't; 'U } } = it

(*********************************************
 *         INDUCTIVE DEFINITIONS PART        *
**********************************************)

(* Coq's Ind(H)[Hp](Hi:=Hc) - inductive definition *)
declare Ind       (* *)
declare IndTypes    (* for ind.defenitions, Hi - new types, defenitions of new types *)
declare IndParams (* for ind. defenirions, Hp - parameters of ind. defenition *)
declare IndConstrs (* for ind. defenitions, Hc - constructors *)

(* declaration of a multiple product, i.e. (p1:P1)(p2:P2)...(pr:Pr)T *)
declare prodH     (*{ <H> >- 'T }*)


(* inductive definition of multiple product *)
prim_rw prodH_base :
   sequent [prodH] { x:'T >- 'S['x] } <--> product{'T; x.'S['x]}

prim_rw prodH_step :
   sequent [prodH] { <H>; x:'T >- 'S['x] } <-->
	sequent [prodH] { <H> >- product{'T;x.'S['x]} }


(* base axioms about Ind and IndTypes *)
(* for new types *)
prim_rw indSubstDef 'Hi1 :
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi1>; x:'T<|Hp|>; <Hi2<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x]> >- 't['x]})})} <-->
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi1>; x1:'T<|Hp|>; <Hi2<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x1]> >-
			   't[sequent [IndParams] { <Hp> >-
				   (sequent [IndTypes] { <Hi1>; x:'T<|Hp|>; <Hi2<|Hp|> > >-
				      sequent [IndConstrs] { <Hc['x]> >- 'x}})}] })})}

(* for constructors (names, types) *)
prim_rw indSubstConstr 'Hc1 :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc1>; c:'C<|Hi;Hp|>; < Hc2<|Hi;Hp|> > >- 't['c]}}} <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent { <Hc1>; c1:'C<|Hi; Hp|>; < Hc2<|Hi; Hp|> > >-
				't[ sequent [IndParams] { <Hp> >-
				   sequent [IndTypes] { <Hi> >-
				      sequent [IndConstrs] { <Hc1>; c:'C<|Hi; Hp|>; < Hc2<|Hi; Hp|> > >- 'c}}}]}}}

(* carry out ground terms from the Ind *)
prim_rw indCarryOut :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't<||> } } } <-->
	't<||>


(* implementation of the first part of the Coq's Ind-Const rule *)
prim ind_ConstDef 'Hi1 :
   sequent { <H> >-
	   WF{
		   sequent [IndParams] { <Hp> >-
		      sequent [IndTypes] { <Hi1>; I:'A<|Hp;H|>; <Hi2<|Hp;H|> > >-
		         sequent [IndConstrs] { <Hc['I]> >- it }}} } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi1>; I:'A<|Hp;H|>; <Hi2<|Hp;H|> > >-
				sequent { <Hc['I]> >- 'I } } }
		in	sequent [prodH] { <Hp> >- 'A} } = it

(* declaration of a multiple application, i.e. (...((Ip1)p2)p3...)pr *)
declare applH (* { <H> >- 'T } *)

(*inductive definition of multiple application *)
prim_rw applH_base :
   sequent [applH] { x:'T >- sequent { <H> >- 'S} } <-->
	sequent { <H>; x:'T >- app{'S;'x} }

prim_rw applH_step :
   sequent [applH] { x:'T; <H> >- sequent { <J> >- 'S} } <-->
	sequent [applH] { <H> >- sequent { <J>; x:'T >- app{'S;'x} } }

(* Product + Application + Substitution (p1:P1)...(pn:Pn)C{I/Ip1...pn} *)
declare prodapp

prim_rw prodapp_base :
   sequent [prodapp] { >- bind{i.'C['i]} } <-->
	bind{ i.'C['i] }

prim_rw prodapp_step :
   sequent [prodapp] { <Hp>; p:'P >- bind{i.'C['i]} } <-->
	sequent [prodapp] { <Hp> >- bind{ i.product{ 'P; p.'C[app{'i;'p}] } } }


(* declaration of multiple substitution *)
declare substH (* {<Hp> >- ( <Hi> >- 'T ) } *)

(* inductive definition of multiple substitution with multiple application applied*)
(*
prim_rw substH_base :
   sequent [substH] { <Hp> >- sequent { >- 'C<|'Hp|> } } <-->  'C<|'Hp|>

prim_rw substH_step :
   sequent [substH] { <Hp> >- sequent { <Hi>; x:'T >- 'C['x] } } <-->
	sequent [substH] { <Hp> >- sequent { <Hi> >-
	   'C[ sequent [applH] { <Hp> >- 'x }] } }
*)
prim_rw substH_base :
   sequent { <Hp> >- sequent [substH] { >- 'C } } <-->
	sequent { <Hp> >- 'C }

prim_rw substH_step :
   sequent { <Hp> >- sequent [substH] { <Hi>; I:'A >- 'C['I] } } <-->
	sequent { <Hp> >- sequent [substH] { <Hi> >-
	   sequent [prodapp] { <Hp> >- bind{i.'C['i]} } } }

(* implementation of the second part of the Coq's Ind-Const rule *)
prim ind_ConstConstrs 'Hc1 :
   sequent { <H> >-
	   WF {
		   sequent [IndParams] { <Hp> >-
			   sequent [IndTypes] { <Hi> >-
	            sequent [IndConstrs] { <Hc1>; c:'C<|Hi;Hp;H|>; <Hc2<|Hi;Hp;H|>['c]> >- it }}} }}  -->
	sequent { <H> >-
	   sequent [IndParams] { <Hp> >-
		   sequent [IndTypes] { <Hi> >-
	         sequent [IndConstrs] { <Hc1>; c:'C<|Hi;Hp;H|>; <Hc2<|Hi;Hp;H|>['c]> >-
				   'c in sequent [prodH] { <Hp> >- 'C } } } } } = it


(*******************************************************************************************
 *  in the next part the conditions for the W-Ind rule and the W-Ind rule are implemented  *
 *******************************************************************************************)

declare of_some_sort (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

declare has_type_m (* { <I> >- ( <T> >- has_type_m ) } *) (* multiple has_type, i.e. I={I1,...,Ik}, T={T1,...,Tk},
                                         member{Ij;Tj}, j=1,..,k *)
(* declaration of 'arity of sort' notion *)
declare arity_of_some_sort_m (* (<Hi> >- <S>)*) (* Hi={I1:A1,...,Ik:Ak}, S={s1,...,sk},
                                            Aj is an arity of sort sj, j=1,...,k*)
declare arity_of_some_sort{'T} (* type T is an arity of some sort *)

prim arity_of_some_sort_Set :
   sequent { <H> >- arity_of_some_sort{Set} } = it

prim arity_of_some_sort_Prop :
	sequent { <H> >- arity_of_some_sort{Prop} } = it

prim arity_of_some_sort_Type :
   sequent { <H> >- arity_of_some_sort{"type"[i:l]} } = it

prim arity_of_some_sort_prod bind{x.'U['x]} :
   sequent { <H>; x:'T1 >- arity_of_some_sort{'U['x]} } -->
	sequent { <H> >- arity_of_some_sort{product{'T1;x.'U['x]}} } = it

prim arity_of_some_sort_m_base :
   sequent { <H> >- arity_of_some_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_some_sort_m] { t:'T >- arity_of_some_sort_m } } = it

prim arity_of_some_sort_m_step :
   sequent { <H> >- arity_of_some_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_some_sort_m] { <T1> >- arity_of_some_sort_m} } -->
   sequent { <H> >- sequent [arity_of_some_sort_m] { <T1>; t:'T<||> >- arity_of_some_sort_m } } = it

declare arity_of_sort{'T;'s} (* type T is an arity of sort 's *)

prim arity_of_sort_Set :
   sequent { <H> >- arity_of_sort{Set;Set} } = it

prim arity_of_sort_Prop :
   sequent { <H> >- arity_of_sort{Prop;Prop} } = it

prim arity_of_sort_Type :
   sequent { <H> >- arity_of_sort{"type"[i:l];"type"[i:l]} } = it

prim arity_of_sort_prod bind{x.'U['x]} :
   sequent { <H>; x:'T1 >- arity_of_sort{'U['x]; 's} } -->
	sequent { <H> >- arity_of_sort{product{'T1;x.'U['x]}; 's} } = it

(* declaration of 'type of constructor' notion *)
declare type_of_constructor{'T;'I} (* 'T is a type of constructor of 'I *)

prim type_of_constructor_app :
   sequent { <H> >- type_of_constructor{ (sequent [applH]{ <T1> >- 'I}); 'I } } = it

prim type_of_constructor_prod 'T1 bind{x.'C['x]} :
   sequent { <H>; x:'T1 >- type_of_constructor{'C['x];'I} } -->
	sequent { <H> >- type_of_constructor{ product{'T1;x.'C['x]}; 'I } } = it

declare imbr_pos_cond_m (* { <Hc> >-( 'I >- 'x ) } *)
(* Hc={c1:C1,...,cn:Cn}, the types constructor Ci (each of them) of 'I
satisfies the imbricated positivity condition for a constant 'x *)

declare imbr_pos_cond{'T;'I;'x} (* the type constructor 'T of 'I satisfies the imbricated positivity
                                   condition of 'x *)

declare strictly_pos{'x;'T} (* constant 'x occurs strictly positively in 'T *)

declare positivity_cond{ 'T; 'x } (* the type of constructor 'T satisfies the positivity
												condition for a constant 'x *)

(* declaration of 'positivity condition' notion *)
prim positivity_cond_1 'H :
   sequent { <H>; x:'T; <J['x]> >- sequent [applH] { <T1> >- 'x} } -->
	sequent { <H>; x:'T; <J['x]> >-
	   positivity_cond{ sequent [applH] { <T1> >- 'x} ;'x } } = it

prim positivity_cond_2 'H bind{x.'T['x]} bind{y,x.'U['y;'x]}:
   sequent { <H>; x:'S; <J['x]> >- strictly_pos{'x;'T['x]}} -->
	sequent { <H>; x:'S; <J['x]>; y:'T['x] >- positivity_cond{'U['y;'x];'x} } -->
	sequent { <H>; x:'S; <J['x]> >- positivity_cond{product{'T['x];y.'U['y;'x]};'x} } = it

(* declaration of multiple positivity condition *)
declare positivity_cond_m

prim positivity_cond_m_base :
   sequent { <H>; I:'A >- positivity_cond{'C['I];'I} } -->
	sequent { <H> >- sequent [positivity_cond_m] { I:'A >- 'C['I] } } = it

prim positivity_cond_m_step :
   sequent { <H>; I:'A >- sequent { <Hi> >- positivity_cond{'C['I];'I} } } -->
	sequent { <H>; I:'A >- sequent [positivity_cond_m] { <Hi > >- 'C['I] } } -->
	sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|> >- 'C['I] } } = it

(* declaration of 'strictly positive' notion *)
prim strictly_pos_1 'H :
   sequent { <H>; x:'T1; <J['x]>  >- strictly_pos{'x;'T} } = it

prim strictly_pos_2 'H :
	sequent { <H>; x:'T1; <J['x]> >- strictly_pos{'x;sequent [applH] { <T2> >- 'x}} } = it

prim strictly_pos_3 'H 'U bind{x,y.'V['x;'y]} :
   sequent { <H>; x:'T2; <J['x]>; x1:'U >- strictly_pos{'x;'V['x1;'x]} } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{'x ; product{ 'U;x1.'V['x1;'x]}} } = it

(*
prim strictly_pos_4 'H :
   sequent { <H>; x:'T2; <J['x]>; <A1['x]> >-
	   sequent [imbr_pos_cond_m] { <Hc<|A1;H;J|>['I;'x]> >-
		   sequent { 'I >- 'x } } } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{
		   'x;
			sequent [applH] { <T1>; <A1['x]> >-
				sequent [IndParams] { <Hp> >-
					sequent [IndTypes] { I:'A<|Hp;H;J|>['x] >-
						sequent [IndConstrs] { <Hc<|Hp;H;J|>['I;'x]> >- 'I } } } }} } = it
*)



(* declaration of 'imbricated positivity condition' notion *)

prim imbr_pos_cond_1 'H :
   sequent { <H>; x:'T; <J['x]> >-
	   type_of_constructor{ sequent [applH] { <T1> >- 'I<|J;H|>['x]} ;'I<|J;H|>['x]} } -->
	sequent { <H>; x:'T; <J['x]> >-
	   imbr_pos_cond{ sequent [applH] { <T1> >- 'I<|J;H|>['x]};'I<|J;H|>['x];'x} } = it

prim imbr_pos_cond_2 'H bind{x,y.'U['x;'y]} :
   sequent { <H>; x:'T2; <J['x]> >- type_of_constructor{ product{'T['x];x1.'U['x1;'x]} ;'I} } -->
   sequent { <H>; x:'T2; <J['x]> >- strictly_pos{'x;'T['x]} } -->
	sequent { <H>; x:'T2; <J['x]>; x1:'T['x] >- imbr_pos_cond{'U['x1;'x];'I;'x} } -->
	sequent { <H>; x:'T2; <J['x]> >- imbr_pos_cond{product{'T['x];x1.'U['x1;'x]};'I;'x} } = it

(* inductive definition of multiple imbricated positivity condition, i.e.
   of imbr_pos_cond_m *)
declare imbr_params{'I;'x}

prim imbr_pos_cond_m_base 'H :
   sequent { <H>; x:'T; <J['x]> >- imbr_pos_cond{'C['x];'I['x];'x} } -->
	sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { c:'C['x] >- imbr_params{'I['x];'x} } } = it

prim imbr_pos_cond_m_step 'H :
   sequent { <H>; x:'T; <J['x]> >- imbr_pos_cond{'C['x];'I['x];'x} } -->
	sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { <Hc['x]> >-
			imbr_params{'I<|H;J|>['x];'x} } } -->
	sequent { <H>; x:'T; <J['x]> >- sequent [imbr_pos_cond_m] { <Hc['x]>; c:'C<|H;J|>['x] >-
	   imbr_params{'I<|H;J|>['x];'x} } } = it


(* declaration of 'of some sort' notion *)
declare of_some_sort_m (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

(* inductive defenition of multiple of_come_sort_m *)
prim of_some_sort_m_base :
   sequent { <H> >- of_some_sort{'T} } -->
	sequent { <H> >- sequent [of_some_sort_m] { t:'T >- of_some_sort_m } } = it

prim of_some_sort_m_step :
   sequent { <H> >- of_some_sort{'T2} } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1> >- of_some_sort_m } } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1>; t:'T2<|H|> >- of_some_sort_m } } = it


(* description-defenition of the third condition in the declaration of w_Ind rule*)
declare req3{'C}
declare req3_m

prim req3_intro 'Hi 's :
   sequent { <H> >- sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >- type_of_constructor{'C['I];'I} } } -->
   sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'I } } -->
	sequent { <H> >- arity_of_sort{'A<|H|>;'s<||>} } -->
	sequent { <H> >- sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'C['I] in 's<||> } } -->
   sequent { <H> >- sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >- req3{'C['I]} } } = it

prim req3_m_base :
   sequent { <Hi> >- req3{'C} } -->
	sequent { <Hi> >- sequent [req3_m] { c:'C >- it } } = it

prim req3_m_step :
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent { <Hc> >- it } } } -->
	sequent { <H> >- sequent { <Hi> >- req3{'C<|Hi;H|>} } } -->
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent { <Hc>; c:'C<|Hi;H|> >- it } } } = it


(* implementation of the Coq's W-Ind rule *)
prim w_Ind :
   sequent { <H> >- sequent { <Hp> >-
		sequent [of_some_sort_m] { <Hi> >- of_some_sort_m } } } -->
	sequent { <H> >- sequent { <Hp> >-
		sequent [arity_of_some_sort_m] { <Hi> >- arity_of_some_sort_m } } } -->
	sequent { <H> >- sequent { <Hp> >- sequent [req3_m] { <Hi> >- sequent { <Hc> >- it } } } } -->
	sequent { <H> >-
	   WF{
			sequent [IndParams] { <Hp> >-
				sequent [IndTypes] { <Hi> >-
					sequent [IndConstrs] { <Hc> >- it } } } } } = it


(****************************************************************
 * *
 ****************************************************************)


