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
declare has_type{'t;'T} (* term 't has a type 'T*)
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

(*****************************************************
*   The type of a type is always a constant of the
*   language of CIC called a 'sort'.
*   Set, Prop, Type[i] are sorts.
******************************************************)

(* Prop is a sort *)
prim prop_a_sort:
   sequent { <H> >- has_type{'P;Prop} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* Set is a sort *)
prim set_a_sort:
   sequent { <H> >- has_type{'P;Set} } -->
   sequent { <H> >- of_some_sort{'P} } = it

(* Type[i] is a sort *)
prim type_a_sort "type"[i:l]:
   sequent { <H> >- has_type{'P;"type"[i:l]} } -->
   sequent { <H> >- of_some_sort{'P} } = it


(****************************************************
* Tentative axioms stating that type Prop (Set)
* is sort Prop or sort Set
*****************************************************)

prim prop_a_prop_set:
   sequent { <H> >- has_type{'P;Prop} } -->
   sequent { <H> >- prop_set{'P} } = it

prim set_a_prop_set:
   sequent { <H> >- has_type{'P;Set} } -->
   sequent { <H> >- prop_set{'P} } = it


(************************************************
*      RULES
*************************************************)

prim w_e :
   sequent { >- WF } = it

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
   sequent { <H> >-  has_type{'t;'T} } -->
   sequent { <H>; x: "let"{'t;'T} >- WF } = it


(************************************************
 *                                              *
 ************************************************)


(************************************************
 *                                              *
 ************************************************)

prim ax_prop :
   sequent { <H> >- WF } -->
   sequent { <H> >- has_type{Prop;"type"[i:l]}  } = it



prim ax_set :
   sequent { <H> >- WF } -->
   sequent { <H> >- has_type{Set;"type"[i:l]}  } = it



prim ax_type :
   sequent { <H> >- WF } -->
   sequent { <H> >- has_type{"type"[i:l];"type"[i':l]}  } = it


(************************************************
 *                                              *
 ************************************************)

prim var_decl 'H:
   sequent { <H>; x: decl{'T}; <J['x]> >- WF } -->
   sequent { <H>; x: decl{'T}; <J['x]> >- has_type{'x;'T}  } = it



prim var_let 'H:
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- WF } -->
   sequent { <H>; x: "let"{'t;'T}; <J['x]> >- has_type{'x;'T}  } = it


(************************************************
 *                                              *
 ************************************************)

prim prod_1 's1:
   sequent { <H> >- prop_set{'s1}  } -->
   sequent { <H> >- has_type{ 'T; 's1 } } -->
   sequent { <H>; x:decl{'T} >- has_type{ 'U['x]; 's2 } } -->
   sequent { <H> >- has_type{ product{'T;x.'U['x]}; 's2  }  } = it

prim prod_2 's1:
   sequent { <H>; x:decl{'T} >- prop_set{'s2}  } -->
   sequent { <H>; x:decl{'T} >- has_type{ 'U['x]; 's2 } } -->
   sequent { <H> >- has_type{ 'T; 's1 } } -->
   sequent { <H> >- has_type{ product{'T;x.'U['x]}; 's2  }  } = it

prim prod_types "type"[i:l] "type"[j:l] :
   sequent { <H> >- has_type{'T;"type"[i:l]}  } -->
   sequent { <H>; x:decl{'T} >- has_type{ 'U['x]; "type"[j:l] }  } -->
   sequent { >- le[i:l,k:l]  } -->
   sequent { >- le[j:l,k:l]  } -->
   sequent { <H> >- has_type{ product{'T;x.'U['x]}; "type"[k:l] } } = it


(************************************************
 *                                              *
 ************************************************)

prim lam 's:
   sequent { <H> >- has_type{ product{'T;x.'U['x]}; 's }  } -->
   sequent { <H> >- of_some_sort{'s }  } -->
   sequent { <H>; x:decl{'T} >- has_type{ 't['x]; 'U['x] }  } -->
   sequent { <H> >- has_type{ lambda{'T;x.'t['x]}; product{'T;x.'U['x]} } } = it


(************************************************
 *                                              *
 ************************************************)

prim app product{'U; x.'T['x]} :
   sequent { <H> >- has_type{ 't; product{'U; x.'T['x]} }  } -->
   sequent { <H> >- has_type{ 'u;'U }  } -->
   sequent { <H> >- has_type{ app{'t;'u}; 'T['u]  } } = it


(************************************************
 *                                              *
 ************************************************)

prim let_in 'T bind{x.'U['x]}:
   sequent { <H> >- has_type{'t;'T}  } -->
   sequent { <H>; x:"let"{'t;'T} >- has_type{'u['x];'U['x]} } -->
   sequent { <H> >- has_type{ let_in{'t;x.'u['x]}; 'U['t] }  } = it


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
   sequent { <H> >- has_type{ 'U; 's } } -->
   sequent { <H> >- has_type{ 't; 'T } } -->
   sequent { <H> >- conv_le{ 'T; 'U } } -->
   sequent { <H> >- has_type{ 't; 'U } } = it

(*********************************************
 *         INDUCTIVE DEFINITIONS PART        *
**********************************************)

(* Coq's Ind(H)[Hp](Hi:=Hc) - inductive definition *)
declare Ind       (* *)
declare IndDef    (* for ind.defenitions, Hi - new types, defenitions of new types *)
declare IndParam (* for ind. defenirions, Hp - parameters of ind. defenition *)
declare IndConstrs (* for ind. defenitions, Hc - constructors *)

(* declaration of a multiple product, i.e. (p1:P1)(p2:P2)...(pr:Pr)T *)
declare prodH     (*{ <H> >- 'T }*)


(* inductive definition of multiple product *)
prim_rw prodH_base :
   sequent [prodH] { x:'T >- 'S['x] } <--> product{'T; x.'S['x]}

prim_rw prodH_step :
   sequent [prodH] { <H>; x:'T >- 'S['x] } <-->
	sequent [prodH] { <H> >- product{'T;x.'S['x]} }


prim_rw test 'H :
   (sequent [Ind] { <H>; x:'T; <J['x]> >- 't['x]}) <-->
   (sequent [Ind] { <H>; x:'T; <J['x]> >- 't[IndDef] })

(* base axioms about Ind and IndDef *)
(* for new types *)
prim_rw indSubstDef 'Hi1 :
   sequent [IndParam] { <Hp> >-
	   (sequent [IndDef] { <Hi1>; x:'T; <Hi2['x]> >-
		   (sequent [IndConstrs] { <Hc['x]> >- 't['x]})})} <-->
   sequent [IndParam] { <Hp> >-
	   (sequent [IndDef] { <Hi1>; x1:'T; <Hi2['x1]> >-
		   (sequent [IndConstrs] { <Hc['x1]> >-
			   't[sequent [IndParam] { <Hp> >-
				   (sequent [IndDef] { <Hi1>; x:'T; <Hi2['x]> >-
				      sequent [IndConstrs] { <Hc['x]> >- 'x}})}] })})}

(* for constructors (names, types) *)
prim_rw indSubstConstr 'Hc1 :
   sequent [IndParam] { <Hp> >-
	   sequent [IndDef] { <Hi> >-
		   sequent [IndConstrs] { <Hc1>; c:'C<|Hi;Hp|>; < Hc2<|Hi;Hp|> > >- 't['c]}}} <-->
   sequent [IndParam] { <Hp> >-
	   sequent [IndDef] { <Hi> >-
		   sequent { <Hc1>; c1:'C<|Hi; Hp|>; < Hc2<|Hi; Hp|> > >-
				't[ sequent [IndParam] { <Hp> >-
				   sequent [IndDef] { <Hi> >-
				      sequent [IndConstrs] { <Hc1>; c:'C<|Hi; Hp|>; < Hc2<|Hi; Hp|> > >- 'c}}}]}}}

(* carry out ground terms from the Ind *)
prim_rw indCarryOut :
   sequent { <H> >-
	   sequent [IndParam] { <Hp> >-
		   sequent [IndDef] { <Hi> >-
	         sequent [IndConstrs] { <Hc> >- 't<||> } } }} <-->
	't<||>


(* implementation of the first part of the Coq's Ind-Const rule *)
(*prim_rw ind_ConstDef 'Hi1 :
   sequent [Ind] { <H> >- sequent { <Hp> >- sequent { <Hi1>; I:'A; <Hi2> >-
	   sequent { <Hc> >- WF }}} } <-->
	sequent [Ind] { <H> >- sequent { <Hp> >- sequent { <Hi1>; I:'A; <Hi2> >-
	   sequent { <Hc> >- has_type{'I;sequent [prodH] { <Hp> >- 'A}} }}} }
*)
prim ind_ConstDef 'Hi1 :
   sequent { <H> >-
	   WF{
		   sequent [IndParam] { <Hp> >-
		      sequent [IndDef] { <Hi1>; I:'A<|Hp;H|>; <Hi2> >-
		         sequent [IndConstrs] { <Hc<|Hp;H;Hi1;Hi2|>['I]> >- it }}} } } -->
	sequent { <H> >-
		has_type {
			sequent [IndParam] { <Hp> >-
				sequent [IndDef] { <Hi1>; I:'A<|Hp;H|>; <Hi2> >-
					sequent { <Hc<|Hp;H;Hi1;Hi2|>['I]> >- 'I} }};
			sequent [prodH] { <Hp> >- 'A}} } } = it


(*		 sequent [IndDef] { <Hi1>; I:'A<|Hp;H|>; <Hi2> >- sequent { <Hc<|Hp;H;Hi1;Hi2|>['I]> >-
		    has_type{ 'I; sequent [prodH] { <Hp> >- 'A} } }}} } = it
*)

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
(* old uncorrected
prim ind_ConstConstr :
   sequent {Ind{ <H> >- ( <Hp> >- ( <Hi> >- (<Hc1>; c:'C; <Hc2['x]> >-
	   has_type{'c;prodH{ <Hp> >- sequent [substH] {<Hp> ( <Hi> >- 'C)}}} ))) }}  = it
*)
(*
prim ind_ConstConstr 'Hc1 :
   sequent [Ind] { <H> >- sequent { <Hp> >- sequent { <Hi> >-
	   sequent { <Hc1>; c:'C; <Hc2['c]> >- WF }}} }  -->
	sequent [Ind] { <H> >- sequent { <Hp> >- sequent { <Hi> >-
	   sequent { <Hc1>; c:'C; <Hc2['c]> >-
		   has_type{'c;sequent { <Hp> >- sequent [substH] { <Hi> >- 'C}}} }}} } = it
*)
prim ind_ConstConstrs 'Hc1 :
   sequent { <H> >-
	   WF {
		   sequent [IndParam] { <Hp> >-
			   sequent [IndDef] { <Hi> >-
	            sequent [IndConstrs] { <Hc1>; c:'C<|Hp;H;Hi|>; <Hc2['c]> >- it }}} }}  -->
	sequent { <H> >-
	   has_type {
		   sequent [IndParam] { <Hp> >-
			   sequent [IndDef] { <Hi> >-
	            sequent [IndConstrs] { <Hc1>; c:'C<|Hp;H;Hi|>; <Hc2['c]> >- 'c }}};
			sequent { <Hp> >- sequent [substH] { <Hi> >- 'C}}} } = it


(*******************************************************************************************
 *  in the next part the conditions for the W-Ind rule and the W-Ind rule are implemented  *
 *******************************************************************************************)

declare of_some_sort (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

declare has_type_m (* { <I> >- ( <T> >- has_type_m ) } *) (* multiple has_type, i.e. I={I1,...,Ik}, T={T1,...,Tk},
                                         has_type{Ij;Tj}, j=1,..,k *)
(* declaration of 'arity of sort' notion *)
declare arity_of_sort_m (* (<Hi> >- <S>)*) (* Hi={I1:A1,...,Ik:Ak}, S={s1,...,sk},
                                            Aj is an arity of sort sj, j=1,...,k*)
declare arity_of_sort{'T} (* type T is an arity of some sort *)

prim arity_of_sort_Set :
   sequent { <H> >- conv_le{'T;Set} } -->
	sequent { <H> >- arity_of_sort{'T} } = it

prim arity_of_sort_Prop :
   sequent { <H> >- conv_le{'T;Prop} } -->
	sequent { <H> >- arity_of_sort{'T} } = it

prim arity_of_sort_Type "type"[i:l] :
   sequent { <H> >- conv_le{'T;"type"[i:l]} } -->
	sequent { <H> >- arity_of_sort{'T} } = it

prim arity_of_sort_prod 'T1 bind{x.'U['x]} :
   sequent { <H> >- conv_le{'T; product{'T1;x.'U['x]}} } -->
	sequent { <H>; x:'T1 >- arity_of_sort{'U['x]} } -->
	sequent { <H> >- arity_of_sort{'T} } = it

prim arity_of_sort_m_base :
   sequent { <H> >- arity_of_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_sort_m] { t:'T >- arity_of_sort_m } } = it

prim arity_of_sort_m_step :
   sequent { <H> >- arity_of_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_sort_m] { <T1> >- arity_of_sort_m} } -->
   sequent { <H> >- sequent [arity_of_sort_m] { <T1>; t:'T<||> >- arity_of_sort_m } } = it

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
   sequent { <H>; x: 'T; <J['x]> >- sequent [applH] { <T1> >- 'x} } -->
	sequent { <H>; x: 'T; <J['x]> >-
	   positivity_cond{ sequent [applH] { <T1> >- 'x} ;'x } } = it

prim positivity_cond_2 'H bind{x.'T['x]} bind{y,x.'U['y;'x]}:
   sequent { <H>; x:'S; <J['x]> >- strictly_pos{'x;'T['x]}} -->
	sequent { <H>; x:'S; <J['x]>; y:'T['x] >- positivity_cond{'U['y;'x];'x} } -->
	sequent { <H>; x:'S; <J['x]> >- positivity_cond{product{'T['x];y.'U['y;'x]};'x} } = it


(* declaration of 'strictly positive' notion *)
prim strictly_pos_1 'H :
   sequent { <H>; x:'T1; <J['x]>  >- strictly_pos{'x;'T} } = it

prim strictly_pos_2 'H :
	sequent { <H>; x:'T1; <J['x]> >- strictly_pos{'x;sequent [applH] { <T2> >- 'x}} } = it

prim strictly_pos_3 'H 'U bind{x,y.'V['x;'y]} :
   sequent { <H>; x:'T2; <J['x]>; x1:'U >- strictly_pos{'x;'V['x1;'x]} } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{'x ; product{ 'U;x1.'V['x1;'x]}} } = it

prim strictly_pos_4 'H 'T1:
   sequent { <H>; x:'T2; <J['x]>  >-
		sequent [IndParam] { <Hp> >-
	         sequent [IndDef] { I:'A<|Hp;H;J|>['x] >-
			      sequent [IndConstrs] { <Hc<|Hp;H;J|>['I;'x]> >- it } } } } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   sequent [imbr_pos_cond_m] { <Hc<|Hp;H;J|>['I;'x]> >-
		   sequent { 'I >- 'x } } } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{
		   'x;
			sequent [applH] { <T1>; <A1['x]> >- 'I }} } = it




(* declaration of 'imbricated positivity condition' notion *)

prim imbr_pos_cond_1 :
   sequent { <H>; x:'T; <J['x]> >- imbr_pos_cond{sequent [applH] { <T1> >- 'I};'I;'x} = it

prim imbr_pos_cond_2 bind{x,y.'U['x,'y]} :
   sequent { <H>; x:'T2; <J['x]> >- strictly_pos{'x;'T['x]} } -->
	sequent { <H>; x:'T2; <J['x]> >- imbr_pos_cond{'U['x]; ;'x} } -->
	sequent { <H>; x:'T2; <J['x]> >- imbr_pos_cond{product{'T['x];x1.'U['x1,'x]};'I;'x} } = it

(* inductive definition of multiple imbricated positivity condition, i.e.
   of imbr_pos_cond_m *)
prim imbr_pos_cond_m_base :
   sequent { <H> >- imbr_pos_cond{'C;'I;'x} } -->
	sequent { <H> >- sequent [imbr_pos_cond_m] { c:'C >- sequent { 'I >- 'x } } } = it

prim imbr_pos_cond_m_step :
   sequent { <H> >- imbr_pos_cond{'C;'I;'x} } -->
	sequent { <H> >- sequent [imbr_pos_cond_m] { <Hc> >- ( 'I >- 'x ) } } -->
	sequent { <H> >- sequent [imbr_pos_cond_m] { <Hc>; c:'C >- ( 'I >- 'x ) } } = it


(* declaration of 'of some sort' notion *)
declare of_some_sort_m (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

(* inductive defenition of multiple of_come_sort_m *)
prim of_some_sort_m_base :
   sequent { <H> >- of_some_sort{'T} } -->
	sequent { <H> >- sequent [of_some_sort_m] { t:'T >- of_some_sort_m } }

prim of_some_sort_m_step :
   sequent { <H> >- of_some_sort{'T2} } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1> >- of_some_sort_m } } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1>; t:'T2 >- of_some_sort_m } }


(* description-defenition of the third condition in the declaration of w_Ind rule*)
declare req3{'C}
declare req3_m

prim req3_intro 'Hi 's :
   sequent { <H> >- sequent { <Hi>; I:'A; <Ji['I]> >- type_of_constructor{'C;'I} } } -->
   sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A; <Ji['I]> >- 'I } } -->
	sequent { <H> >- arity_of_sort{'A;'s} } -->
	sequent { <H> >- sequent { <Hi>; I:'A; <Ji['I]> >- has_type{'C;'s} } } -->
   sequent { <H> >- sequent { <Hi>; I:'A; <Ji['I]> >- req3{'C} } }

prim req3_m_base :
   sequent { <Hi> >- req{'C} } -->
	sequent { <Hi> >- sequent [req3_m] { c:'C >- req3 } }

prim req3_m_step :
	sequent { <Hi> >- sequent [req3_m] { <Hc> >- req3 } } -->
	sequent { <Hi> >- req3{'C} } -->
	sequent { <Hi> >- sequent [req3_m] { <Hc>; c:'C >- req3 } } = it


(* implementation of the Coq's W-Ind rule *)
prim w_Ind :
   sequent { <H>; <Hp> >- sequent [of_some_sort_m] { <Hi> >- of_some_sort_m } } -->
	sequent { <H>; <Hp> >- sequent [arity_of_sort_m] { <Hi> >- arity_of_sort_m } } -->
	sequent { <H>; <Hp> >- sequent { <Hi> >- sequent [req3_m] { <Hc> >- req3 } } } -->
	sequent [Ind] { <H> >- sequent { <Hp> >- sequent { <Hi> >- sequent { <Hc> >- WF } } } }


(****************************************************************
 * *
 ****************************************************************)


