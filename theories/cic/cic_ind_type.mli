extends Cic_lambda

open Basic_tactics

(*********************************************
 *         INDUCTIVE DEFINITIONS PART        *
**********************************************)

(* Coq's Ind(H)[Hp](Hi:=Hc) - inductive definition *)
declare sequent [IndTypes] { Term : Term >- Term } : Term (* for ind.defenitions, Hi - new types, defenitions of new types *)
declare sequent [IndParams] { Term : Term >- Term } : Term (* for ind. defenirions, Hp - parameters of ind. defenition *)
declare sequent [IndConstrs] { Term : Term >- Term } : Term (* for ind. defenitions, Hc - constructors *)

(*
 * These sequent args are used to state the well-formedness
 * of an inductive definition. We need them to distinguish WF
 * judgements from other uses of inductive definitions in order
 * to make indCarryOut inapplicable to WF judgements.
 *)
declare sequent [IndTypesWF] { Term : Term >- Term } : Term
declare sequent [IndParamsWF] { Term : Term >- Term } : Term
declare sequent [IndConstrsWF] { Term : Term >- Term } : Term

(* declaration of a multiple product, i.e. (p1:P1)(p2:P2)...(pr:Pr)T *)
declare sequent [prodH] { Term : Term >- Term } : Term


(* inductive definition of multiple product *)
rewrite prodH_base :
   prodH{| >- 'S |} <--> 'S

rewrite prodH_step :
   prodH{| <H>; x:'T >- 'S['x] |} <-->
	prodH{| <H> >- x:'T -> 'S['x] |}

topval fold_prodH_base : conv
topval fold_prodH_step : conv
topval fold_prodH : conv
(*
topval conclAddrC : conv -> conv
topval indHeadAddrC : conv -> conv
*)
(* base axioms about Ind and IndTypes *)
(* for new types *)
rewrite indSubstDef 'Hi :
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x]> >- 't['x]})})} <-->
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x1:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x1]> >-
			   't[sequent [IndParams] { <Hp> >-
				   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
				      sequent [IndConstrs] { <Hc['x]> >- 'x}})}] })})}

topval indFoldDefC : int -> term -> conv -> conv
topval indFoldHDefC : int -> term -> conv -> conv

(* for constructors (names, types) *)
rewrite indSubstConstr 'Hc :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c:'C<|Hi;Hp|>; < Jc<|Hi;Hp|> > >- 't['c]}}} <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c1:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >-
				't[ sequent [IndParams] { <Hp> >-
				   sequent [IndTypes] { <Hi> >-
				      sequent [IndConstrs] { <Hc>; c:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >- 'c}}}]}}}

topval indFoldConstrC : int -> term -> conv -> conv
topval indFoldHConstrC : int -> term -> conv -> conv

(* carry out ground terms from the Ind *)
rewrite indCarryOut :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't<||> } } } <-->
	't<||>

rewrite indWrap
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi> >-
				sequent [IndConstrs] { <Hc> >- 'aux } } } ('t :> Term) :
	't <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't<||> } } }

(*
rewrite indWrap
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi> >-
				sequent [IndConstrs] { <Hc> >- 'aux } } } :
	('t in 'T) <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't in 'T } } }
*)

topval indWrapC : term -> conv -> conv

rewrite mergeIndApp :
	(
	 IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'f|}|}|}
	 IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'arg|}|}|}
	) <-->
	IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'f 'arg|}|}|}

(* implementation of the first part of the Coq's Ind-Const rule *)
rule ind_ConstDef 'Hi :
   sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { <Hi>; I:'A<|Hp;H|>; <Ji<|Hp;H|> > >-
		      sequent [IndConstrsWF] { <Hc['I]> >- it }}} } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I:'A<|Hp;H|>; <Ji<|Hp;H|> > >-
				sequent [IndConstrs] { <Hc['I]> >- 'I } } }
		in	prodH{| <Hp> >- 'A|} }

(* declaration of a multiple application, i.e. (...((Ip1)p2)p3...)pr *)
declare sequent [applH] { Term : Term >- Term } : Term

topval fold_applHBase : conv
topval fold_applHStep : conv
topval fold_applH : conv
topval applHC : conv

declare sequent [lambdaH] { Term : Term >- Term } : Term

rewrite lambdaHBase :
	lambdaH{| >-'t|} <--> 't

rewrite lambdaHStep :
	lambdaH{|<H>; x:'s >-'t['x]|} <--> lambdaH{|<H> >-lambda{'s; x.'t['x]}|}

topval fold_lambdaHBase : conv
topval fold_lambdaHStep : conv
topval fold_lambdaH : conv

declare sequent [IndParamsSubst] { Term : Term >- Term } : Term
declare sequent [IndTypesSubst] { Term : Term >- Term } : Term
declare sequent [IndConstrsSubst] { Term : Term >- Term } : Term
declare sequent [IndParamsSubstApp] { Term : Term >- Term } : Term
declare sequent [IndTypesSubstApp] { Term : Term >- Term } : Term
declare sequent [IndConstrsSubstApp] { Term : Term >- Term } : Term
declare sequent [Aux] { Term : Term >- Term } : Term

topval fold_substStart : conv
topval fold_substStep : conv
topval fold_substFinal : conv
topval fold_appStart : conv
topval fold_appStepC : conv
topval fold_appFinalC : conv
topval fold_substApp : conv
topval fold_substProdStart: conv
topval fold_substProdStep: conv
topval fold_substProd: conv
topval fold_subst : conv
topval substProdStart : conv
topval substProdStep : conv
topval substFinal : conv
topval substApp : conv
topval appStart : conv
topval appStep : conv
topval appFinal : conv
topval substC : conv
topval substStart : conv
topval substStep : conv
topval substProd : conv


(* implementation of the second part of the Coq's Ind-Const rule *)
rule ind_ConstConstrs 'Hc :
   sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { <Hi> >-
	         sequent [IndConstrsWF] { <Hc>; c:'C<|Hi;Hp;H|>; <Jc<|Hi;Hp;H|>['c]> >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParams] { <Hp> >-
		   sequent [IndTypes] { <Hi> >-
	         sequent [IndConstrs] { <Hc>; c:'C<|Hi;Hp;H|>; <Jc<|Hi;Hp;H|>['c]> >- 'c }}}
		in
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { <Hi> >-
	         sequent [IndConstrsSubst] { <Hc>; c:'C<|Hi;Hp;H|>; <Jc<|Hi;Hp;H|>['c]> >-
				   'C } } } }

(*******************************************************************************************
 *  in the next part the conditions for the W-Ind rule and the W-Ind rule are implemented  *
 *******************************************************************************************)

(* declaration of 'arity of sort' notion *)
declare sequent [arity_of_some_sort_m] { Term : Term >- Term } : Term (* (<Hi> >- <S>)*) (* Hi={I1:A1,...,Ik:Ak}, S={s1,...,sk}, Aj is an arity of sort sj, j=1,...,k*)

declare arity_of_some_sort{'T} (* type T is an arity of some sort *)

rule arity_of_some_sort_Set :
   sequent { <H> >- arity_of_some_sort{Set} }

rule arity_of_some_sort_Prop :
	sequent { <H> >- arity_of_some_sort{Prop} }

rule arity_of_some_sort_Type :
   sequent { <H> >- arity_of_some_sort{"type"[i:l]} }

rule arity_of_some_sort_prod (*bind{x.'U['x]}*) :
   sequent { <H>; x:'T1 >- arity_of_some_sort{'U['x]} } -->
	sequent { <H> >- arity_of_some_sort{ (x:'T1->'U['x]) } }

rule arity_of_some_sort_m_base :
   sequent { <H> >- sequent [arity_of_some_sort_m] { >- arity_of_some_sort_m } }

rule arity_of_some_sort_m_step :
   sequent { <H> >- arity_of_some_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_some_sort_m] { <T1> >- arity_of_some_sort_m} } -->
   sequent { <H> >- sequent [arity_of_some_sort_m] { <T1>; t:'T<||> >- arity_of_some_sort_m } }

declare arity_of_sort{'T;'s} (* type T is an arity of sort 's *)

rule arity_of_sort_Set :
   sequent { <H> >- arity_of_sort{Set;Set} }

rule arity_of_sort_Prop :
   sequent { <H> >- arity_of_sort{Prop;Prop} }

rule arity_of_sort_Type :
   sequent { <H> >- arity_of_sort{"type"[i:l];"type"[i:l]} }

rule arity_of_sort_prod (*bind{x.'U['x]}*) :
   sequent { <H>; x:'T1 >- arity_of_sort{'U['x]; 's} } -->
	sequent { <H> >- arity_of_sort{(x:'T1 -> 'U['x]); 's} }

(* declaration of 'type of constructor' notion *)
declare type_of_constructor{'T;'I} (* 'T is a type of constructor of 'I *)

rule type_of_constructor_app :
   sequent { <H> >- type_of_constructor{ applH{| <T1> >- 'I<|H|> |}; 'I } }

rule type_of_constructor_prod 'T1 (*bind{x.'C['x]}*) :
   sequent { <H>; x:'T1 >- type_of_constructor{'C['x];'I} } -->
	sequent { <H> >- type_of_constructor{ (x:'T1 -> 'C['x]); 'I } }

declare sequent [imbr_pos_cond_m] { Term : Term >- Term } : Term
(* { <Hc> >-( 'I >- 'x ) } *)
(* Hc={c1:C1,...,cn:Cn}, the types constructor Ci (each of them) of 'I
satisfies the imbricated positivity condition for a constant 'x *)

declare imbr_pos_cond{'T;'I;'x} (* the type constructor 'T of 'I satisfies the imbricated positivity
                                   condition of 'x *)

declare strictly_pos{'x;'T} (* constant 'x occurs strictly positively in 'T *)

declare positivity_cond{ 'T; 'x } (* the type of constructor 'T satisfies the positivity
												condition for a constant 'x *)

(* declaration of 'positivity condition' notion *)
rule positivity_cond_1 'H :
	sequent { <H>; x:'T; <J['x]> >-
	   positivity_cond{ applH{| <T1> >- 'x|} ;'x } }

rule positivity_cond_2 'H (*bind{x.'T['x]} bind{y,x.'U['y;'x]}*) :
   sequent { <H>; x:'S; <J['x]> >- strictly_pos{'x;'T['x]}} -->
	sequent { <H>; x:'S; <J['x]>; y:'T['x] >- positivity_cond{'U['y;'x];'x} } -->
	sequent { <H>; x:'S; <J['x]> >- positivity_cond{(y:'T['x] -> 'U['y;'x]);'x} }

(* declaration of multiple positivity condition *)
declare sequent [positivity_cond_m] { Term : Term >- Term } : Term

rule positivity_cond_m_base :
   sequent { <H>; I:'A >- positivity_cond{'C['I];'I} } -->
	sequent { <H> >- sequent [positivity_cond_m] { I:'A >- 'C['I] } }

rule positivity_cond_m_step :
   sequent { <H>; I:'A >- sequent [Aux] { <Hi> >- positivity_cond{'C['I];'I} } } -->
	sequent { <H>; I:'A >- sequent [positivity_cond_m] { <Hi > >- 'C['I] } } -->
	sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|> >- 'C['I] } }

(* declaration of 'strictly positive' notion *)
rule strictly_pos_1 'H :
   sequent { <H>; x:'T1; <J['x]>  >- strictly_pos{'x;'T} }

rule strictly_pos_2 'H :
	sequent { <H>; x:'T1; <J['x]> >- strictly_pos{'x;applH{| <T2> >- 'x|}} }

rule strictly_pos_3 'H (*'U bind{x,y.'V['x;'y]}*) :
   sequent { <H>; x:'T2; <J['x]>; x1:'U >- strictly_pos{'x;'V['x1;'x]} } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{'x ; (x1:'U -> 'V['x1;'x])} }

(*
rule strictly_pos_4 'H :
   sequent { <H>; x:'T2; <J['x]>; <A1['x]> >-
	   sequent [imbr_pos_cond_m] { <Hc<|A1;H;J|>['I;'x]> >-
		   sequent { 'I >- 'x } } } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{
		   'x;
			applH{| <T1>; <A1['x]> >-
				sequent [IndParams] { <Hp> >-
					sequent [IndTypes] { I:'A<|Hp;H;J|>['x] >-
						sequent [IndConstrs] { <Hc<|Hp;H;J|>['I;'x]> >- 'I } } } |}} }
*)



(* declaration of 'imbricated positivity condition' notion *)

rule imbr_pos_cond_1 'H :
   sequent { <H>; x:'T; <J['x]> >-
	   type_of_constructor{ applH{| <T1> >- 'I<|J;H|>['x]|} ;'I<|J;H|>['x]} } -->
	sequent { <H>; x:'T; <J['x]> >-
	   imbr_pos_cond{ applH{| <T1> >- 'I<|J;H|>['x]|};'I<|J;H|>['x];'x} }

rule imbr_pos_cond_2 'H (*bind{x,y.'U['x;'y]}*) :
   sequent { <H>; x:'T2; <J['x]> >- type_of_constructor{ (x1:'T['x] -> 'U['x1;'x]) ;'I} } -->
   sequent { <H>; x:'T2; <J['x]> >- strictly_pos{'x;'T['x]} } -->
	sequent { <H>; x:'T2; <J['x]>; x1:'T['x] >- imbr_pos_cond{'U['x1;'x];'I;'x} } -->
	sequent { <H>; x:'T2; <J['x]> >- imbr_pos_cond{(x1:'T['x] -> 'U['x1;'x]);'I;'x} }

(* inductive definition of multiple imbricated positivity condition, i.e.
   of imbr_pos_cond_m *)
declare imbr_params{'I;'x}

rule imbr_pos_cond_m_base 'H :
	sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { >- imbr_params{'I['x];'x} } }

rule imbr_pos_cond_m_step 'H :
   sequent { <H>; x:'T; <J['x]> >- imbr_pos_cond{'C['x];'I['x];'x} } -->
	sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { <Hc['x]> >-
			imbr_params{'I<|H;J|>['x];'x} } } -->
	sequent { <H>; x:'T; <J['x]> >- sequent [imbr_pos_cond_m] { <Hc['x]>; c:'C<|H;J|>['x] >-
	   imbr_params{'I<|H;J|>['x];'x} } }


(* declaration of 'of some sort' notion *)
declare sequent [of_some_sort_m] { Term : Term >- Term } : Term
(* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

(* inductive defenition of multiple of_come_sort_m *)
rule of_some_sort_m_base :
   sequent { <H> >- sequent [of_some_sort_m] { >- of_some_sort_m } }

rule of_some_sort_m_step :
   sequent { <H> >- is_sort{'T2} } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1> >- of_some_sort_m } } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1>; t:'T2<|H|> >- of_some_sort_m } }


(* description-defenition of the third condition in the declaration of w_Ind rule*)
declare req3{'C}
declare sequent [req3] { Term : Term >- Term } : Term
declare sequent [req3_m] { Term : Term >- Term } : Term

rule req3_intro 'Hi 's :
   sequent { <H>; <Hi>; I:'A<|H|>; <Ji<|H|> > >- type_of_constructor{'C['I];'I} } -->
   sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'I } } -->
	sequent { <H> >- arity_of_sort{'A<|H|>;'s<||>} } -->
	sequent { <H>; <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'C['I] in 's<||> } -->
   sequent { <H> >- sequent [req3] { <Hi>; I:'A<|H|>; <Ji<|H|> > >- req3{'C['I]} } }

rule req3_m_base :
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent  [Aux] { >- it } } }

rule req3_m_step :
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent [Aux] { <Hc> >- it } } } -->
	sequent { <H> >- sequent [req3] { <Hi> >- req3{'C<|Hi;H|>} } } -->
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent [Aux] { <Hc>; c:'C<|Hi;H|> >- it } } }


(* implementation of the Coq's W-Ind rule *)
rule w_Ind :
   sequent { <H>; <Hp> >-
		sequent [of_some_sort_m] { <Hi> >- of_some_sort_m } } -->
	sequent { <H>; <Hp> >-
		sequent [arity_of_some_sort_m] { <Hi> >- arity_of_some_sort_m } } -->
	sequent { <H>; <Hp> >- sequent [req3_m] { <Hi> >- sequent [Aux] { <Hc> >- it } } } -->
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
			sequent [IndTypesWF] { <Hi> >-
				sequent [IndConstrsWF] { <Hc> >- it } } } }


(****************************************************************
 * *
 ****************************************************************)


