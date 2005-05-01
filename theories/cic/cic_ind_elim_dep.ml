extends Cic_ind_type
extends Cic_ind_elim

open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type
open Cic_ind_elim

declare ForAll1TConstr{'terms; 'IndDef; t,c,C.'P['t;'c;'C]}
declare ForAll1TConstrAux{'terms; 'IndDef; t,c,C.'P['t;'c;'C]}

prim forAll1TConstr_base :
	sequent { <H> >- ForAll1TConstrAux{Terms{| >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc> >- IndConstrs{| >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } = it

prim forAll1TConstr_step :
	sequent { <H> >-
		'P['t;
			IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc>; c:'C; <Jc> >- 'c|}|}|};
			IndParamsSubst{|<Hp> >- IndTypesSubst{|<Hi> >- IndConstrsSubst{|<Hc>; c:'C; <Jc> >- 'C|}|}|}
		] } -->
	sequent { <H> >- ForAll1TConstrAux{Terms{|<T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc>; c:'C >- IndConstrs{|<Jc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } -->
	sequent { <H> >- ForAll1TConstrAux{Terms{| 't; <T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc> >- IndConstrs{|c:'C; <Jc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } = it

prim forAll1TConstr_start :
	sequent { <H> >- ForAll1TConstrAux{Terms{|<T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{| >- IndConstrs{|<Hc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } -->
	sequent { <H> >-
		ForAll1TConstr{Terms{|<T> >-it|}; IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- it|}|}|}; t,c,C.'P['t;'c;'C]} } = it

let rec forAll1TConstr_aux _ =
	forAll1TConstr_step thenLT [idT; funT forAll1TConstr_aux] orelseT forAll1TConstr_base

let forAll1TConstr_iter = funT forAll1TConstr_aux

let forAll1TConstrT = forAll1TConstr_start thenT forAll1TConstr_iter

let resource intro +=
	<<ForAll1TConstr{'Terms; 'IndDef; t,c,C.'P['t;'c;'C]}>>, wrap_intro forAll1TConstrT

(*
 *	HypForAll1D{| <H> >- Aux{| <J> >- bind{x.'pred['x]} |}|} holds iff
 * (<H> >- 'pred['v]) for all declarations (v: 'T) in <J>
 *)
declare sequent [HypForAll1D] { Term : Term >- Term } : Term

prim hypForAll1D_base {| intro [] |} :
	sequent { <H> >- HypForAll1D{| <K> >- Aux{| >- bind{x.'pred['x]} |}|} } = it

prim hypForAll1D_step {| intro [] |} :
	sequent { <H> >- HypForAll1D{|<K>; v: 'T >- Aux{|<J['v]> >- bind{x.'pred['v;'x]}|}|} } -->
	sequent { <H>; <K>; v: 'T; <J['v]> >- 'pred['v;'v] } -->
	sequent { <H> >- HypForAll1D{|<K> >- Aux{|v: 'T; <J['v]> >- bind{x.'pred['v;'x]}|}|} } = it

(*
 * BackHyp{| <H> >- Back{|<ToDrop> >- BackIn{|<J> >- it|}|}|} drops |ToDrop| elements from
 * the end of <J> and then returns the last element of the rest of <J>
 *)
declare sequent [BackHyp] { Term : Term >- Term } : Term
declare sequent [Back] { Term : Term >- Term } : Term
declare sequent [BackIn] { Term : Term >- Term } : Term

prim_rw back_base {| reduce |} :
	BackHyp{|<H> >- Back{| >-BackIn{|<Prefix>; 't<||> >-it|}|}|} <--> 't

prim_rw back_step {| reduce |} :
	BackHyp{|<H> >- Back{|<ToDrop>; 'dummy >-BackIn{|<Prefix>; 't >- it|}|}|} <-->
	BackHyp{|<H> >- Back{|<ToDrop> >-BackIn{|<Prefix> >- it|}|}|}

(******************************************************************************************
 * Definition of application for left parts of declarations                               *
 ******************************************************************************************
 *)

declare prodAppShape{x.'T['x]; 't}
declare sequent [prodApp] { Term : Term >- Term } : Term

prim_rw prodApp_base :
	prodApp{| >- prodAppShape{y.'S['y]; 't} |} <-->
	'S['t]

prim_rw prodApp_step :
	prodApp{| <H>; x: 'T >- prodAppShape{y.'S['x;'y]; 't} |} <-->
	prodApp{| <H> >- prodAppShape{y.(x: 'T -> 'S['x; 'y 'x]); 't} |}
(*
let fold_prodApp_base = makeFoldC <<prodApp{| >- prodAppShape{y.'S['y]; 't} |}>> prodApp_base
let fold_prodApp_step = makeFoldC <<prodApp{| <H>; x: 'T >- prodAppShape{y.'S['x;'y]; 't} |}>> prodApp_step
let fold_prodAppC = fold_prodApp_base thenC (repeatC fold_prodApp_step)
*)
let prodAppC = (repeatC prodApp_step) thenC prodApp_base

let resource reduce += [
	<<prodAppShape{x.'T['x]; 't}>>, prodAppC;
]

(******************************************************************************************
 * definition of ElimCaseTypeDef                                                          *
 ******************************************************************************************
 *)

declare ElimCaseTypeDep{'C; 'predicates; 'c}

(* (P->C){X,Q} = P -> (P[X<-Q] ->C{X,Q}), X=I_1,..., I_n, Q=P1,...,P_n,
 * when strictly_positive(P,I_i) holds
 *)
prim_rw elimCaseTypeDep_inductive 'Hi :
	HypForAll1D{|<Hp> >- Aux{|<Hi> >- bind{I.strictly_pos{'I; prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |}}} |}|} -->
	ElimCaseTypeDep{
		IndParams{|<Hp> >-
			IndTypes{|<Hi>; I: 'A; <Ji> >-
				IndConstrs{|<Hc['I]> >-
					prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |} -> 'C['I]|}|}|};
		ElimPredicates{|<Predicates> >- it|};
		'c
	} <-->
	(p:prodH{| <P> >- applH{| <M> >-
			IndParams{|<Hp> >- IndTypes{|<Hi>; I: 'A; <Ji> >- IndConstrs{|<Hc['I]> >- 'I |}|}|} |} |} ->
		(prodApp{| <P> >-
			prodAppShape{
				x.(applH{| <M> >-
					BackHyp{|<Hp>;<Hi>;I: 'A >- Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}|}|} 'x);
				'p
			} |}
		 ->
		 ElimCaseTypeDep{
			IndParams{|<Hp> >- IndTypes{|<Hi>; I: 'A; <Ji> >- IndConstrs{|<Hc['I]> >- 'C['I] |}|}|};
			ElimPredicates{|<Predicates> >- it|};
			'c 'p}
		)
	)

(* ((x:M)C{I_1,...,I_n,P_1,...,P_n,c} = (x:M)C{I_1,...,I_n,P_1,...,P_n,c x)
 * or
 * ((x:M)C{X,Q,c} = (x:M)C{X,Q,(c x)} )
 *)
prim_rw elimCaseTypeDep_dfun {| reduce |} :
	ElimCaseTypeDep{
		IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- x:'M<||> -> 'C['x]|}|}|};
		ElimPredicates{|<Predicates> >- it|};
		'c
	} <-->
	(x:'M ->
		ElimCaseTypeDep{
			IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'C['x]|}|}|};
			ElimPredicates{|<Predicates> >- it|};
			'c 'x
		}
	)

interactive_rw elimCaseTypeDep_fun {| reduce |} :
	ElimCaseTypeDep{
		IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'M<||> -> 'C|}|}|};
		ElimPredicates{|<Predicates> >- it|};
		'c
	} <-->
	(x:'M ->
		ElimCaseTypeDep{
			IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- 'C|}|}|};
			ElimPredicates{|<Predicates> >- it|};
			'c 'x
		}
	)

(* (I_i <a>){I_1,...,I_n,P_1,...,P_n,c} = ((P_i <a>) c)
 * or
 * (X <a>){X,Q,c} = ((Q <a>) c)
 *)
prim_rw elimCaseTypeDep_applH 'Hi :
	ElimCaseTypeDep{
		IndParams{|<Hp> >- IndTypes{|<Hi>; I: 'A; <Ji> >- IndConstrs{|<Hc['I]> >- applH{|<Args<||> > >- 'I|}|}|}|};
		ElimPredicates{|<Predicates> >- it|};
		'c
	} <-->
	(applH{|<Args<||> > >- BackHyp{|<Hp>;<Hi>;I: 'A >- Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}|}|} 'c)

declare good_dep{'sort1; 'sort2}

(**********************************************************************************************************
 * the typing rule for dependent elimination for mutually inductive definitions
 **********************************************************************************************************
 * given Ind(X_1:A1, ..., X_n:A_n){C_1|...|C_p}
 * "restr" - restriction on s2 and s
 * "eq" -  number of mutually inductive definitions should be equal to the number of predicates P_i
 * "f_p" - c:(I_k <a>) - first premise of the rule
 * "s_p" - \forall i=1...n ( P_i:(<x> : <A_i>)s2 )  - the "second premise" of the rule
 * "thrd_p" - \forall i=1...p ( f_i:C_i{I_1,...,I_n,P_1,...,P_n, Constr(i, decl)} ) the "third premise" of the rule
 *)

(* should I do <Hc['I]>; c:'C['I]; <Jc['I]> >-it ?*)
prim dep 's2 'Hi (sequent [IndParams] { <Hp> >- sequent [IndTypes] { <Hi>; I: 'A<|Hp|>; <Ji<|Hp|> > >- sequent [IndConstrs] { <Hc['I]> >-it}}}) 'Hpredicates :
	[restr]  sequent { <H>; <Hp> >- good_dep{'A<|Hp|>; 's2<||>} } -->
	[eq] 		sequent { <H>; <Hp> >- equal_length{Aux{|<Hpredicates<|H|> > >- it|}; Aux{|<Hi> >- it|}} } -->
	[f_p]		sequent { <H> >-
					'const in applH{|<Hargs> >-
						IndParams{|<Hp<||> > >-
						IndTypes{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-
						IndConstrs{|<Hc<|Hp;Hi;Ji|>['I]> >- 'I |}|}|}|} } -->
	[s_p]		sequent { <H> >-
					ForAll1T{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >-
						bind{P.('P in prodApp{| <Hp<||> > >-
							prodAppShape{x.('x -> 's2<||>);
								IndParams{|<Hp<||> > >-
								IndTypes{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-
								IndConstrs{|<Hc<|Hp;Hi;Ji|>['I]> >- 'I |}|}|}
							}
						|})} |} } -->
	[thrd_p]	sequent { <H> >-
					ForAll1TConstr{
						Terms{|<F> >-it|};
						IndParams{|<Hp<||> > >- IndTypes{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >- IndConstrs{|<Hc<|Hp;Hi;Ji|>['I]> >- it|}|}|};
						f,c,C.('f in ElimCaseTypeDep{
											'C;
											ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|};
											'c})
					}
				} -->
   sequent { <H> >-
		Elim{'const; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}; ElimCases{|<F<|H|> > >- it|}}
		in applH{|<Hargs<|H|> >; 'const >- 'P<|H|> |}
	} = it


(* In Coq there is a restriction that (s, s2) are sorts (Set,Set) or (Set,Prop),
 * where A = (<x> : <A>)s, meaning that A is an arity of sort s (X_i : A)
 *)
prim good_dep_set_set {| intro [] |} :
	sequent { <H> >- good_dep{Set; Set} } = it

prim good_dep_set_prop {| intro [] |} :
	sequent { <H> >- good_dep{Set; Prop} } = it
