extends Cic_ind_type
extends Cic_ind_elim

open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type
open Cic_ind_elim

declare ForAll1TConstr{'terms; 'IndDef; t,c,C.'P['t;'c;'C]}
declare ForAll1TConstrAux{'terms; 'IndDef; t,c,C.'P['t;'c;'C]}

rule forAll1TConstr_base  :
	sequent { <H> >- ForAll1TConstrAux{Terms{| 't; <T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc> >- IndConstrs{| >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} }

rule forAll1TConstr_step  :
	sequent { <H> >- IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc>; c:'C; <Jc> >- 'P['t; 'c; 'C]|}|}|} } -->
	sequent { <H> >- ForAll1TConstrAux{Terms{|<T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc>; c:'C >- IndConstrs{|<Jc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } -->
	sequent { <H> >- ForAll1TConstrAux{Terms{| 't; <T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{|<Hc> >- IndConstrs{|c:'C; <Jc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} }

rule forAll1TConstr_start  :
	sequent { <H> >- ForAll1TConstrAux{Terms{|<T> >-it|};
		IndParams{|<Hp> >- IndTypes{|<Hi> >- Aux{| >- IndConstrs{|<Hc> >- it|}|}|}|}; t,c,C.'P['t;'c;'C]} } -->
	sequent { <H> >-
		ForAll1TConstr{Terms{|<T> >-it|}; IndParams{|<Hp> >- IndTypes{|<Hi> >- IndConstrs{|<Hc> >- it|}|}|}; t,c,C.'P['t;'c;'C]} }

(******************************************************************************************
 * Definition of application for left parts of declarations                               *
 ******************************************************************************************
 *)

declare prodAppShape{x.'T['x]; 't}
declare sequent [prodApp] { Term : Term >- Term } : Term

rewrite prodApp_base :
	prodApp{| >- prodAppShape{y.'S['y]; 't} |} <-->
	'S['t]

rewrite prodApp_step :
	prodApp{| <H>; x: 'T >- prodAppShape{y.'S['x;'y]; 't} |} <-->
	prodApp{| <H> >- prodAppShape{y.(x: 'T -> 'S['x; 'y 'x]); 't} |}
(*
let fold_prodApp_base = makeFoldC <<prodApp{| >- prodAppShape{y.'S['y]; 't} |}>> prodApp_base
let fold_prodApp_step = makeFoldC <<prodApp{| <H>; x: 'T >- prodAppShape{y.'S['x;'y]; 't} |}>> prodApp_step
let fold_prodAppC = fold_prodApp_base thenC (repeatC fold_prodApp_step)
*)
topval prodAppC : conv


(******************************************************************************************
 * definition of ElimCaseTypeDef                                                          *
 ******************************************************************************************
 *)

declare ElimCaseTypeDep{'C; 'predicates; 'c}

(* (P->C){X,Q} = P -> (P[X<-Q] ->C{X,Q}), X=I_1,..., I_n, Q=P1,...,P_n,
 * when strictly_positive(P,I_i) holds
 *)
rewrite elimCaseTypeDep_inductive 'Hi :
	ForAll1D{|<Hi> >- bind{I.strictly_pos{'I; prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |}}} |} -->
	ElimCaseTypeDep{
		prodH{|<Hi>; I:'A; <Ji> >- prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |} -> 'C|};
		ElimPredicates{|<Predicates> >- it|};'c
	} <-->
	prodH{| <Hi>; I:'A; <Ji> >-
		p:prodH{| <P> >- applH{| <M> >- 'I |} |} ->
			(prodApp{| <P> >-
				prodAppShape{
					x.(applH{| <M> >-
						Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}|} 'x);
					'p
				} |}
			 ->
			 ElimCaseTypeDep{prodH{|<Hi>; I:'A; <Ji> >- 'C|}; ElimPredicates{|<Predicates> >- it|}; 'c 'p}
			)
	|}

(* ((x:M)C{I_1,...,I_n,P_1,...,P_n,c} = (x:M)C{I_1,...,I_n,P_1,...,P_n,c x)
 * or
 * ((x:M)C{X,Q,c} = (x:M)C{X,Q,(c x)} )
 *)
rewrite elimCaseTypeDep_dfun  :
	ElimCaseTypeDep{prodH{|<Hi> >- x:'M<||> -> 'C['x]|}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	(x:'M -> ElimCaseTypeDep{prodH{|<Hi> >- 'C['x]|}; ElimPredicates{|<Predicates> >- it|}; 'c 'x})

(* auxilary function
 * (C a){I_1,...,I_n,P_1,...,P_n,c} = (C{I_1,...,I_n,P_1,...,P_n,c} a)
 * or
 * (C a){X,Q,c}=(C{X,Q,c} a)
 *)
rewrite elimCaseTypeDep_app  :
	ElimCaseTypeDep{prodH{|<Hi> >- 'C 'a<||> |}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	(ElimCaseTypeDep{prodH{|<Hi> >- 'C |}; ElimPredicates{|<Predicates> >- it|}; 'c} 'a)

(* auxilary function
 * I_i{I_1,...,I_n,P_1,...,P_n,c} = P_{i}
 * or
 * X{X,Q,c}=Q
 *)
rewrite elimCaseTypeDep_id 'Hi :
	ElimCaseTypeDep{prodH{|<Hi>; I: 'A; <Ji<||> > >- 'I |}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}

(* (I_i <a>){I_1,...,I_n,P_1,...,P_n,c} = ((P_i <a>) c)
 * or
 * (X <a>){X,Q,c} = ((Q <a>) c)
 *)
rewrite elimCaseTypeDep_applH 'Hi :
	ElimCaseTypeDep{prodH{|<Hi>; I: 'A; <Ji<||> > >- applH{|<Args<||> > >- 'I|}|}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	(applH{|<Args<||> > >- Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}|} 'c)

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
rule dep 's2 'Hi (sequent [IndParams] { <Hp> >- sequent [IndTypes] { <Hi>; I: 'A<|Hp|>; <Ji<|Hp|> > >- sequent [IndConstrs] { <Hc['I]> >-it}}}) 'Hpredicates :
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
						f,c,C.('f in ElimCaseTypeDep{'C; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}; 'c})
					}
				} -->
   sequent { <H> >-
		Elim{'const; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}; ElimCases{|<F<|H|> > >- it|}}
		in applH{|<Hargs<|H|> >; 'const >- 'P<|H|> |}
	}


(* In Coq there is a restriction that (s, s2) are sorts (Set,Set) or (Set,Prop),
 * where A = (<x> : <A>)s, meaning that A is an arity of sort s (X_i : A)
 *)
rule good_dep_set_set  :
	sequent { <H> >- good_dep{Set; Set} }

rule good_dep_set_prop  :
	sequent { <H> >- good_dep{Set; Prop} }
