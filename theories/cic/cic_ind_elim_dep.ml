extends Cic_ind_type
extends Cic_ind_elim

open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type
open Cic_ind_elim

(******************************************************************************************
 * Definition of application for left parts of declarations                               *
 ******************************************************************************************
 *)

 declare sequent [applHLeft] { Term : Term >- Term } : Term
(*
dform applHLeft_df : except_mode[src] :: sequent [applHLeft] { <H> >- 'e } =
	display_concl{sequent { <H> >- 'e }} display_hyps_emph{sequent { <H> >- 'e }}
*)

(*inductive definition of multiple application *)
prim_rw applHLeftBase {| reduce |} :
   applHLeft{| >- 'S |} <-->
	'S

(* x:'T should be removed from the second sequent*)
prim_rw applHLeftStep {| reduce |} :
   applHLeft{| x:'T; <H> >- 'S |} <-->
	applHLeft{| x:'T; <H> >- apply{'S;'x} |}

let fold_applHLeftBase = makeFoldC <<applHLeft{| >- 'S |}>> applHLeftBase
let fold_applHLeftStep = makeFoldC <<applHLeft{| x:'T; <H> >- 'S |}>> applHLeftStep
let fold_applHLeft = fold_applHLeftBase thenC (repeatC fold_applHLeftStep)

let applHCLeft = (repeatC applHLeftStep) thenC applHLeftBase


(******************************************************************************************
 * definition of ElimCaseTypeDef                                                          *
 ******************************************************************************************
 *)

declare ElimCaseTypeDep{'C; 'predicates; 'c}

(* (P->C){X,Q} = P -> (P[X<-Q] ->C{X,Q}), X=I_1,..., I_n, Q=P1,...,P_n,
 * when strictly_positive(P,I_i) holds
 *)
prim_rw elimCaseTypeDep_inductive 'Hi :
	ForAll1D{|<Hi> >- bind{I.strictly_pos{'I; prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |}}} |} -->
	ElimCaseTypeDep{prodH{|<Hi>; I:'A; <Ji> >- (prodH{|<P<||> > >- applH{| <M<|P|> > >- 'I |} |}) -> 'C|}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	prodH{| <Hi>; I:'A; <Ji> >-
		(p:prodH{| <P> >- applH{| <M> >- 'I |} |} ->
			(prodH{| <P> >- (applH{| <M> >- 'I |}) (applHLeft{| <P> >- 'p |})|} ->
				ElimCaseTypeDep{prodH{|<Hi>; I:'A; <Ji> >- 'C|}; ElimPredicates{|<Predicates> >- it|}; 'c 'p}
			)
		)
	|}

(* ((x:M)C{I_1,...,I_n,P_1,...,P_n,c} = (x:M)C{I_1,...,I_n,P_1,...,P_n,c x)
 * or
 * ((x:M)C{X,Q,c} = (x:M)C{X,Q,(c x)} )
 *)
prim_rw elimCaseTypeDep_dfun {| reduce |} :
	ElimCaseTypeDep{prodH{|<Hi> >- x:'M<||> -> 'C['x]|}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	(x:'M -> ElimCaseTypeDep{prodH{|<Hi> >- 'C['x]|}; ElimPredicates{|<Predicates> >- it|}; 'c 'x})

(* auxilary function
 * (C a){I_1,...,I_n,P_1,...,P_n,c} = (C{I_1,...,I_n,P_1,...,P_n,c} a)
 * or
 * (C a){X,Q,c}=(C{X,Q,c} a)
 *)
prim_rw elimCaseTypeDep_app {| reduce |} :
	ElimCaseTypeDep{prodH{|<Hi> >- 'C 'a<||> |}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	(ElimCaseTypeDep{prodH{|<Hi> >- 'C |}; ElimPredicates{|<Predicates> >- it|}; 'c} 'a)

(* auxilary function
 * I_i{I_1,...,I_n,P_1,...,P_n,c} = P_{i}
 * or
 * X{X,Q,c}=Q
 *)
prim_rw elimCaseTypeDep_id 'Hi :
	ElimCaseTypeDep{prodH{|<Hi>; I: 'A; <Ji<||> > >- 'I |}; ElimPredicates{|<Predicates> >- it|};'c} <-->
	Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}

(* (I_i <a>){I_1,...,I_n,P_1,...,P_n,c} = ((P_i <a>) c)
 * or
 * (X <a>){X,Q,c} = ((Q <a>) c)
 *)
prim_rw elimCaseTypeDep_applH 'Hi :
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
						bind{P.('P in prodH{| <Hp<||> > >-
							(applHLeft{|<Hp<||> > >-
								IndParams{|<Hp<||> > >-
								IndTypes{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-
								IndConstrs{|<Hc<|Hp;Hi;Ji|>['I]> >- 'I |}|}|}|} -> 's2<||>) |})} |} } -->
	[thrd_p]	sequent { <H>; <Hp<||> > >-
					ForAll1T1DT{
						Terms{|<F<|H|> > >-it|};
						prodH{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-Terms{|<Hc<|Hp;Hi;Ji|>['I]> >-it|}|};
						f,c,C.('f in ElimCaseTypeDep{'C; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}; 'c})
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
