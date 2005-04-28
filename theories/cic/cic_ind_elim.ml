extends Cic_ind_type

open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type

(*
 *	ForAll1D{ <H> >- bind{x.'pred['x]} } holds iff
 * 'pred['v] for all declarations (v: 'T) in <H>
 *)
declare sequent [ForAll1D] { Term : Term >- Term } : Term

prim forAll1D_base {| intro [] |} :
	sequent { <H> >- ForAll1D{| >- bind{x.'pred['x]} |} } = it

prim forAll1D_step {| intro [] |} :
	sequent { <H>; v: 'T >- ForAll1D{|<J['v]> >- bind{x.'pred<|H;J|>['v;'x]}|} } -->
	sequent { <H>; v: 'T; <J['v]> >- 'pred['v;'v] } -->
	sequent { <H> >- ForAll1D{|v: 'T; <J['v]> >- bind{x.'pred<|H;J|>['v;'x]}|} } = it

declare sequent [ForAll1T] { Term : Term >- Term } : Term

prim forAll1T_base :
	sequent { <H> >- ForAll1T{| >- bind{y.'pred['y]} |} } = it

prim forAll1T_step :
	sequent { <H>; v: 'T >- ForAll1T{|<J['v]> >- bind{y.'pred<|H|>['y]}|} } -->
	sequent { <H> >- 'pred['T] } -->
	sequent { <H> >- ForAll1T{|v: 'T; <J['v]> >- bind{y.'pred<|H|>['y]}|} } = it

let rec forAll1T_aux _ =
  (forAll1T_step thenLT [funT forAll1T_aux; idT]) orelseT forAll1T_base

let forAll1T = funT forAll1T_aux

(*
let rec forAll1Ttac = funT (fun p ->
	let concl = Sequent.concl p in
	let {	sequent_args = args;
			sequent_hyps = hyps;
			sequent_concl = goal} = TermMan.explode_sequent concl in
	if SeqHyp.length hyps = 0 then
		forAll1T_base
	else
		forAll1T_step thenLT [forAll1Ttac; idT]
)

let rec forAll1Ttac = (forAll1T_step thenLT [forAll1Ttac; idT]) orelseT forAll1T_base
*)

let resource intro += [
	<<ForAll1T{|<H> >- 'C|}>>, (wrap_intro forAll1T);
]

(*
 * Subst{SubstIn{<Params> >- 'Body}; SubstArgs{<Args>}} evaluates to
 * 'Bode[<Args>/<Params>], i.e. parameters are replaced with actual arguments -
 * for each (p: 'P) in <Params> 'p is replaced with _term_ from <Args> from the same position
 * as position of 'p in <Params>;
 * <Args> and <Params> have to be of the same length;
 * arguments have no (explicit) types, hence no typ-checking
 *)
declare Subst{'Body; 'Args}
declare sequent [SubstIn] { Term : Term >- Term } : Term
declare sequent [SubstArgs] { Term : Term >- Term } : Term

prim_rw subst_base {| reduce |} :
	Subst{SubstIn{| >- 'Body|}; SubstArgs{| >- it|}} <-->
	'Body

prim_rw subst_step {| reduce |} :
	Subst{SubstIn{|<Hv<||> >; v: 'T2<|Hv|> >- 'Body['v]|}; SubstArgs{|<Ha>; 'a<||> >- it|}} <-->
	Subst{SubstIn{|<Hv<||> > >- 'Body['a]|}; SubstArgs{|<Ha> >- it|}}

(*
 * Back{|<ToDrop> >- BackIn{|<J> >- it|}|} drops |ToDrop| elements from
 * the end of <J> and then returns the last element of the rest of <J>
 *)
declare sequent [Back] { Term : Term >- Term } : Term
declare sequent [BackIn] { Term : Term >- Term } : Term

prim_rw back_base {| reduce |} :
	Back{| >-BackIn{|<Prefix>; 't<||> >-it|}|} <--> 't

prim_rw back_step {| reduce |} :
	Back{|<ToDrop>; 'dummy >-BackIn{|<Prefix>; 't >- it|}|} <-->
	Back{|<ToDrop> >-BackIn{|<Prefix> >- it|}|}
(*
let fold_back_base = makeFoldC <<Back{|<H> >- BackFor{| >- BackIn{|<Prefix>; 't<||> >- it|}|}|}>> back_base
let fold_back_step = makeFoldC <<Back{|<H> >- BackFor{|<ToDrop>; 'dummy >- BackIn{|<Prefix>; 't >- it|}|}|}>> back_step
*)
(*
 * Types of cases for Nodep rule
 *)
declare sequent [ElimPredicates] { Term : Term >- Term } : Term
declare ElimCaseType{'C; 'predicates}

(* (P->C){X,Q} = P -> (P[X<-Q] ->C{X,Q}), X=I_1,..., I_n, Q=P1,...,P_n,
 * when strictly_positive(P,I_i) holds
 *)
prim_rw elimCaseType_inductive {| reduce |} :
	 ForAll1D{|<Hi> >- bind{I.strictly_pos{'I; 'P}} |} -->
	 ElimCaseType{prodH{|<Hi> >- 'P -> 'C|}; ElimPredicates{|<Predicates> >- it|}} <-->
		prodH{|<Hi> >-
			('P -> Subst{SubstIn{|<Hi> >- 'P|}; SubstArgs{|<Predicates> >- it|} } ->
			ElimCaseType{prodH{|<Hi> >- 'C|}; ElimPredicates{|<Predicates> >- it|}})
	|}

(* ((x:M)C{I_1,...,I_n,P_1,...,P_n} = (x:M)C{I_1,...,I_n,P_1,...,P_n)
 * or
 * ((x:M)C{X,Q} = (x:M)C{X,Q} )
 *)
prim_rw elimCaseType_dfun {| reduce |} :
	ElimCaseType{prodH{|<Hi> >- x:'M<||> -> 'C['x]|}; ElimPredicates{|<Predicates> >- it|}} <-->
	(x:'M -> ElimCaseType{prodH{|<Hi> >- 'C['x]|}; ElimPredicates{|<Predicates> >- it|}})

(* auxilary function
 * (C a){I_1,...,I_n,P_1,...,P_n} = (C{I_1,...,I_n,P_1,...,P_n} a)
 * or
 * (C a){X,Q}=(C{X,Q} a)
 *)
prim_rw elimCaseType_app {| reduce |} :
	ElimCaseType{prodH{|<Hi> >- 'C 'a<||> |}; ElimPredicates{|<Predicates> >- it|}} <-->
	(ElimCaseType{prodH{|<Hi> >- 'C |}; ElimPredicates{|<Predicates> >- it|}} 'a)

(* auxilary function
 * I_i{I_1,...,I_n,P_1,...,P_n} = P_{i}
 * or
 * X{X,Q}=Q
 *)
prim_rw elimCaseType_id 'Hi :
	ElimCaseType{prodH{|<Hi>; I: 'A; <Ji<||> > >- 'I |}; ElimPredicates{|<Predicates> >- it|}} <-->
	Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}

(* (I_i <a>){I_1,...,I_n,P_1,...,P_n} = (P_i <a>)
 * or
 * (X <a>){X,Q} = (Q <a>)
 *)
prim_rw elimCaseType_applH 'Hi :
	ElimCaseType{prodH{|<Hi>; I: 'A; <Ji<||> > >- applH{|<Args<||> > >- 'I|}|}; ElimPredicates{|<Predicates> >- it|}} <-->
	applH{|<Args<||> > >- Back{|<Ji> >- BackIn{|<Predicates> >- it|}|}|}

declare sequent [Terms] { Term : Term >- Term } : Term
(*
 * ForAll2T{Terms{|<T1> >-it|}; Terms{|<T2> >-it|}; t1,t2.'pred['t1;'t2]}
 *)
declare ForAll2T{'Ht1; 'Ht2; t1,t2.'pred['t1;'t2]}

prim forAll2T_base {| intro [] |} :
	sequent { <H> >- ForAll2T{Terms{| >-it|}; Terms{| >-it|}; t1,t2.'pred['t1;'t2]} } = it

prim forAll2T_step {| intro [] |} :
	sequent { <H> >- 'pred['t1; 't2] } -->
	sequent { <H> >- ForAll2T{Terms{|<T1> >-it|}; Terms{|<T2> >-it|}; t1,t2.'pred['t1;'t2]} } -->
	sequent { <H> >- ForAll2T{Terms{|<T1>; 't1<|H|> >-it|}; Terms{|<T2>; 't2<|H|> >-it|}; t1,t2.'pred['t1;'t2]} } = it

(*
 * ForAll1T1DT{Terms{|<T1> >-it|}; prodH{|<H> >- Terms{|<T2> >-it|}|}; t1,t2.'pred['t1;'t2]}
 *)
declare ForAll1T1DT{'Ht1; 'Ht2; t1,v,t2.'pred['t1;'v;'t2]}

prim forAll1T1DT_base {| intro [] |} :
	sequent { <H> >- ForAll1T1DT{Terms{| >-it|}; prodH{|<J> >-Terms{| >-it|}|}; t1,v,t2.'pred['t1;'v;'t2]} } = it

prim forAll1T1DT_step {| intro [] |} :
	sequent { <H> >- 'pred['t1; prodH{|<J>; v: 't2 >- 'v |}; prodH{|<J> >-'t2 |}] } -->
	sequent { <H> >- ForAll1T1DT{Terms{|<T1> >-it|}; prodH{|<J> >-Terms{|<T2> >-it|}|}; t1,v,t2.'pred['t1;'v;'t2]} } -->
	sequent { <H> >-
		ForAll1T1DT{Terms{|<T1>; 't1<|H|> >-it|}; prodH{|<J> >-Terms{|<T2>; 't2<|H;J|> >-it|}|}; t1,v,t2.'pred['t1;'v;'t2]} } = it

declare equal_length{'context1; 'context2}

prim equal_length_base {| intro [] |} :
	sequent { <H> >- equal_length{Aux{| >- it|}; Aux{| >- it|}} } = it

prim equal_length_step {| intro [] |} :
	sequent { <H> >- equal_length{Aux{|<H1> >- it|}; Aux{|<H2> >- it|}} } -->
	sequent { <H> >- equal_length{Aux{|<H1>; x: 'T >- it|}; Aux{|<H2>; y: 'S >- it|}} } = it

declare Elim{'c; 'predicates; 'cases}
declare sequent [ElimCases] { Term : Term >- Term } : Term
declare good_nodep{'sort1; 'sort2}


(* the typing rule for non-dependent elimination for mutually inductive definitions
 * given Ind(X_1:A1, ..., X_n:A_n){C_1|...|C_p}
 * "restr" - restriction on s2 and s
 * "eq" -  number of mutually inductive definitions should be equal to the number of predicates P_i
 * "f_p" - c:(I_k <a>) - first premise of the rule
 * "s_p" - \forall i=1...n ( P_i:(<x> : <A_i>)s2 )  - the "second premise" of the rule
 * "thrd_p" - \forall i=1...p ( f_i:C_i{I_1,...,I_n,P_1,...,P_n} ) the "third premise" of the rule
 *)

prim nodep 's2 'Hi (sequent [IndParams] { <Hp> >- sequent [IndTypes] { <Hi>; I: 'A<|Hp|>; <Ji<|Hp|> > >- sequent [IndConstrs] { <Hc['I]> >-it}}}) 'Hpredicates :
	[restr]  sequent { <H>;<Hp> >- good_nodep{'A<|Hp|>; 's2<||>} } -->
	[eq]     sequent { <H>;<Hp> >- equal_length{Aux{|<Hpredicates<|H|> > >- it|}; Aux{|<Hi> >- it|}} } -->
	[f_p]    sequent { <H> >-
					'c in applH{|<Hargs> >-
						IndParams{|<Hp<||> > >-
						IndTypes{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-
						IndConstrs{|<Hc<|Hp;Hi;Ji|>['I]> >- 'I |}|}|}|} } -->
	[s_p]		sequent { <H> >-
					ForAll1T{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- bind{P.('P in prodH{| <Hp<||> > >- 's2<||> |})} |} } -->
	[thrd_p]	sequent { <H>;<Hp<||> > >-
					ForAll1T1DT{
						Terms{|<F<|H|> > >-it|};
						prodH{|<Hi<|Hp|> >; I: 'A<|Hp|>; <Ji<|Hp|> > >-Terms{|<Hc<|Hp;Hi;Ji|>['I]> >-it|}|};
				f,v,C.('f in ElimCaseType{'C; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}})
					}
				} -->
   sequent { <H> >-
		Elim{'c; ElimPredicates{|<Hpredicates<|H|> >; 'P<|H|>; <Jpredicates<|H|> > >- it|}; ElimCases{|<F<|H|> > >- it|}}
		in applH{|<Hargs<|H|> > >- 'P<|H|> |}
	} = it

(*
prim nodep 's2 'Hi (sequent [IndParams] { <Hp> >- sequent [IndTypes] { <Hi>; I: 'A<|Hp|>; <Ji<|Hp|> > >- sequent [IndConstrs] { <Hc['I]> >-it}}}) :
   sequent { <H>;<Hp> >- good_nodep{'A<|Hp|>; 's2<||>} } -->
	sequent { <H> >- 'c in applH{|<Hargs> >- IndParams{|<Hp> >- IndTypes{|<Hi>; I: 'A<|Hp|>; <Ji<|Hp|> > >- IndConstrs{|<Hc['I]> >- 'I |}|}|}|} } -->
   sequent { <H> >- ForAll1T{|<Predicates> >- bind{P.('P in prodH{| <Hp<||> > >- 's2<||> |})} |} } -->
	sequent { <H>;<Hp>;<Hi>;I: 'A<|Hp|>;<Ji> >-
		ForAll2T{Terms{|<F> >-it|}; Terms{|<Hc['I]> >-it|};
			f,C.('f in
				ElimCaseType{
					ElimCaseType{|<Hi> >- 'C |};
					ElimPredicates{|<Predicates> >- it|}
				}
			)
		}
	} -->
   sequent { <H> >-
		Elim{'c; ElimPredicates{|<Predicates<|H|> > >- it|}; ElimCases{|<F> >- it|}}
		in applH{|<Hargs<|H|> > >- Back{|<Hp<||> > >- BackFor{|<Ji<|Hp|> > >- BackIn{|<Predicates<|H|> > >- it|}|}|} |}
	} = it
*)

(* In Coq there is a restriction that s2, s are sorts Prop, where
 * A = (<x> : <A>)s, meaning that A is an arity of sort s (X_i : A)
 *)
prim good_nodep_prop_prop {| intro [] |} :
	sequent { <H> >- good_nodep{Prop; Prop} } = it

(*
declare case_type{'C; 'Q; 'c}
declare ind_type{I.'T['I]}

prim_rw
   ind_type{X.strictly_pos{'X; 'P['X]}} -->
   ind_type{X.case_type{'P['X] -> 'C['X]; 'Q; 'c} <-->
   ind_type{X.(p: 'P['X] -> 'P['Q] -> case_typ{'C['X]; 'Q})}

prim_rw
   ind_type{X.case_type{x:'M -> 'C['X;'x]; 'Q; 'c}} <-->
   ind_type{X. x: 'M -> case_type{'C['X;'x]; 'Q; ('c 'x)}}

prim_rw
   ind_type{X.case_type{applH{ <Hargs['X]> >- 'X}; 'Q; 'c}} <-->
   ind_type{X.(applH{ <Hargs['X]> >- 'Q} 'c)}

prim dep 's
   <H> >- good{'s} -->
   <H> >- 'c in applH{ <Hargs> >- 'I } -->
   <H> >- 'Q in prodH{ <Hp> >- 's } -->
   <H> >- ForAllCases{ <Hc> >- <F> >- it } -->
   <H> >- Elim{'c; 'Q; ElimCases{<F> >- it}} in applH{ <Hargs> >- 'Q }} = it
*)