extends Cic_ind_type
open Dtactic

declare case{'t;'P;'F}
declare cases
declare brackets{'I;'B}
declare brackets{'I;'A;'B}

declare branchCases
declare branchConstrs

declare emptyDef{'I}
declare singletonDef{'I}


prim bracketsProd {| intro [] |} :
	sequent { <H>; x:'C >- brackets{'I 'x; 'A['x]; 'B['x]} } -->
	sequent { <H> >- brackets{'I;(x:'C -> 'A['x]); (x:'C -> 'B['x])} } = it

prim bracketsSetProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Prop} } = it

prim bracketsSetSet {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Set} } = it

prim bracketsSetType {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> "type"[i:l]} } = it

prim bracketsTypeProp {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Prop} } = it

prim bracketsTypeSet {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Set} } = it

prim bracketsTypeType {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> "type"[i:l]} } = it

prim bracketsProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Prop;'I -> Prop} } = it


prim emptyDefSimple :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { I: 'A >-
	         sequent [IndConstrsWF] { >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { I: 'A >-
	         sequent [IndConstrsSubst] { >- emptyDef{'I} } } } } = it

(*
prim emptyDefMutual :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { <Hi>; I: 'A; <Ji> >-
	         sequent [IndConstrsWF] { <Hc['I]> >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { <Hi>; I: 'A; <Ji> >-
	         sequent [IndConstrsSubst] { <Hc['I]> >- emptyDef{'I} } } } } = it
*)

(*
declare branchConstrsAux
declare branchCasesAux

prim branchStep1 'Hi :
	sequent { <H> >-
		sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >-
			type_of_constructor{'C['I];'I} } } -->
   sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					sequent [branchConstrsAux] { c:'C['I]; <Jc['I]> >-
						sequent [branchCases] { <F> >-
							sequent [branchCasesAux] { 'f; <G> >- 'P} } } } } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]>; c:'C['I] >-
					sequent [branchConstrsAux] { <Jc['I]> >-
						sequent [branchCases] { <F>; 'f >-
							sequent [branchCasesAux] { <G> >- 'P} } } } } } } } } = it

prim branchStep2 'Hi :
	sequent { <H> >-
		sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >-
			type_of_constructor{'C['I];'I} } } -->
   sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					sequent [branchConstrsAux] { c:'C['I]; <Jc['I]> >-
						sequent [branchCases] { <F> >-
							sequent [branchCasesAux] { 'f; <G> >- 'P} } } } } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]>; c:'C['I] >-
					sequent [branchConstrsAux] { <Jc['I]> >-
						sequent [branchCases] { <F>; 'f >-
							sequent [branchCasesAux] { <G> >- 'P} } } } } } } } } = it

*)

declare branchType
declare branchType{'P;'c;'C}

prim_rw branchTypeApp :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; sequent[applH] { <Hp>;<T<| |> > >- 'I} } } <-->
	sequent [applH] { <T>; 'c >- 'P }

prim_rw branchTypeFun :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; (x:'T<||> -> 'C['x]) } } <-->
	(x: 'T -> sequent [branchType] { <Hp> >- branchType{'P; 'c 'x; 'C['x]}} )

(*
prim branchTypes :
	f in  sequent [branchType] { <Hp> >-
		branchType{'P; sequent[applH]{ <Hp> >- 'c}; sequent[applH]{ <Hp> >- 'C} } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]>; c: 'C['I]; <Jc['I]> >-
					sequent [branchConstrs] { <HcI>; 'C['I] >-
						sequent [branchCases] { <F>; 'f >- 'P} } } } } }
*)


(**********************************************************************
 *    typing rule for general destructor for inductive defenitions    *
 **********************************************************************)

prim indCases 'Hi 'B sequent [branchConstrs] { <HcI> >- it } :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
			sequent [IndTypesWF] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrsWF] { <Hc['I]> >- it } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					'c in sequent [applH] { <Hp>; <T> >- 'I } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					'P in 'B } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					brackets{sequent [applH] { <Hp> >- 'I }; 'B} } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					sequent [branchConstrs] { <HcI> >-
						sequent [branchCases] { <F> >- 'P} } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					case{'c;'P; sequent [cases] { <F> >- it} }
					in (sequent [applH] { <T>; 'c >- 'P }) } } } } = it


